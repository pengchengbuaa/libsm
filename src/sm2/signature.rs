// Copyright (C) 2018
//
// This file is part of libsm.
//
// libsm is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// libsm is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with libsm.  If not, see <http://www.gnu.org/licenses/>.

use num_bigint::BigUint;
use super::ecc::*;
use sm3::hash::Sm3Hash;
use num_traits::*;

use yasna;

use byteorder::{BigEndian, WriteBytesExt};

pub struct Signature {
    r: BigUint,
    s: BigUint,
}

impl Signature {
    pub fn der_decode(buf: &[u8]) -> Result<Signature, yasna::ASN1Error>
    {
        let (r, s) = yasna::parse_der(buf, |reader| {
            reader.read_sequence(|reader| {
                let r = reader.next().read_biguint()?;
                let s = reader.next().read_biguint()?;
                return Ok((r, s));
            })
        })?;
        Ok(Signature {
            r,
            s,
        })
    }

    pub fn der_decode_raw(buf: &[u8]) -> Result<Signature, bool>
    {
        if buf[0] != 0x02 {
            return Err(true);
        }
        let r_len: usize = buf[1] as usize;
        if buf.len() <= r_len + 4 {
            return Err(true);
        }
        let r = BigUint::from_bytes_be(&buf[2..2 + r_len]);

        let buf = &buf[2 + r_len..];
        if buf[0] != 0x02 {
            return Err(true);
        }
        let s_len: usize = buf[1] as usize;
        if buf.len() < s_len + 2 {
            return Err(true);
        }
        let s = BigUint::from_bytes_be(&buf[2..2 + s_len]);

        return Ok(Signature {
            r,
            s,
        })
    }

    pub fn der_encode(&self) -> Vec<u8>
    {
        let der = yasna::construct_der(|writer| {
            writer.write_sequence(|writer| {
                writer.next().write_biguint(&self.r);
                writer.next().write_biguint(&self.s);
            })
        });
        return der;
    }
}

pub struct SigCtx {
    curve: EccCtx,
}

impl SigCtx {
    pub fn new() -> SigCtx
    {
        SigCtx {
            curve: EccCtx::new(),
        }
    }

    pub fn hash(&self, id: &str, pk: &Point, msg: &[u8]) -> [u8; 32]
    {
        let curve = &self.curve;

        let mut prepend: Vec<u8> = Vec::new();
        if id.len() > 65535 {
            panic!("ID is too long.");
        }
        prepend.write_u16::<BigEndian>(id.len() as u16).unwrap();
        for c in id.bytes() { prepend.push(c); }

        let a = curve.get_a();
        let b = curve.get_b();
        prepend.extend_from_slice(&a[..]);
        prepend.extend_from_slice(&b[..]);

        let (x_g, y_g) = curve.to_affine(&curve.generator());
        let (x_g, y_g) = (x_g.to_bytes(), y_g.to_bytes());
        prepend.extend_from_slice(&x_g[..]);
        prepend.extend_from_slice(&y_g[..]);

        let (x_a, y_a) = curve.to_affine(pk);
        let (x_a, y_a) = (x_a.to_bytes(), y_a.to_bytes());
        prepend.extend_from_slice(&x_a[..]);
        prepend.extend_from_slice(&y_a[..]);

        let mut hasher = Sm3Hash::new(&prepend[..]);
        let z_a = hasher.get_hash();

        // Z_A = HASH_256(ID_LEN || ID || x_G || y_G || x_A || y_A)

        // e = HASH_256(Z_A || M)

        let mut prepended_msg: Vec<u8> = Vec::new();
        prepended_msg.extend_from_slice(&z_a[..]);
        prepended_msg.extend_from_slice(msg);

        let mut hasher = Sm3Hash::new(&prepended_msg[..]);
        hasher.get_hash()
    }

    pub fn sign(&self, msg: &[u8], sk: &BigUint, pk: &Point) -> Signature
    {
        let curve = &self.curve;
        // Get the value "e", which is the hash of message and ID, EC parameters and public key
        let e = self.hash("1234567812345678", pk, msg);
        let e = BigUint::from_bytes_be(&e[..]);

        // two while loops
        loop {
            // k = rand()
            // (x_1, y_1) = g^k
            let k = self.curve.random_uint();
            let p_1 = curve.mul(&k, &curve.generator());
            let (x_1, _) = curve.to_affine(&p_1);
            let x_1 = x_1.to_biguint();

            // r = e + x_1
            let r = (e.clone() + x_1) % curve.get_n();
            if r == BigUint::zero() || r.clone() + k.clone() == curve.get_n() {
                continue;
            }

            // s = (1 + sk)^-1 * (k - r * sk)
            let s1 = curve.inv_n(&(sk.clone() + BigUint::one()));

            let mut s2_1 = r.clone() * sk.clone();
            if s2_1 < k { s2_1 = s2_1 + curve.get_n(); }
            let mut s2 = s2_1 - k;
            s2 = s2 % curve.get_n();
            let s2 = curve.get_n() - s2;

            let s = (s1 * s2) % curve.get_n();

            if s != BigUint::zero() {
                // Output the signature (r, s)
                return Signature { r, s };
            }
            panic!("cannot sign")
        }
    }

    pub fn verify(&self, msg: &[u8], pk: &Point, sig: &Signature) -> bool
    {
        let curve = &self.curve;
        // check r and s
        if sig.r == BigUint::zero() || sig.s == BigUint::zero() {
            return false;
        }
        if sig.r >= curve.get_n() || sig.s >= curve.get_n() {
            return false;
        }

        //Get hash value
        let e = self.hash("1234567812345678", pk, msg);
        let e = BigUint::from_bytes_be(&e[..]);

        // calculate R
        let t = (sig.s.clone() + sig.r.clone()) % curve.get_n();
        if t == BigUint::zero() {
            return false;
        }

        let p_1 = curve.add(
            &curve.mul(&sig.s, &curve.generator()),
            &curve.mul(&t, pk),
        );
        let (x_1, _) = curve.to_affine(&p_1);
        let x_1 = x_1.to_biguint();

        let r_ = (e + x_1) % curve.get_n();

        // check R == r?
        if r_ == sig.r {
            return true;
        }

        return false;
    }

    pub fn new_keypair(&self) -> (Point, BigUint)
    {
        let curve = &self.curve;
        let mut sk: BigUint = curve.random_uint();
        let mut pk: Point = curve.mul(&sk, &curve.generator());

        loop {
            if !pk.is_zero() {
                break;
            }
            sk = curve.random_uint();
            pk = curve.mul(&sk, &curve.generator());
        }


        return (pk, sk);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sign_and_verify()
    {
        let string = String::from("abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd");
        let msg = string.as_bytes();

        let ctx = SigCtx::new();
        let (pk, sk) = ctx.new_keypair();

        let signature = ctx.sign(msg, &sk, &pk);
        assert!(ctx.verify(msg, &pk, &signature));
    }

    #[test]
    fn test_sig_encode_and_decode()
    {
        let string = String::from("abcdabcdabcdabcdabcdabcdabcdabcdabcdabcdabcd");
        let msg = string.as_bytes();

        let ctx = SigCtx::new();
        let (pk, sk) = ctx.new_keypair();

        let signature = ctx.sign(msg, &sk, &pk);
        let der = signature.der_encode();
        let sig = Signature::der_decode(&der[..]).unwrap();
        assert!(ctx.verify(msg, &pk, &sig));
    }
}