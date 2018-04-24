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
use super::field::FieldElem;

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

        let mut a = curve.get_a();
        let mut b = curve.get_b();

        prepend.append(&mut a);
        prepend.append(&mut b);

        let (x_g, y_g) = curve.to_affine(&curve.generator());
        let (mut x_g, mut y_g) = (x_g.to_bytes(), y_g.to_bytes());
        prepend.append(&mut x_g);
        prepend.append(&mut y_g);

        let (x_a, y_a) = curve.to_affine(pk);
        let (mut x_a, mut y_a) = (x_a.to_bytes(), y_a.to_bytes());
        prepend.append(&mut x_a);
        prepend.append(&mut y_a);


        let mut hasher = Sm3Hash::new(&prepend[..]);
        let z_a = hasher.get_hash();

        // Z_A = HASH_256(ID_LEN || ID || x_G || y_G || x_A || y_A)

        // e = HASH_256(Z_A || M)

        let mut prepended_msg: Vec<u8> = Vec::new();
        prepended_msg.extend_from_slice(&z_a[..]);
        prepended_msg.extend_from_slice(&msg[..]);

        let mut hasher = Sm3Hash::new(&prepended_msg[..]);
        hasher.get_hash()
    }

    pub fn sign(&self, msg: &[u8], sk: &BigUint, pk: &Point) -> Signature
    {
        // Get the value "e", which is the hash of message and ID, EC parameters and public key
        let digest = self.hash("1234567812345678", pk, msg);

        self.sign_raw(&digest[..], sk)
    }

    pub fn sign_raw(&self, digest: &[u8], sk: &BigUint) -> Signature
    {
        let curve = &self.curve;
        // Get the value "e", which is the hash of message and ID, EC parameters and public key

        let e = BigUint::from_bytes_be(digest);

        // two while loops
        loop {
            // k = rand()
            // (x_1, y_1) = g^kg
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
        //Get hash value
        let digest = self.hash("1234567812345678", pk, msg);
        println!("digest: {:?}", digest);
        self.verify_raw(&digest[..], pk, sig)

    }

    pub fn verify_raw(&self, digest: &[u8], pk: &Point, sig: &Signature) -> bool
    {
        if digest.len() != 32{
            panic!("the length of digest must be 32-bytes.");
        }
        let e = BigUint::from_bytes_be(digest);

        let curve = &self.curve;
        // check r and s
        if sig.r == BigUint::zero() || sig.s == BigUint::zero() {
            return false;
        }
        if sig.r >= curve.get_n() || sig.s >= curve.get_n() {
            return false;
        }

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

    pub fn load_pubkey(&self, buf: &[u8]) -> Result<Point, bool>
    {
        self.curve.bytes_to_point(buf)
    }

    pub fn serialize_pubkey(&self, p: &Point, compress: bool) -> Vec<u8>
    {
        self.curve.point_to_bytes(p, compress)
    }

    pub fn load_seckey(&self, buf: &[u8]) -> Result<BigUint, bool>
    {
        if buf.len() != 32 {
            return Err(true);
        }
        let sk = BigUint::from_bytes_be(buf);
        if sk > self.curve.n {
            return Err(true);
        }
        return Ok(sk);
    }

    pub fn serialize_seckey(&self, x: &BigUint) -> Vec<u8>
    {
        if *x > self.curve.n {
            panic!("invalid secret key");
        }
        let x = FieldElem::from_biguint(x);
        x.to_bytes()
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

        let signature = ctx.sign(msg, &sk, &pk);
        let der = signature.der_encode();
        let sig = Signature::der_decode_raw(&der[2..]).unwrap();
        assert!(ctx.verify(msg, &pk, &sig));
    }

    #[test]
    fn test_key_serialization()
    {
        let ctx = SigCtx::new();
        let (pk, sk) = ctx.new_keypair();

        let pk_v = ctx.serialize_pubkey(&pk, true);
        let new_pk = ctx.load_pubkey(&pk_v[..]).unwrap();
        assert!(ctx.curve.eq(&new_pk, &pk));

        let sk_v = ctx.serialize_seckey(&sk);
        let new_sk = ctx.load_seckey(&sk_v[..]).unwrap();
        assert_eq!(new_sk, sk);
    }

    #[test]
    fn test_gmssl()
    {
        let msg = "abc";

        let pk: &[u8] = &[4, 74, 96, 47, 163, 99, 77, 222, 236, 237, 71, 125, 218, 161, 229, 246, 228, 192, 42,
            104, 234, 126, 248, 66, 213, 229, 197, 240, 217, 189, 63, 129, 200, 87, 182, 18, 147, 247, 228,
            50, 153, 131, 195, 134, 229, 170, 169, 156, 40, 17, 181, 174, 114, 75, 207, 124, 34, 167, 115,
            107, 237, 208, 148, 190, 57];

        let sig: &[u8] = &[48, 69, 2, 33, 0, 193, 39, 212, 158, 175, 81, 172, 84, 159, 245, 23, 3,
            123, 144, 111, 58, 145, 67, 200, 250, 113, 127, 180, 235, 124, 112, 120, 143, 164, 8,
            114, 105, 2, 32, 79, 208, 246, 149, 207, 210, 75, 65, 215, 190, 236, 148, 228, 128,
            200, 146, 183, 52, 17, 129, 44, 36, 151, 15, 157, 56, 130, 1, 151, 27, 141, 34];


        let ctx = SigCtx::new();
        let pk = ctx.load_pubkey(pk).unwrap();

        let sig = Signature::der_decode(sig).unwrap();
        assert!(ctx.verify(&msg.as_bytes(), &pk, &sig));
    }
}