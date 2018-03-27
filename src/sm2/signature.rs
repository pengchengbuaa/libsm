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

struct Signature {
    r: BigUint,
    s: BigUint,
}

impl Signature {
    pub fn parse() // -> Signature
    {}

    pub fn der_encode(&self) // -> Vec<u8>
    {
        let ret: Vec<u8> = Vec::new();

        let vr = self.r.to_bytes_be();
        let vs = self.s.to_bytes_be();
    }
}

struct SigCtx {
    curve: EccCtx,
}

impl SigCtx {
    pub fn new() -> SigCtx
    {
        SigCtx {
            curve: EccCtx::new(),
        }
    }

    pub fn sign(&self, msg: &[u8], sk: &BigUint) // -> Signature
    {}

    pub fn verify(&self, msg: &[u8], pk: &Point, sig: &Signature) // -> bool
    {}

    pub fn new_keypair() // -> (Point, BigUint)
    {}
}

#[cfg(test)]
mod tests {}