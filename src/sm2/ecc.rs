use super::field::*;
use num_bigint::BigUint;

pub struct EccCtx {}

pub struct Point {}

impl EccCtx {
    pub fn add(&self, a: &Point, b: &Point) {}

    pub fn double(&self, a: &Point) {
        self.add(a, a);
    }

    pub fn scalar_mul(&self, a: &Point, b: &BigUint) {}
}

impl Point {
    pub fn new(x: &FieldElem, y: &FieldElem) {}

    pub fn to_tuple(&self) {}

    pub fn eq(&self, x: &Point) {}

    pub fn der_encode(&self) {}

    pub fn parse_der(x: &[u8]) {}
}