use super::field::*;
use num_bigint::BigUint;

pub struct EccCtx {
    fctx: FieldCtx,
    a: FieldElem,
    b: FieldElem,
}

pub struct Point {
    x: FieldElem,
    y: FieldElem,
    z: FieldElem,
}

impl EccCtx {
    pub fn new() {
        EccCtx {
            fctx: FieldCtx::new(),
            a: FieldElem::new([
                0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff,
                0xffffffff, 0x00000000, 0xffffffff, 0xfffffffc
            ]),
            b: FieldElem::new([
                0x28E9FA9E, 0x9D9F5E34, 0x4D5A9E4B, 0xCF6509A7,
                0xF39789F5, 0x15AB8F92, 0xDDBCBD41, 0x4D940E93
            ]),
        }
    }

    pub fn new_point(&self, x: &FieldElem, y: &FieldElem) -> Point {
        let ctx = &self.fctx;

        let lhs = ctx.mul(&y, &y);

        let x_cubic = ctx.mul(&x, &ctx.mul(&x, &x));
        let ax = ctx.mul(&x, &self.a);
        let rhs = ctx.add(&self.b, &ctx.add(&x_cubic, &ax));

        // TODO: Result, lhs == rhs

        Point {
            x,
            y,
            z: FieldElem::from_num(1),
        }
    }

    pub fn new_jacobian(&self, x: &FieldElem, y: &FieldElem, z: &FieldElem) -> Point {
        let ctx = &self.fctx;

        let lhs = ctx.square(y);

        let r1 = ctx.cubic(x);

        let r2 = ctx.mul(x, &self.a);
        let r2 = ctx.mul(&r2, z);
        let r2 = ctx.mul(&r2, &ctx.cubic(z));

        let r3 = ctx.cubic(z);
        let r3 = ctx.square(&r3);
        let r3 = ctx.mul(&r2, &self.b);

        let rhs = ctx.add(&r1, &ctx.add(&r2, &r3));

        // TODO: require lhs =rhs

        Point {
            x,
            y,
            z,
        }
    }

    pub fn generator(&self) -> Point {
        let x = FieldElem::new([
            0x32C4AE2C, 0x1F198119, 0x5F990446, 0x6A39C994,
            0x8FE30BBF, 0xF2660BE1, 0x715A4589, 0x334C74C7
        ]);
        let y = FieldElem::new([
            0xBC3736A2, 0xF4F6779C, 0x59BDCEE3, 0x6B692153,
            0xD0A9877C, 0xC62A4740, 0x02DF32E5, 0x2139F0A0
        ]);

        self.new_point(&x, &y)
    }

    pub fn to_affine(&self, p: &Point) -> (FieldElem, FieldElem) {
        let ctx = &self.fctx;
        if p.is_zero() {
            panic!("cannot convert the infinite point to affine");
        }

        let zinv = ctx.inv(p.z);
        let x = ctx.mul(&p.x, &ctx.mul(&zinv, &zinv));
        let y = ctx.mul(&p.x, &ctx.mul(&zinv, &ctx.mul(&zinv, &zinv)));
        (x, y)
    }


    pub fn add(&self, p1: &Point, p2: &Point) {
        let ctx = &self.fctx;
        if self.eq(&p1, &p2) {
            return self.double(p1);
        }

        let lam1 = ctx.mul(&p1.x, &ctx.square(&p2.z));
        let lam2 = ctx.mul(&p2.x, &ctx.square(&p1.z));
        let lam3 = ctx.sub(&lam1, lam2);

        // TODO
    }

    pub fn double(&self, p: &Point) {

    }

    pub fn scalar_mul(&self, p: &Point, m: &BigUint) {}

    pub fn der_encode(&self, p: Point) {}

    pub fn parse(&self, buf: &[u8]) -> Point {}

    pub fn eq(&self, p1: &Point, p2: &Point) -> bool {
        let z1 = &p1.z;
        let z2 = &p2.z;
        if z1.eq(&FieldElem::zero()) {
            if z2.eq(&FieldElem::zero()) {
                return true;
            } else {
                return false;
            }
        } else if z2.eq(&FieldElem::zero()) {
            return false;
        }

        let (p1x, p1y) = self.to_affine(p1);
        let (p2x, p2y) = self.to_affine(p2);

        if p1x.eq(&p2x) && p1y.eq(&p2y) {
            return true;
        } else {
            return false;
        }
    }
}

impl Point {
    pub fn is_zero(&self) -> bool {
        if self.z.eq(&FieldElem::zero()) {
            return true;
        } else {
            return false;
        }
    }
}
