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
    pub fn new() -> EccCtx {
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

    pub fn new_point(&self, x: &FieldElem, y: &FieldElem) -> Result<Point, String>
    {
        let ctx = &self.fctx;

        // Check if (x, y) is a valid point on the curve(affine projection)
        // y^2 = x^3 + a * x + b
        let lhs = ctx.mul(&y, &y);

        let x_cubic = ctx.mul(&x, &ctx.mul(&x, &x));
        let ax = ctx.mul(&x, &self.a);
        let rhs = ctx.add(&self.b, &ctx.add(&x_cubic, &ax));

        if !lhs.eq(&rhs) {
            return Err(String::from("invalid point"));
        }

        let p = Point {
            x: *x,
            y: *y,
            z: FieldElem::from_num(1),
        };
        return Ok(p);
    }

    pub fn new_jacobian(&self, x: &FieldElem, y: &FieldElem, z: &FieldElem)
                        -> Result<Point, String>
    {
        let ctx = &self.fctx;

        // Check if (x, y, z) is a valid point on the curve(in jacobian projection)
        // y^2 = x^3 + a * x * z^4 + b * z^6
        let lhs = ctx.square(y);

        let r1 = ctx.cubic(x);

        let r2 = ctx.mul(x, &self.a);
        let r2 = ctx.mul(&r2, z);
        let r2 = ctx.mul(&r2, &ctx.cubic(z));

        let r3 = ctx.cubic(z);
        let r3 = ctx.square(&r3);
        let r3 = ctx.mul(&r3, &self.b);

        let rhs = ctx.add(&r1, &ctx.add(&r2, &r3));

        // Require lhs =rhs
        if !lhs.eq(&rhs) {
            return Err(String::from("invalid jacobian point"));
        }

        let p = Point {
            x: *x,
            y: *y,
            z: *z,
        };
        return Ok(p);
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

        match self.new_point(&x, &y) {
            Ok(p) => p,
            Err(m) => panic!(m),
        }
    }

    pub fn to_affine(&self, p: &Point) -> (FieldElem, FieldElem) {
        let ctx = &self.fctx;
        if p.is_zero() {
            panic!("cannot convert the infinite point to affine");
        }

        let zinv = ctx.inv(&p.z);
        let x = ctx.mul(&p.x, &ctx.mul(&zinv, &zinv));
        let y = ctx.mul(&p.y, &ctx.mul(&zinv, &ctx.mul(&zinv, &zinv)));
        (x, y)
    }

    pub fn neg(&self, p: &Point) -> Point{
        let neg_y = self.fctx.neg(&p.y);
        match self.new_jacobian(&p.x, &neg_y, &p.z) {
            Ok(neg_p) => neg_p,
            Err(e) => panic!(e),
        }
    }

    pub fn add(&self, p1: &Point, p2: &Point) -> Point {
        let ctx = &self.fctx;
        if self.eq(&p1, &p2) {
            return self.double(p1);
        }

        let lam1 = ctx.mul(&p1.x, &ctx.square(&p2.z));
        let lam2 = ctx.mul(&p2.x, &ctx.square(&p1.z));
        let lam3 = ctx.sub(&lam1, &lam2);

        let lam4 = ctx.mul(&p1.y, &ctx.cubic(&p2.z));
        let lam5 = ctx.mul(&p2.y, &ctx.cubic(&p1.z));
        let lam6 = ctx.sub(&lam4, &lam5);

        let lam7 = ctx.add(&lam1, &lam2);
        let lam8 = ctx.add(&lam4, &lam5);

        let x3 = ctx.sub(
            &ctx.square(&lam6),
            &ctx.mul(&lam7, &ctx.square(&lam3))
        );

        let lam9 = ctx.sub(
            &ctx.mul(&lam7, &ctx.square(&lam3)),
            &ctx.mul(&FieldElem::from_num(2), &x3)
        );

        let inv2 = ctx.inv(&FieldElem::from_num(2));
        let y3 = ctx.mul(
            &inv2,
            &ctx.sub(
                &ctx.mul(&lam9, &lam6),
                &ctx.mul(&lam8, &ctx.cubic(&lam3))
            )
        );

        let z3 = ctx.mul(&p1.z, &ctx.mul(&p2.z, &lam3));

        match self.new_jacobian(&x3, &y3, &z3) {
            Ok(new_p) => new_p,
            Err(e) => panic!(e),
        }
    }

    pub fn double(&self, p: &Point) -> Point {
        let ctx = &self.fctx;
        // λ1 = 3 * x1^2 + a * z1^4
        let lam1 = ctx.add(
            &ctx.mul(&FieldElem::from_num(3), &ctx.square(&p.x)),
            &ctx.mul(&self.a, &ctx.square(&ctx.square(&p.z)))
        );
        // λ2 = 4 * x1 * y1^2
        let lam2 = &ctx.mul(
            &FieldElem::from_num(4),
            &ctx.mul(&p.x, &ctx.square(&p.y)));
        // λ3 = 8 * y1^4
        let lam3 = &ctx.mul(
            &FieldElem::from_num(8),
            &ctx.square(&ctx.square(&p.y)));

        // x3 = λ1^2 - 2 * λ2
        let x3 = ctx.sub(
            &ctx.square(&lam1),
            &ctx.mul(&FieldElem::from_num(2), &lam2),
        );
        // y3 = λ1 * (λ2 - x3) - λ3
        let y3 = ctx.sub(
            &ctx.mul(
                &lam1,
                &ctx.sub(&lam2, &x3),
            ),
            &lam3,
        );
        // z3 = 2 * y1 * z1
        let z3 = &ctx.mul(
            &FieldElem::from_num(2),
            &ctx.mul(&p.y, &p.z));

        match self.new_jacobian(&x3, &y3, &z3) {
            Ok(new_p) => new_p,
            Err(e) => panic!(e),
        }
    }

    // TODO:
    //pub fn scalar_mul(&self, p: &Point, m: &BigUint) {}

    // TODO:
    // pub fn der_encode(&self, p: Point) {}

    // TODO:
    // pub fn parse(&self, buf: &[u8]){}

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

use std::fmt;

impl fmt::Display for Point {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let curve = EccCtx::new();
        let (x, y) = curve.to_affine(self);
        writeln!(f, "(x = {}, y = {})", x.to_str(10), y.to_str(10));
        write!(f, "x: {}, y: {}, z:{}",
               self.x.to_str(10), self.y.to_str(10), self.z.to_str(10))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_double_neg() {
        let curve = EccCtx::new();
        let g = curve.generator();

        let neg_g = curve.neg(&g);
        let double_g = curve.double(&g);
        let new_g = curve.add(&double_g, &neg_g);

        assert!(curve.eq(&g, &new_g));
    }
}
