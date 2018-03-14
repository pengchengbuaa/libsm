// Implementation of the prime field(SCA-256) used by SM2

// References:
// http://www.oscca.gov.cn/sca/xxgk/2010-12/17/1002386/files/b965ce832cc34bc191cb1cde446b860d.pdf
// http://www.oscca.gov.cn/sca/xxgk/2010-12/17/1002386/files/b791a9f908bb4803875ab6aeeb7b4e03.pdf

pub struct FieldCtx {
    modulus: FieldElem,
    modulus_complete: FieldElem,
}

impl FieldCtx {
    pub fn new() -> FieldCtx {
        // p = FFFFFFFE FFFFFFFF FFFFFFFF FFFFFFFF FFFFFFFF 00000000 FFFFFFFF FFFFFFFF
        //   = 2^256 - 2^224 - 2^96 + 2^32 -1
        let modulus = FieldElem::new([
            0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff,
            0xffffffff, 0x00000000, 0xffffffff, 0xffffffff
        ]);

        let (modulus_complete, borrow) =
            raw_sub(&FieldElem::zero(), &modulus);
        FieldCtx {
            modulus,
            modulus_complete,
        }
    }

    pub fn add(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let (raw_sum, carry) = raw_add(a, b);
        if carry == 1 || raw_sum.ge(&self.modulus) {
            let (sum, borrow) = raw_sub(&raw_sum, &self.modulus);
            return sum;
        } else {
            return raw_sum;
        }
    }

    pub fn sub(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let (raw_diff, borrow) = raw_sub(a, b);
        if borrow == 1 {
            let (diff, borrow) = raw_sub(&raw_diff, &self.modulus_complete);
            return diff;
        } else {
            return raw_diff;
        }
    }

    // a quick algorithm to reduce elements on SCA-256 field
// Reference:
// http://ieeexplore.ieee.org/document/7285166/ for details
    fn fast_reduction(&self, input: &[u32; 16]) -> FieldElem {
        let mut s: [FieldElem; 10] = [FieldElem::zero(); 10];
        let mut x: [u32; 16] = [0; 16];
        for i in 0..16 {
            x[i] = input[15 - i];
        }

        s[0] = FieldElem::new([
            x[7], x[6], x[5], x[4], x[3], x[2], x[1], x[0]
        ]);
        s[1] = FieldElem::new([
            x[15], 0, 0, 0, 0, 0, x[15], x[14]
        ]);
        s[2] = FieldElem::new([
            x[14], 0, 0, 0, 0, 0, x[14], x[13]
        ]);
        s[3] = FieldElem::new([
            x[13], 0, 0, 0, 0, 0, 0, 0
        ]);
        s[4] = FieldElem::new([
            x[12], 0, x[15], x[14], x[13], 0, 0, x[15]
        ]);
        s[5] = FieldElem::new([
            x[15], x[15], x[14], x[13], x[12], 0, x[11], x[10]
        ]);
        s[6] = FieldElem::new([
            x[11], x[14], x[13], x[12], x[11], 0, x[10], x[9]
        ]);
        s[7] = FieldElem::new([
            x[10], x[11], x[10], x[9], x[8], 0, x[13], x[12]
        ]);
        s[8] = FieldElem::new([
            x[9], 0, 0, x[15], x[14], 0, x[9], x[8]
        ]);
        s[9] = FieldElem::new([
            x[8], 0, 0, 0, x[15], 0, x[12], x[11]
        ]);

        let mut carry: i32 = 0;
        let mut sum = FieldElem::zero();

        println!("start reduction");
        for i in 1..5 {
            let (t, c) = raw_add(&sum, &s[i]);
            sum = t;
            carry = carry + c as i32;
        }
        let (t, c) = raw_add(&sum, &sum);
        sum = t;
        carry = carry * 2 + c as i32;

        for i in 5..10 {
            let (t, c) = raw_add(&sum, &s[i]);
            sum = t;
            carry = carry + c as i32;
        }

        let mut part3 = FieldElem::zero();
        let t: u64 = x[8] as u64 + x[9] as u64 + x[13] as u64 + x[14] as u64;
        part3.value[5] = (t & 0xffffffff) as u32;
        part3.value[4] = (t >> 32) as u32;

        let (t, c) = raw_add(&sum, &s[0]);
        sum = t;
        carry = carry + c as i32;

        let (t, c) = raw_sub(&sum, &part3);
        sum = t;
        carry = carry - c as i32;

        println!("get carry:{}", carry);
        println!("get sum:{:?}", sum.value);

        while carry > 0 || sum.ge(&self.modulus) {
            let (s, b) = raw_sub(&sum, &self.modulus);
            sum = s;
            carry -= b as i32;
        }
        sum
    }


    pub fn mul(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let raw_prod = raw_mul(a, b);
        self.fast_reduction(&raw_prod)
    }

    // TODO: Extended Eulidean Algorithm(EEA) to calculate x^(-1) mod p
    // Reference:
    // http://delta.cs.cinvestav.mx/~francisco/arith/julio.pdf for details
    pub fn inv(&self, x: &FieldElem) -> FieldElem {
        FieldElem::zero()
    }

    // TODO: square root of a field element
    // pub fn sqrt(&self, x: FieldElem) -> FieldElem(){}
}

#[derive(Copy, Clone)]
pub struct FieldElem {
    value: [u32; 8]
}

fn raw_add(a: &FieldElem, b: &FieldElem) -> (FieldElem, u32) {
    let mut sum = FieldElem::zero();
    let mut carry: u32 = 0;
    for i in 0..8 {
        let i = 7 - i;
        let t_sum: u64 = a.value[i] as u64 + b.value[i] as u64 + carry as u64;
        sum.value[i] = (t_sum & 0xffffffff) as u32;
        carry = (t_sum >> 32) as u32;
    }
    (sum, carry)
}

fn raw_sub(a: &FieldElem, b: &FieldElem) -> (FieldElem, u32) {
    let mut sum = FieldElem::new([0; 8]);
    let mut borrow: u32 = 0;
    for i in 0..8 {
        let i = 7 - i;
        let t_sum: i64 = a.value[i] as i64 - b.value[i] as i64 - borrow as i64;
        if t_sum < 0 {
            sum.value[i] = (t_sum + (1 << 32)) as u32;
            borrow = 1;
        } else {
            sum.value[i] = t_sum as u32;
            borrow = 0;
        }
    }
    (sum, borrow)
}

fn raw_mul(a: &FieldElem, b: &FieldElem) -> [u32; 16] {
    let mut local: u64 = 0;
    let mut carry: u64 = 0;
    let mut ret: [u32; 16] = [0; 16];

    let mut uv: u64;

    for k in 0..15 {
        let index = 15 - k;
        for i in 0..8 {
            if i > k {
                break;
            }
            let j = k - i;
            if j < 8 {
                uv = a.value[7 - i] as u64 * b.value[7 - j] as u64;
                local += uv & 0xffffffff;
                carry += uv >> 32;
            }
        }
        carry += local >> 32;
        local = local & 0xffffffff;

        ret[index] = local as u32;
        local = carry;
        carry = 0;
    }
    ret[0] = local as u32;
    ret
}

impl FieldElem {
    pub fn new(x: [u32; 8]) -> FieldElem {
        FieldElem {
            value: x
        }
    }

    pub fn from_slice(x: &[u32]) -> FieldElem {
        let mut arr: [u32; 8] = [0; 8];
        for i in 0..8 {
            arr[i] = x[i];
        }
        FieldElem::new(arr)
    }

    pub fn zero() -> FieldElem {
        FieldElem::new([0; 8])
    }

    // self >= x
    pub fn ge(&self, x: &FieldElem) -> bool {
        for i in 0..8 {
            if self.value[i] < x.value[i] {
                return false;
            } else if self.value[i] > x.value[i] {
                return true;
            }
        }
        return true;
    }

    pub fn eq(&self, x: &FieldElem) -> bool {
        for i in 0..8 {
            if self.value[i] != x.value[i] {
                return false;
            }
        }
        return true;
    }


    // TODO: Conversions
    pub fn to_bytes() {}
    pub fn from_bytes() {}

    pub fn from_num(x: u64) -> FieldElem {
        let mut arr: [u32; 8] = [0; 8];
        arr[7] = (x & 0xffffffff) as u32;
        arr[6] = (x >> 32) as u32;

        FieldElem::new(arr)
    }

    pub fn to_hex() {}
    pub fn from_hex(x: String) {}

    pub fn to_digits() {}
    pub fn from_digits(x: String) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    use rand::os::OsRng;
    use rand::Rng;

    #[test]
    fn test_add() {
        let ctx = FieldCtx::new();

        let a = FieldElem::from_num(1);
        let b = FieldElem::from_num(0xffffffff);
        let c = ctx.add(&a, &b);
        let c1 = FieldElem::from_num(0x100000000);
        assert!(c.eq(&c1));

        let b1 = ctx.add(&ctx.modulus, &b);
        assert!(b1.eq(&b));
    }

    #[test]
    fn test_sub() {
        let ctx = FieldCtx::new();

        let a = FieldElem::from_num(0xffffffff);
        let a1 = ctx.sub(&a, &ctx.modulus);
        assert!(a.eq(&a1));
    }

    fn rand_elem() -> FieldElem {
        let mut rng = OsRng::new().unwrap();
        let mut buf: [u32; 8] = [0; 8];
        for i in 0..8 {
            buf[i] = rng.next_u32();
        }

        let ret = FieldElem::new(buf);
        let ctx = FieldCtx::new();
        if ret.ge(&ctx.modulus) {
            let (ret, borrow) = raw_sub(&ret, &ctx.modulus);
            return ret;
        }
        ret
    }

    #[test]
    fn add_sub_rand_test() {
        let ctx = FieldCtx::new();

        for i in 0..20 {
            let a = rand_elem();
            let b = rand_elem();
            let c = ctx.add(&a, &b);
            let a1 = ctx.sub(&c, &b);
            assert!(a1.eq(&a));
        }
    }

    // TODO: test multiplilcations
    #[test]
    fn test_mul() {
        let ctx = FieldCtx::new();
        let x = raw_mul(&ctx.modulus, &ctx.modulus);
        let y = ctx.fast_reduction(&x);
        assert!(y.eq(&FieldElem::zero()));
    }
}
