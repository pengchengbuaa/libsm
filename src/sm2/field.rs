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
            FieldCtx::raw_sub(&FieldElem::zero(), &modulus);
        FieldCtx {
            modulus,
            modulus_complete,
        }
    }

    pub fn add(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let (raw_sum, carry) = FieldCtx::raw_add(a, b);
        if carry == 1 || FieldCtx::ge(raw_sum, self.modulus) {
            let (sum, borrow) = FieldCtx::raw_sub(raw_sum, self.modulus);
            return sum;
        } else {
            return raw_sum;
        }
    }

    pub fn sub(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let (raw_diff, borrow) = FieldCtx::raw_sub(a, b);
        if borrow == 1 {
            let diff = FieldCtx::raw_sub(raw_diff, self.modulus_complete);
            return diff;
        } else {
            return raw_diff;
        }
    }

    pub fn mul(&self, a: &FieldElem, b: &FieldElem) -> FieldElem {
        let raw_prod = FieldCtx::raw_mul(a, b);
        FieldCtx::fast_reduction(raw_prod)
    }

    // TODO: Extended Eulidean Algorithm(EEA) to calculate x^(-1) mod p
    // Reference:
    // http://delta.cs.cinvestav.mx/~francisco/arith/julio.pdf for details
    pub fn inv(&self, x: &FieldElem) -> FieldElem {
        FieldElem::zero()
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
                    uv = a.value[i] as u64 * b.value[j] as u64;
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

    // TODO: a quick algorithm to reduce elements on SCA-256 field
    // Reference:
    // http://ieeexplore.ieee.org/document/7285166/ for details
    pub fn fast_reduction(x: &[u32; 16]) -> FieldElem {
        FieldElem::zero()
    }

    // TODO: square root of a field element
    // pub fn sqrt(&self, x: FieldElem) -> FieldElem(){}
}

pub struct FieldElem {
    value: [u32; 8]
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
        FieldElem::new(arr);
    }

    pub fn zero() -> FieldElem {
        FieldElem::new([0; 8])
    }

    // TODO: Conversions
    pub fn to_bytes() {}
    pub fn from_bytes() {}

    pub fn from_int(x: u64) {}

    pub fn to_hex() {}
    pub fn from_hex(x: String) {}

    pub fn to_digits() {}
    pub fn from_digits(x: String) {}
}
