//! Reduction of constants in expressions.

use crate::{Expr};

/// Reduce constant.
///
/// This operation preserves preserves the structure of the expression,
/// but might change the constants in it.
pub fn run(e: &mut Expr) -> bool {
    let mut changed = false;
    if let Some((a, b)) = e.get_mul_mut() {
        if let (Some((_a1, a2)), Some(b)) = (a.get_div_mut(), b.get_nat_mut()) {
            if let Some(a2) = a2.get_nat_mut() {
                // `a1/k * k`.
                let mut f = |p: u64| if *a2 % p == 0 && *b % p == 0 {
                    *a2 /= p;
                    *b /= p;
                    changed = true;
                };
                f(2); f(2); f(2); f(2); f(2); f(2);
                f(3); f(3); f(3); f(3);
                f(5); f(5); f(5);
                f(7); f(7); f(7);
                f(11); f(11);
                f(13);
                f(17);
            }
        }
        if let (Some((a1, a2)), Some(b)) = (a.get_mul_mut(), b.get_recip_mut()) {
            if let (Some(a1), Some(b)) = (a1.get_nat_mut(), b.get_nat_mut()) {
                // `(k * a2) / k`.
                let mut f = |p: u64| if *a1 % p == 0 && *b % p == 0 {
                    *a1 /= p;
                    *b /= p;
                    changed = true;
                };
                f(2); f(2); f(2); f(2); f(2); f(2);
                f(3); f(3); f(3); f(3);
                f(5); f(5); f(5);
                f(7); f(7); f(7);
                f(11); f(11);
                f(13);
                f(17);
            }
            if let (Some(a2), Some(b)) = (a2.get_nat_mut(), b.get_nat_mut()) {
                // `(a1 * k) / k`.
                let mut f = |p: u64| if *a2 % p == 0 && *b % p == 0 {
                    *a2 /= p;
                    *b /= p;
                    changed = true;
                };
                f(2); f(2); f(2); f(2); f(2); f(2);
                f(3); f(3); f(3); f(3);
                f(5); f(5); f(5);
                f(7); f(7); f(7);
                f(11); f(11);
                f(13);
                f(17);
            }
        }
        if let (Some(a), Some((b1, b2))) = (a.get_nat_mut(), b.get_sub_mut()) {
            if let (Some((_b11, b12)), Some((_b21, b22))) = (b1.get_div_mut(), b2.get_div_mut()) {
                if let (Some(b12), Some(b22)) = (b12.get_nat_mut(), b22.get_nat_mut()) {
                    // `k * (b11/k - b21/k)`.
                    let mut f = |p: u64| if *a % p == 0 && *b12 % p == 0 && *b22 % p == 0 {
                        *a /= p;
                        *b12 /= p;
                        *b22 /= p;
                        changed = true;
                    };
                    f(2); f(2); f(2); f(2); f(2); f(2);
                    f(3); f(3); f(3); f(3);
                    f(5); f(5); f(5);
                    f(7); f(7); f(7);
                    f(11); f(11);
                    f(13);
                    f(17);
                }
            }
        }
        if let (Some(a), Some((b1, b2))) = (a.get_nat_mut(), b.get_add_mut()) {
            if let (Some((_b11, b12)), Some((_b21, b22))) = (b1.get_div_mut(), b2.get_div_mut()) {
                if let (Some(b12), Some(b22)) = (b12.get_nat_mut(), b22.get_nat_mut()) {
                    // `k * (b11/k + b21/k)`.
                    let mut f = |p: u64| if *a % p == 0 && *b12 % p == 0 && *b22 % p == 0 {
                        *a /= p;
                        *b12 /= p;
                        *b22 /= p;
                        changed = true;
                    };
                    f(2); f(2); f(2); f(2); f(2); f(2);
                    f(3); f(3); f(3); f(3);
                    f(5); f(5); f(5);
                    f(7); f(7); f(7);
                    f(11); f(11);
                    f(13);
                    f(17);
                }
            }
        }
        if let (Some(a), Some((b1, b2))) = (a.get_nat_mut(), b.get_sub_mut()) {
            if let (Some((_b11, b12)), Some((_b21, b22))) = (b1.get_mul_mut(), b2.get_div_mut()) {
                if let (Some((b121, b122)), Some(b22)) = (b12.get_sub_mut(), b22.get_nat_mut()) {
                    if let (Some((_b1211, b1212)), Some((_b1221, b1222))) =
                        (b121.get_div_mut(), b122.get_div_mut())
                    {
                        if let (Some(b1212), Some(b1222)) =
                            (b1212.get_nat_mut(), b1222.get_nat_mut())
                        {
                            // `k*(b11*(b1211/k-b1221/k)-b21/k).`
                            let mut f = |p: u64| if *a % p == 0 &&
                                *b1212 % p == 0 && *b1222 % p == 0 && *b22 % p == 0
                            {
                                *a /= p;
                                *b1212 /= p;
                                *b1222 /= p;
                                *b22 /= p;
                                changed = true;
                            };
                            f(2); f(2); f(2); f(2); f(2); f(2);
                            f(3); f(3); f(3); f(3);
                            f(5); f(5); f(5);
                            f(7); f(7); f(7);
                            f(11); f(11);
                            f(13);
                            f(17);
                        }
                    }
                }
            }
        }
        if let (Some(a), Some((b1, b2))) = (a.get_nat_mut(), b.get_sub_mut()) {
            if let (Some((_b11, b12)), Some((_b21, b22))) = (b1.get_mul_mut(), b2.get_mul_mut()) {
                if let (Some((b121, b122)), Some((b221, b222))) =
                    (b12.get_sub_mut(), b22.get_sub_mut())
                {
                    if let (
                        Some((_b1211, b1212)),
                        Some((_b1221, b1222)),
                        Some((_b2211, b2212)),
                        Some((_b2221, b2222))
                    ) = (
                        b121.get_div_mut(),
                        b122.get_div_mut(),
                        b221.get_div_mut(),
                        b222.get_div_mut(),
                    ) {
                        if let (
                            Some(b1212),
                            Some(b1222),
                            Some(b2212),
                            Some(b2222),
                        ) = (
                            b1212.get_nat_mut(),
                            b1222.get_nat_mut(),
                            b2212.get_nat_mut(),
                            b2222.get_nat_mut(),
                        ) {
                            // k*(b11*(b1211/k - b1221/k) - b21*(b2211/k - b2221/k))
                            let mut f = |p: u64| if *a % p == 0 &&
                                *b1212 % p == 0 && *b1222 % p == 0 &&
                                *b2212 % p == 0 && *b2222 % p == 0
                            {
                                *a /= p;
                                *b1212 /= p;
                                *b1222 /= p;
                                *b2212 /= p;
                                *b2222 /= p;
                                changed = true;
                            };
                            f(2); f(2); f(2); f(2); f(2); f(2);
                            f(3); f(3); f(3); f(3);
                            f(5); f(5); f(5);
                            f(7); f(7); f(7);
                            f(11); f(11);
                            f(13);
                            f(17);
                        }
                    }
                }
            }
        }
    }

    changed
}
