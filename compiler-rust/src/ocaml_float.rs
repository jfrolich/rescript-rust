//! OCaml's conversion of a string to a float, `float_of_string`
//! (`caml_float_of_string` in the OCaml 5.5 runtime's `floats.c`), which the
//! compiler applies to float literals: an untagged variant's literal key
//! (compiler/ml/variant_runtime.ml `literal_value_key`) and the JavaScript of
//! a hexadecimal float (compiler/core/js_number.ml
//! `caml_float_literal_to_js_string`).
//!
//! The runtime removes every `_`, then reads a `0x` constant after an
//! optional sign with `caml_float_of_hex`, and anything else with C's
//! `strtod`, which must consume the whole string. `caml_float_of_hex` keeps
//! the first 60 significant bits, rounded to odd, converts them to a double
//! and scales the result with `ldexp`; the two roundings are part of its
//! result.

/// OCaml `float_of_string_opt`.
pub fn float_of_string(s: &str) -> Option<f64> {
    let buf: Vec<u8> = s.bytes().filter(|&c| c != b'_').collect();
    if buf.is_empty() {
        return None;
    }
    let (negative, rest) = split_sign(&buf);
    if let Some(digits) = strip_hex_prefix(rest) {
        let d = caml_float_of_hex(digits)?;
        return Some(if negative { -d } else { d });
    }
    strtod(&buf)
}

fn split_sign(s: &[u8]) -> (bool, &[u8]) {
    match s.first() {
        Some(b'-') => (true, &s[1..]),
        Some(b'+') => (false, &s[1..]),
        _ => (false, s),
    }
}

fn strip_hex_prefix(s: &[u8]) -> Option<&[u8]> {
    match s {
        [b'0', b'x' | b'X', rest @ ..] => Some(rest),
        _ => None,
    }
}

fn hex_digit(c: u8) -> Option<u64> {
    match c {
        b'0'..=b'9' => Some((c - b'0') as u64),
        b'a'..=b'f' => Some((c - b'a' + 10) as u64),
        b'A'..=b'F' => Some((c - b'A' + 10) as u64),
        _ => None,
    }
}

/// C's `isspace` in the C locale.
fn is_c_space(c: u8) -> bool {
    matches!(c, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

/// C's `strtol(s, &end, 10)` on a 64-bit `long`: the value, saturated, and
/// the number of bytes read (0 when no digits were read).
fn strtol(s: &[u8]) -> (i64, usize) {
    let mut i = 0;
    while i < s.len() && is_c_space(s[i]) {
        i += 1;
    }
    let negative = match s.get(i) {
        Some(b'-') => {
            i += 1;
            true
        }
        Some(b'+') => {
            i += 1;
            false
        }
        _ => false,
    };
    let start = i;
    let mut value: i64 = 0;
    while let Some(c) = s.get(i).filter(|c| c.is_ascii_digit()) {
        let d = (c - b'0') as i64;
        value = if negative {
            value.saturating_mul(10).saturating_sub(d)
        } else {
            value.saturating_mul(10).saturating_add(d)
        };
        i += 1;
    }
    if i == start { (0, 0) } else { (value, i) }
}

/// The hexadecimal digits of a constant after `0x`: the mantissa, rounded to
/// odd past its first 60 significant bits, and the binary exponent of its
/// last digit, as `caml_float_of_hex` reads them. `Err(d)` is a result the
/// exponent decides alone (an exponent beyond `int`).
fn read_hex(s: &[u8]) -> Option<Result<(u64, i32), f64>> {
    let mut m: u64 = 0;
    let mut n_bits: i32 = 0;
    let mut m_bits: i32 = 0;
    let mut x_bits: i32 = 0;
    let mut dec_point: i32 = -1;
    let mut exp: i32 = 0;
    let mut i = 0;
    while i < s.len() {
        let c = s[i];
        i += 1;
        match c {
            b'.' => {
                if dec_point >= 0 {
                    return None;
                }
                dec_point = n_bits;
            }
            b'p' | b'P' => {
                if i >= s.len() {
                    return None;
                }
                let (e, read) = strtol(&s[i..]);
                if read == 0 || i + read != s.len() {
                    return None;
                }
                if e <= i32::MIN as i64 {
                    return Some(Err(0.0));
                } else if e >= i32::MAX as i64 {
                    return Some(Err(if m == 0 { 0.0 } else { f64::INFINITY }));
                }
                exp = e as i32;
                i = s.len();
            }
            _ => {
                let d = hex_digit(c)?;
                n_bits += 4;
                if d == 0 && m == 0 {
                    continue;
                }
                if m_bits < 60 {
                    m = (m << 4) + d;
                    m_bits += 4;
                } else {
                    if d != 0 {
                        m |= 1;
                    }
                    x_bits += 4;
                }
            }
        }
    }
    if n_bits == 0 {
        return None;
    }
    let mut adj = x_bits;
    if dec_point >= 0 {
        adj += dec_point - n_bits;
    }
    let exp = if adj > 0 && exp > i32::MAX - adj {
        i32::MAX
    } else if adj < 0 && exp < i32::MIN - adj {
        i32::MIN
    } else {
        exp + adj
    };
    Some(Ok((m, exp)))
}

/// `caml_float_of_hex`: `ldexp((double) m, exp)`.
fn caml_float_of_hex(s: &[u8]) -> Option<f64> {
    Some(match read_hex(s)? {
        Err(d) => d,
        Ok((m, exp)) => {
            let f = m as i64 as f64;
            if exp != 0 { ldexp(f, exp) } else { f }
        }
    })
}

/// A hexadecimal constant as `strtod` reads it: `m * 2^exp` rounded once.
fn strtod_hex(s: &[u8]) -> Option<f64> {
    Some(match read_hex(s)? {
        Err(d) => d,
        Ok((m, exp)) => round_scaled(m, exp as i64),
    })
}

/// `m * 2^exp` rounded to nearest, ties to even, once.
fn round_scaled(m: u64, exp: i64) -> f64 {
    if m == 0 {
        return 0.0;
    }
    // m = 1.f * 2^top
    let top = 63 - m.leading_zeros() as i64;
    let e = top + exp;
    if e > 1023 {
        return f64::INFINITY;
    }
    // The bit of `m` worth the result's last mantissa bit.
    let unit = if e >= -1022 { e - 52 } else { -1074 };
    let shift = unit - exp;
    let q = if shift <= 0 {
        m << (-shift) as u32
    } else if shift >= 64 {
        // Below half the smallest step: `m < 2^64 <= 2^(shift - 1)` unless
        // `shift` is exactly 64 and the top bit is set.
        let half = shift == 64 && m >= 1 << 63;
        let above = half && m > 1 << 63;
        u64::from(above)
    } else {
        let q = m >> shift as u32;
        let rem = m & ((1u64 << shift as u32) - 1);
        let half = 1u64 << (shift as u32 - 1);
        if rem > half || (rem == half && q & 1 == 1) {
            q + 1
        } else {
            q
        }
    };
    // `q * 2^unit`, with `q` up to 2^53 after rounding up.
    let (q, unit) = if q >= 1 << 53 {
        (q >> 1, unit + 1)
    } else {
        (q, unit)
    };
    if unit + 52 > 1023 && q >= 1 << 52 {
        return f64::INFINITY;
    }
    if q < 1 << 52 {
        // Subnormal (or rounded up to the smallest normal, which the same
        // bits spell).
        f64::from_bits(q)
    } else {
        let biased = (unit + 52 + 1023) as u64;
        f64::from_bits((biased << 52) | (q & ((1 << 52) - 1)))
    }
}

/// C's `ldexp(f, exp)` for a finite `f`: `f * 2^exp` rounded once.
fn ldexp(f: f64, exp: i32) -> f64 {
    if f == 0.0 || !f.is_finite() {
        return f;
    }
    let bits = f.to_bits();
    let negative = bits >> 63 == 1;
    let biased = ((bits >> 52) & 0x7ff) as i64;
    let frac = bits & ((1 << 52) - 1);
    // f = m * 2^e exactly.
    let (m, e) = if biased == 0 {
        (frac, -1074)
    } else {
        (frac | (1 << 52), biased - 1075)
    };
    let r = round_scaled(m, e + exp as i64);
    if negative { -r } else { r }
}

/// C's `strtod`, which must read the whole string: leading white space, a
/// sign, then `inf`, `infinity`, `nan`, `nan(...)`, a hexadecimal or a
/// decimal constant.
fn strtod(buf: &[u8]) -> Option<f64> {
    let mut i = 0;
    while i < buf.len() && is_c_space(buf[i]) {
        i += 1;
    }
    let (negative, rest) = split_sign(&buf[i..]);
    let apply = |d: f64| if negative { -d } else { d };
    let lower = rest.to_ascii_lowercase();
    if lower == b"inf" || lower == b"infinity" {
        return Some(apply(f64::INFINITY));
    }
    if let Some(after) = lower.strip_prefix(b"nan") {
        let valid = after.is_empty()
            || (after.first() == Some(&b'(')
                && after.last() == Some(&b')')
                && after[1..after.len() - 1]
                    .iter()
                    .all(|c| c.is_ascii_alphanumeric() || *c == b'_'));
        return valid.then(|| apply(f64::NAN));
    }
    if let Some(digits) = strip_hex_prefix(rest) {
        return strtod_hex(digits).map(apply);
    }
    // A decimal constant: digits with at most one point, then an optional
    // exponent with at least one digit.
    let mut j = 0;
    let mut digits = 0;
    while j < rest.len() && rest[j].is_ascii_digit() {
        j += 1;
        digits += 1;
    }
    if rest.get(j) == Some(&b'.') {
        j += 1;
        while j < rest.len() && rest[j].is_ascii_digit() {
            j += 1;
            digits += 1;
        }
    }
    if digits == 0 {
        return None;
    }
    if matches!(rest.get(j), Some(b'e' | b'E')) {
        let mut k = j + 1;
        if matches!(rest.get(k), Some(b'+' | b'-')) {
            k += 1;
        }
        let start = k;
        while k < rest.len() && rest[k].is_ascii_digit() {
            k += 1;
        }
        if k == start {
            // `strtod` stops before the `e`, short of the end.
            return None;
        }
        j = k;
    }
    if j != rest.len() {
        return None;
    }
    let text = std::str::from_utf8(rest).ok()?;
    text.parse::<f64>().ok().map(apply)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// OCaml 5.5.2's `float_of_string_opt`, printed with `%h` (`NONE` when it
    /// fails).
    #[test]
    fn float_of_string_matches_ocaml() {
        let cases: &[(&str, &str)] = &[
            ("_0x1p0", "0x1p+0"),
            ("-_0x1p0", "-0x1p+0"),
            ("0_x1p0", "0x1p+0"),
            ("0x_1p0", "0x1p+0"),
            ("0x1p_3", "0x1p+3"),
            ("0x1p 3", "0x1p+3"),
            ("0x1p+3", "0x1p+3"),
            ("0x1p", "NONE"),
            ("0x1p-", "NONE"),
            ("0x", "NONE"),
            ("0x.p1", "NONE"),
            ("0x.", "NONE"),
            ("  0x1p0", "0x1p+0"),
            ("  -0x1p-1074", "-0x0.0000000000001p-1022"),
            ("0x1p-1075", "0x0p+0"),
            ("0x3p-1075", "0x0.0000000000002p-1022"),
            ("0x1.8p-1074", "0x0.0000000000002p-1022"),
            ("0x1.00000000000008p0", "0x1p+0"),
            ("0x1.00000000000018p0", "0x1.0000000000002p+0"),
            ("0x1.000000000000081p0", "0x1.0000000000001p+0"),
            ("0x123456789abcdef12p0", "0x1.23456789abcdfp+64"),
            ("0x1p99999999999", "infinity"),
            ("0x0p99999999999", "0x0p+0"),
            ("0x1p-99999999999", "0x0p+0"),
            ("0x1.fffffffffffff8p1023", "infinity"),
            ("nan(123)", "nan"),
            ("-nan(abc)", "-nan"),
            ("NaN", "nan"),
            ("INF", "infinity"),
            ("-Infinity", "-infinity"),
            ("1.5 ", "NONE"),
            ("\t1.5", "0x1.8p+0"),
            ("1e", "NONE"),
            ("e5", "NONE"),
            (".5", "0x1p-1"),
            ("5.", "0x1.4p+2"),
            (".", "NONE"),
            ("-", "NONE"),
            ("", "NONE"),
            ("_", "NONE"),
            ("1__2", "0x1.8p+3"),
            ("0x1.8", "0x1.8p+0"),
            ("0xA.Bp-2", "0x1.56p+1"),
            ("0x1p+1_0", "0x1p+10"),
        ];
        let mismatches: Vec<_> = cases
            .iter()
            .map(|(s, expected)| {
                let got = float_of_string(s).map_or("NONE".to_string(), |x| {
                    crate::types::variant_runtime::ocaml_hex_float(x)
                });
                (*s, *expected, got)
            })
            .filter(|(_, expected, got)| expected != got)
            .collect();
        assert!(mismatches.is_empty(), "{mismatches:?}");
    }
}
