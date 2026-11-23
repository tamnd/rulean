//! The input layout of the `olean` target.
//!
//! The first byte is a mask. Bit `i` is set if part `i` exists, in the order `.olean`, `.olean.server`, `.olean.private`. Each part that exists follows, with a length of 4 bytes (little-endian) before it. The last part that exists has no length and takes the rest of the input. A length that is longer than the rest of the input takes the rest of the input.

/// Splits an input into the parts of one module.
pub fn split(data: &[u8]) -> [Option<Vec<u8>>; 3] {
    let mut out = [None, None, None];
    let Some((&mask, mut rest)) = data.split_first() else {
        return out;
    };
    let present: Vec<usize> = (0..3).filter(|i| mask & (1 << i) != 0).collect();
    for (j, &i) in present.iter().enumerate() {
        if j + 1 == present.len() {
            out[i] = Some(rest.to_vec());
            break;
        }
        let n = match rest.get(..4) {
            Some(b) => u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as usize,
            None => 0,
        };
        rest = rest.get(4..).unwrap_or(&[]);
        let n = n.min(rest.len());
        out[i] = Some(rest[..n].to_vec());
        rest = &rest[n..];
    }
    out
}

/// Joins the parts of one module into one input. `split` gives the parts again.
pub fn join(parts: &[Option<Vec<u8>>; 3]) -> Vec<u8> {
    let mut mask = 0u8;
    for (i, p) in parts.iter().enumerate() {
        if p.is_some() {
            mask |= 1 << i;
        }
    }
    let present: Vec<&Vec<u8>> = parts.iter().flatten().collect();
    let mut out = vec![mask];
    for (j, p) in present.iter().enumerate() {
        if j + 1 < present.len() {
            let n = u32::try_from(p.len()).unwrap_or(u32::MAX);
            out.extend_from_slice(&n.to_le_bytes());
        }
        out.extend_from_slice(p);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn split_gives_the_parts_of_join() {
        let cases = [
            [Some(vec![1, 2, 3]), Some(vec![]), Some(vec![9; 10])],
            [Some(vec![1]), None, Some(vec![2, 2])],
            [Some(vec![5; 3]), None, None],
            [None, None, None],
        ];
        for parts in cases {
            assert_eq!(split(&join(&parts)), parts);
        }
        assert_eq!(split(&[7, 200, 0, 0, 0, 1]), [Some(vec![1]), None, None]);
    }
}
