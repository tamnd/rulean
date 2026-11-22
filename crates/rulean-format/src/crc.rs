//! CRC-32C (Castagnoli), for the section checksums of the binary format (spec 07.2.2).
//!
//! The function reads 8 bytes in each step with 8 tables ("slicing by 8"), so it uses few instructions for each byte.

/// The reflected polynomial of CRC-32C.
const POLY: u32 = 0x82f6_3b78;

/// The 8 tables. Table 0 is the table of one byte. Table `k` gives the effect of a byte that has `k` more bytes after it.
const TABLES: [[u32; 256]; 8] = make_tables();

const fn make_tables() -> [[u32; 256]; 8] {
    let mut t = [[0u32; 256]; 8];
    let mut i = 0;
    while i < 256 {
        let mut c = i as u32;
        let mut j = 0;
        while j < 8 {
            c = if c & 1 != 0 { (c >> 1) ^ POLY } else { c >> 1 };
            j += 1;
        }
        t[0][i] = c;
        i += 1;
    }
    let mut k = 1;
    while k < 8 {
        let mut i = 0;
        while i < 256 {
            let c = t[k - 1][i];
            t[k][i] = (c >> 8) ^ t[0][(c & 0xff) as usize];
            i += 1;
        }
        k += 1;
    }
    t
}

/// The CRC-32C of `b[start..end]`. The caller makes sure that `start <= end <= b.len()`.
pub fn crc32c(b: &[u8], start: usize, end: usize) -> u32 {
    let mut c: u32 = !0;
    let mut i = start;
    while i + 8 <= end {
        let lo = c ^ u32::from_le_bytes([b[i], b[i + 1], b[i + 2], b[i + 3]]);
        c = TABLES[7][(lo & 0xff) as usize]
            ^ TABLES[6][((lo >> 8) & 0xff) as usize]
            ^ TABLES[5][((lo >> 16) & 0xff) as usize]
            ^ TABLES[4][(lo >> 24) as usize]
            ^ TABLES[3][b[i + 4] as usize]
            ^ TABLES[2][b[i + 5] as usize]
            ^ TABLES[1][b[i + 6] as usize]
            ^ TABLES[0][b[i + 7] as usize];
        i += 8;
    }
    while i < end {
        c = (c >> 8) ^ TABLES[0][((c ^ b[i] as u32) & 0xff) as usize];
        i += 1;
    }
    !c
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn known_values() {
        // The check value of CRC-32C.
        assert_eq!(crc32c(b"123456789", 0, 9), 0xe306_9283);
        assert_eq!(crc32c(b"", 0, 0), 0);
        // 32 zero bytes, from RFC 3720, appendix B.4.
        let z = [0u8; 32];
        assert_eq!(crc32c(&z, 0, 32), 0x8a91_36aa);
        let f = [0xffu8; 32];
        assert_eq!(crc32c(&f, 0, 32), 0x62a8_ab43);
    }

    #[test]
    fn slices_agree_with_one_byte_steps() {
        let mut b = [0u8; 61];
        let mut i = 0;
        while i < b.len() {
            b[i] = (i * 37 + 11) as u8;
            i += 1;
        }
        let mut n = 0;
        while n <= b.len() {
            let mut c: u32 = !0;
            let mut j = 0;
            while j < n {
                c = (c >> 8) ^ TABLES[0][((c ^ b[j] as u32) & 0xff) as usize];
                j += 1;
            }
            assert_eq!(crc32c(&b, 0, n), !c);
            n += 1;
        }
    }
}
