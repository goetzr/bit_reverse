use std::fmt;
use std::fs::{self, File};
use std::io::{self, Read, Write};
use std::os::windows::fs::MetadataExt;
use std::path::Path;

// The maximum word size, in bytes.
const MAX_WORD_SIZE_BYTES: usize = 8;

pub fn bit_reverse<P>(in_file_path: P, out_file_path: P, word_size: WordSize) -> Result<()>
where
    P: AsRef<Path>,
{
    // Get the size of the input file.
    let in_file_size = fs::metadata(in_file_path.as_ref())
        .map_err(|e| BitReverseError::StatInputFile(e))?
        .file_size() as usize;

    // Allocate an input buffer properly aligned to the maximum word size to hold the file contents.
    // Allocate an output buffer of the same size and alignment.
    let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size)?;

    // Read the input file contents into the input buffer.
    {
        let mut in_file =
            File::open(in_file_path.as_ref()).map_err(|e| BitReverseError::OpenInputFile(e))?;
        in_file
            .read_exact(&mut in_buf[..in_file_size])
            .map_err(|e| BitReverseError::ReadInputFile(e))?;
    }

    // Reverse the bits in each word in the input buffer, storing each bit-reversed word in the output buffer.
    reverse_bits(&in_buf, &mut out_buf, word_size);

    // Write the output buffer to the output file.
    let out_file_size = determine_output_file_size(in_file_size, word_size.as_usize());
    let mut out_file =
        File::create(out_file_path).map_err(|e| BitReverseError::CreateOutputFile(e))?;
    let _ = out_file
        .write_all(&out_buf[..out_file_size])
        .map_err(|e| BitReverseError::WriteOutputFile(e));

    Ok(())
}

fn allocate_buffers(in_file_size: usize) -> Result<(Box<[u8]>, Box<[u8]>)> {
    let in_buf_size = determine_input_buffer_size(in_file_size);
    let in_buf = allocate_aligned_buf(in_buf_size, MAX_WORD_SIZE_BYTES)
        .map_err(|e| BitReverseError::AllocateMemory(format!("input buffer: {e}")))?;
    let out_buf = allocate_aligned_buf(in_buf_size, MAX_WORD_SIZE_BYTES)
        .map_err(|e| BitReverseError::AllocateMemory(format!("output buffer: {e}")))?;
    Ok((in_buf, out_buf))
}

fn determine_input_buffer_size(in_file_size: usize) -> usize {
    // Ensure the input buffer size is an even multiple of the maximum word size.
    let misalignment = in_file_size % MAX_WORD_SIZE_BYTES;
    if misalignment != 0 {
        in_file_size + (MAX_WORD_SIZE_BYTES - misalignment)
    } else {
        in_file_size
    }
}

fn determine_output_file_size(in_file_size: usize, word_size: usize) -> usize {
    // Ensure the output file size is an even multiple of the chosen word size.
    let word_size_bytes = word_size / 8;
    let misalignment = in_file_size % word_size_bytes;
    if misalignment != 0 {
        in_file_size + (word_size_bytes - misalignment)
    } else {
        in_file_size
    }
}

fn allocate_aligned_buf(
    buf_size: usize,
    word_size: usize,
) -> std::result::Result<Box<[u8]>, String> {
    use std::alloc::{self, Layout};

    // Ensure the buffer size is an even multiple of the word size.
    assert!(buf_size % word_size == 0);

    let Ok(layout) = Layout::from_size_align(buf_size, word_size) else {
        return Err(String::from("failed to construct buffer layout"));
    };

    unsafe {
        // Allocate the buffer.
        let buf = alloc::alloc(layout);
        if buf.is_null() {
            return Err(String::from("failed to allocate buffer"));
        }

        // Zero-initialize the buffer.
        buf.write_bytes(0, buf_size);

        // Create a byte slice from the buffer pointer.
        let buf = std::slice::from_raw_parts_mut(buf, buf_size);

        Ok(Box::from_raw(buf))
    }
}

fn reverse_bits(in_buf: &[u8], out_buf: &mut [u8], word_size: WordSize) {
    use WordSize::*;

    // The input and output buffers are the same size.
    let word_size_bytes = word_size.as_usize() / 8;
    let slice_len = in_buf.len() / word_size_bytes;

    match word_size {
        // Cast the input/output buffers to the appropriate byte slice type.
        // This is safe because the buffers are aligned to the maximum word size.
        Bits8 => reverse_bits8(in_buf, out_buf),
        Bits16 => {
            let in_buf: &[u16] =
                unsafe { std::slice::from_raw_parts(in_buf.as_ptr() as *const u16, slice_len) };
            let out_buf: &mut [u16] = unsafe {
                std::slice::from_raw_parts_mut(out_buf.as_mut_ptr() as *mut u16, slice_len)
            };
            reverse_bits16(in_buf, out_buf);
        }
        Bits32 => {
            let in_buf: &[u32] =
                unsafe { std::slice::from_raw_parts(in_buf.as_ptr() as *const u32, slice_len) };
            let out_buf: &mut [u32] = unsafe {
                std::slice::from_raw_parts_mut(out_buf.as_mut_ptr() as *mut u32, slice_len)
            };
            reverse_bits32(in_buf, out_buf);
        }
        Bits64 => {
            let in_buf: &[u64] =
                unsafe { std::slice::from_raw_parts(in_buf.as_ptr() as *const u64, slice_len) };
            let out_buf: &mut [u64] = unsafe {
                std::slice::from_raw_parts_mut(out_buf.as_mut_ptr() as *mut u64, slice_len)
            };
            reverse_bits64(in_buf, out_buf);
        }
    };
}

fn reverse_bits8(in_buf: &[u8], out_buf: &mut [u8]) {
    for (idx, &word8) in in_buf.iter().enumerate() {
        out_buf[idx] = LOOKUP_TABLE8[word8 as usize];
    }
}

fn reverse_bits16(in_buf: &[u16], out_buf: &mut [u16]) {
    for (idx, &word16) in in_buf.iter().enumerate() {
        out_buf[idx] = LOOKUP_TABLE16[word16 as usize];
    }
}

fn reverse_bits32(in_buf: &[u32], out_buf: &mut [u32]) {
    for (idx, &word32) in in_buf.iter().enumerate() {
        out_buf[idx] = word32.reverse_bits();
    }
}

fn reverse_bits64(in_buf: &[u64], out_buf: &mut [u64]) {
    for (idx, &word64) in in_buf.iter().enumerate() {
        out_buf[idx] = word64.reverse_bits();
    }
}

const BITS8_NUM_VALUES: usize = 256;
const LOOKUP_TABLE8: [u8; BITS8_NUM_VALUES] = build_lookup_table8();

const fn build_lookup_table8() -> [u8; BITS8_NUM_VALUES] {
    let mut table: [u8; BITS8_NUM_VALUES] = [0; BITS8_NUM_VALUES];
    let mut idx: usize = 0;
    while idx < BITS8_NUM_VALUES {
        table[idx] = (idx as u8).reverse_bits();
        idx += 1;
    }
    table
}

const BITS16_NUM_VALUES: usize = 65536;
const LOOKUP_TABLE16: [u16; BITS16_NUM_VALUES] = build_lookup_table16();

const fn build_lookup_table16() -> [u16; BITS16_NUM_VALUES] {
    let mut table: [u16; BITS16_NUM_VALUES] = [0; BITS16_NUM_VALUES];
    let mut idx: usize = 0;
    while idx < BITS16_NUM_VALUES {
        table[idx] = (idx as u16).reverse_bits();
        idx += 1;
    }
    table
}

#[derive(Clone, Copy)]
pub enum WordSize {
    Bits8,
    Bits16,
    Bits32,
    Bits64,
}

impl WordSize {
    fn as_usize(&self) -> usize {
        use WordSize::*;
        match self {
            Bits8 => 8,
            Bits16 => 16,
            Bits32 => 32,
            Bits64 => 64,
        }
    }
}

impl TryFrom<i32> for WordSize {
    type Error = WordSizeError;

    fn try_from(value: i32) -> std::result::Result<WordSize, WordSizeError> {
        match value {
            8 => Ok(WordSize::Bits8),
            16 => Ok(WordSize::Bits16),
            32 => Ok(WordSize::Bits32),
            64 => Ok(WordSize::Bits64),
            bad_size => Err(WordSizeError(bad_size)),
        }
    }
}

#[derive(Debug)]
pub struct WordSizeError(i32);

impl std::error::Error for WordSizeError {}

impl fmt::Display for WordSizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid word size {}", self.0)
    }
}

#[derive(Debug)]
pub enum BitReverseError {
    AllocateMemory(String),
    StatInputFile(io::Error),
    OpenInputFile(io::Error),
    ReadInputFile(io::Error),
    CreateOutputFile(io::Error),
    WriteOutputFile(io::Error),
}

impl std::error::Error for BitReverseError {}

impl fmt::Display for BitReverseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use BitReverseError::*;
        match self {
            AllocateMemory(msg) => write!(f, "failed to allocate memory: {msg}"),
            StatInputFile(e) => write!(f, "failed to stat input file: {e}"),
            OpenInputFile(e) => write!(f, "failed to open input file: {e}"),
            ReadInputFile(e) => write!(f, "failed to read input file: {e}"),
            CreateOutputFile(e) => write!(f, "failed to create output file: {e}"),
            WriteOutputFile(e) => write!(f, "failed to write output file: {e}"),
        }
    }
}

impl From<BitReverseError> for i32 {
    fn from(value: BitReverseError) -> i32 {
        use BitReverseError::*;
        match value {
            AllocateMemory(_) => 4,
            StatInputFile(_) => 5,
            OpenInputFile(_) => 6,
            ReadInputFile(_) => 7,
            CreateOutputFile(_) => 8,
            WriteOutputFile(_) => 9,
        }
    }
}

pub type Result<T> = std::result::Result<T, BitReverseError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reverse8() {
        let in_file_size = 4;
        let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size).unwrap();
        (&mut in_buf[..in_file_size]).copy_from_slice(&[0x34, 0xcd, 0x19, 0x27]);
        reverse_bits(&in_buf, &mut out_buf, WordSize::Bits8);
        assert_eq!(*out_buf, [0x2c, 0xb3, 0x98, 0xe4, 0, 0, 0, 0]);
    }

    #[test]
    fn reverse16() {
        let in_file_size = 6;
        let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size).unwrap();
        (&mut in_buf[..in_file_size]).copy_from_slice(&[0x34, 0xcd, 0x19, 0x27, 0x82, 0xbe]);
        reverse_bits(&in_buf, &mut out_buf, WordSize::Bits16);
        assert_eq!(*out_buf, [0xb3, 0x2c, 0xe4, 0x98, 0x7d, 0x41, 0, 0]);
    }

    #[test]
    fn reverse32() {
        let in_file_size = 8;
        let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size).unwrap();
        (&mut in_buf[..in_file_size])
            .copy_from_slice(&[0x34, 0xcd, 0x19, 0x27, 0x82, 0xbe, 0xf5, 0xab]);
        reverse_bits(&in_buf, &mut out_buf, WordSize::Bits32);
        assert_eq!(*out_buf, [0xe4, 0x98, 0xb3, 0x2c, 0xd5, 0xaf, 0x7d, 0x41]);
    }

    #[test]
    fn reverse64() {
        let in_file_size = 16;
        let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size).unwrap();
        (&mut in_buf[..in_file_size]).copy_from_slice(&[
            0x34, 0xcd, 0x19, 0x27, 0x82, 0xbe, 0xf5, 0xab, 0x43, 0xe5, 0x12, 0xd7, 0x83, 0xb9,
            0x03, 0xa1,
        ]);
        reverse_bits(&in_buf, &mut out_buf, WordSize::Bits64);
        assert_eq!(
            *out_buf,
            [
                0xd5, 0xaf, 0x7d, 0x41, 0xe4, 0x98, 0xb3, 0x2c, 0x85, 0xc0, 0x9d, 0xc1, 0xeb, 0x48,
                0xa7, 0xc2
            ]
        );
    }

    #[test]
    fn reverse16_unaligned() {
        let in_file_size = 5;
        let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size).unwrap();
        (&mut in_buf[..in_file_size]).copy_from_slice(&[0x34, 0xcd, 0x19, 0x27, 0x82]);
        reverse_bits(&in_buf, &mut out_buf, WordSize::Bits16);
        assert_eq!(*out_buf, [0xb3, 0x2c, 0xe4, 0x98, 0, 0x41, 0, 0]);
    }

    #[test]
    fn reverse32_unaligned() {
        let in_file_size = 7;
        let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size).unwrap();
        (&mut in_buf[..in_file_size]).copy_from_slice(&[0x34, 0xcd, 0x19, 0x27, 0x82, 0xbe, 0xf5]);
        reverse_bits(&in_buf, &mut out_buf, WordSize::Bits32);
        assert_eq!(*out_buf, [0xe4, 0x98, 0xb3, 0x2c, 0, 0xaf, 0x7d, 0x41]);
    }

    #[test]
    fn reverse64_unaligned() {
        let in_file_size = 15;
        let (mut in_buf, mut out_buf) = allocate_buffers(in_file_size).unwrap();
        (&mut in_buf[..in_file_size]).copy_from_slice(&[
            0x34, 0xcd, 0x19, 0x27, 0x82, 0xbe, 0xf5, 0xab, 0x43, 0xe5, 0x12, 0xd7, 0x83, 0xb9,
            0x03,
        ]);
        reverse_bits(&in_buf, &mut out_buf, WordSize::Bits64);
        assert_eq!(
            *out_buf,
            [
                0xd5, 0xaf, 0x7d, 0x41, 0xe4, 0x98, 0xb3, 0x2c, 0, 0xc0, 0x9d, 0xc1, 0xeb, 0x48,
                0xa7, 0xc2
            ]
        );
    }
}
