use std::ffi::{CStr, CString, c_char, c_int, c_ulonglong};

#[unsafe(no_mangle)]
pub extern "C" fn bit_reverse(
    in_file_path: *const c_char,
    out_file_path: *const c_char,
    word_size: c_int,
    err_msg: *mut c_char,
    err_msg_capacity: c_ulonglong,
) -> c_int {
    if in_file_path.is_null() {
        write_c_str("input file path is NULL", err_msg, err_msg_capacity);
        return 1;
    }
    let Ok(in_file_path) = (unsafe { CStr::from_ptr(in_file_path).to_str() }) else {
        write_c_str(
            "input file path is not valid UTF-8",
            err_msg,
            err_msg_capacity,
        );
        return 1;
    };

    if out_file_path.is_null() {
        write_c_str("output file path is NULL", err_msg, err_msg_capacity);
        return 2;
    }
    let Ok(out_file_path) = (unsafe { CStr::from_ptr(out_file_path).to_str() }) else {
        write_c_str(
            "output file path is not valid UTF-8",
            err_msg,
            err_msg_capacity,
        );
        return 2;
    };

    // // The output file is placed in the same directory as the input file.
    // // The output file name is the same as the input file name with "_reversed" appended.
    // let in_file_path = Path::new(in_file_path);
    // let in_file_dir = in_file_path.parent().unwrap_or(Path::new(""));
    // // The cast to &str for the stem and extension will succeed because we already validated above that in_file_path contains valid UTF-8.
    // // Unwrapping the stem is safe because we already validated above that in_file_path is not empty.
    // let in_file_stem =
    //     unsafe { str::from_utf8_unchecked(in_file_path.file_stem().unwrap().as_encoded_bytes()) };
    // let in_file_ext = in_file_path
    //     .extension()
    //     .map(|ext| unsafe { str::from_utf8_unchecked(ext.as_encoded_bytes()) })
    //     .unwrap_or("");
    // let out_file_name = format!("{in_file_stem}_reversed{in_file_ext}");
    // let out_file_path = in_file_dir.join(out_file_name);

    let Ok(word_size) = bit_reverse::WordSize::try_from(word_size) else {
        write_c_str("invalid word size", err_msg, err_msg_capacity);
        return 3;
    };

    match bit_reverse::bit_reverse(in_file_path, out_file_path, word_size) {
        Ok(()) => 0,
        Err(e) => {
            write_c_str(e.to_string().as_str(), err_msg, err_msg_capacity);
            e.into()
        }
    }
}

fn write_c_str(src: &str, dst: *mut c_char, dst_cap: c_ulonglong) {
    // This count does not include the NULL terminator. Subtract 1 from dst_cap to leave room for the NULL terminator.
    let count = std::cmp::min(src.len(), (dst_cap - 1) as usize);
    // Only grab the amount of src that will fit in dst.
    let src = &src[..count];
    // This adds the NULL terminator.
    let src = CString::new(src).unwrap();
    // Write count + 1 so the NULL terminator is included.
    unsafe { dst.copy_from_nonoverlapping(src.as_ptr(), count + 1) };
}
