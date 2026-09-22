/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Wizer, driven in-process. The shell reads the program on stdin (its
//! `ShellMain` is called with no script argument), so wizening a program
//! means running the shell module under wizer with stdin pointed at the
//! program file.

use anyhow::{bail, Context, Result};
use std::os::fd::AsRawFd;
use std::path::Path;

/// Snapshot `shell` after it has run `program`, returning the snapshot
/// module bytes.
pub fn wizen(shell: &Path, program: &Path) -> Result<Vec<u8>> {
    let shell_bytes =
        std::fs::read(shell).with_context(|| format!("reading {}", shell.display()))?;
    let mut w = wizer::Wizer::new();
    w.allow_wasi(true)?
        .init_func("wizer.initialize")
        // The resumed snapshot must NOT re-run the WASI ctors: `_start` has
        // already run at wizening time. Renaming `wizer.resume` over it is
        // what makes the snapshot resumable.
        .func_rename("_start", "wizer.resume")
        .inherit_stdio(true)
        .inherit_env(false);

    let file =
        std::fs::File::open(program).with_context(|| format!("reading {}", program.display()))?;
    with_stdin(file.as_raw_fd(), || w.run(&shell_bytes))?
}

/// Run `f` with `fd` installed as this process's stdin, restoring the
/// original stdin afterwards.
fn with_stdin<T>(fd: i32, f: impl FnOnce() -> T) -> Result<T> {
    // SAFETY: plain fd bookkeeping; `fd` is owned by the caller and stays
    // open for the call, and the saved descriptor is closed exactly once.
    unsafe {
        let saved = libc::dup(libc::STDIN_FILENO);
        if saved < 0 {
            bail!("dup(stdin): {}", std::io::Error::last_os_error());
        }
        if libc::dup2(fd, libc::STDIN_FILENO) < 0 {
            let e = std::io::Error::last_os_error();
            libc::close(saved);
            bail!("redirecting stdin: {e}");
        }
        let r = f();
        libc::dup2(saved, libc::STDIN_FILENO);
        libc::close(saved);
        Ok(r)
    }
}
