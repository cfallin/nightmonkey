/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Mirror of the engine's `NightLayoutDescriptor`. The field list is generated
//! from NightRegistration.h at build time; values are read out of the guest
//! memory at the descriptor address recorded in the registration block.

use crate::mem::MemAccess;
use anyhow::{bail, Result};

include!(concat!(env!("OUT_DIR"), "/layout_fields.rs"));

pub struct Layout {
    fields: Vec<u32>,
}

impl Layout {
    pub fn read(mem: &impl MemAccess, descriptor_addr: u32) -> Result<Layout> {
        let abi = mem.read_u32(descriptor_addr)?;
        if abi != ABI_VERSION {
            bail!("layout descriptor ABI version {abi}, reader expects {ABI_VERSION}");
        }
        let num_fields = mem.read_u32(descriptor_addr + 8)? as usize;
        if num_fields != FIELD_COUNT {
            bail!("layout descriptor has {num_fields} fields, reader expects {FIELD_COUNT}");
        }
        let mut fields = Vec::with_capacity(num_fields);
        for i in 0..num_fields {
            fields.push(mem.read_u32(descriptor_addr + 12 + 4 * i as u32)?);
        }
        Ok(Layout { fields })
    }

    #[inline]
    pub fn get(&self, f: Field) -> u32 {
        self.fields[f as u32 as usize]
    }
}
