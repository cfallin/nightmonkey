/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/. */

//! Locate the registration block through the engine's exported
//! constant-returning accessor (`night.registration`).
//!
//! Adapted from weval's `find_global_data_by_exported_func` in
//! `src/intrinsics.rs` (bytecodealliance/weval, Apache-2.0 WITH
//! LLVM-exception): handles both a plain `i32.const` and the PIC
//! `global.get GOT + i32.const` form, under `Return` and `Br` terminators.

use waffle::{ExportKind, Func, Module, Operator, Terminator, Type, ValueDef};

fn find_exported_func(
    module: &Module,
    name: &str,
    in_tys: &[Type],
    out_tys: &[Type],
) -> Option<Func> {
    module
        .exports
        .iter()
        .find(|ex| ex.name == name)
        .and_then(|ex| match &ex.kind {
            &ExportKind::Func(f) => {
                let sig = module.funcs[f].sig();
                let sig = &module.signatures[sig];
                (&sig.params[..] == in_tys && &sig.returns[..] == out_tys).then_some(f)
            }
            _ => None,
        })
}

pub fn find_global_data_by_exported_func(module: &Module, name: &str) -> Option<u32> {
    let f = find_exported_func(module, name, &[], &[Type::I32])?;
    let mut body = module.funcs[f].clone();
    body.parse(module).ok()?;
    let body = body.body()?;

    let extract_const_value = |value| match &body.values[value] {
        ValueDef::Operator(Operator::I32Const { value }, _, _) => Some(*value),
        ValueDef::Operator(Operator::I32Add, args, _) => {
            let args = &body.arg_pool[*args];
            match (&body.values[args[0]], &body.values[args[1]]) {
                (
                    ValueDef::Operator(Operator::GlobalGet { global_index }, _, _),
                    ValueDef::Operator(Operator::I32Const { value }, _, _),
                ) => {
                    let g = &module.globals[*global_index];
                    // The PIC form is `GOT.mem base + offset`, so the global
                    // must be the i32 base; anything else is a shape we do
                    // not recognize. The add wraps in the 32-bit address
                    // space by construction.
                    (g.ty == Type::I32)
                        .then_some(g.value)
                        .flatten()
                        .map(|base| (base as u32).wrapping_add(*value))
                }
                _ => None,
            }
        }
        _ => None,
    };

    match &body.blocks[body.entry].terminator {
        Terminator::Return { values } if values.len() == 1 => extract_const_value(values[0]),
        Terminator::Br { target } if target.args.len() == 1 => {
            let val = extract_const_value(target.args[0])?;
            match &body.blocks[target.block].terminator {
                Terminator::Return { values }
                    if values.len() == 1 && values[0] == body.blocks[target.block].params[0].1 =>
                {
                    Some(val)
                }
                _ => None,
            }
        }
        _ => None,
    }
}
