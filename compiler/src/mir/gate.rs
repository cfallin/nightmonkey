//! Which tier compiles a script, and the coverage census that reports it.
//!
//! Coverage is measured, never assumed (MIR.md §13): with the `mir`
//! diagnostic on, every translated script gets one
//! `night: mir <sid> <status>` line, and the run ends with a summary
//! counting each status (declines by reason).

use std::collections::BTreeMap;

use crate::ids::ScriptId;
use crate::options::MirMode;

/// What happened to one script.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum MirStatus {
    /// The MIR builder produced the script's body.
    Compiled,
    /// The builder declined; the script falls back to legacy (`On`) or
    /// GEN-only (`Only`).
    Declined(String),
    /// MIR is off.
    Legacy,
}

impl std::fmt::Display for MirStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MirStatus::Compiled => f.write_str("compiled"),
            MirStatus::Declined(r) => write!(f, "declined:{r}"),
            MirStatus::Legacy => f.write_str("legacy"),
        }
    }
}

/// The builder's verdict for a script under `mode`. There is no builder
/// until M2, so every script it is offered declines.
pub fn status(mode: MirMode) -> MirStatus {
    match mode {
        MirMode::Off => MirStatus::Legacy,
        MirMode::On | MirMode::Only => MirStatus::Declined("no-builder".into()),
    }
}

/// Per-status counts over a compilation.
#[derive(Clone, Debug, Default)]
pub struct MirCensus {
    pub compiled: usize,
    pub legacy: usize,
    pub declined: BTreeMap<String, usize>,
}

impl MirCensus {
    /// Count `status` for `sid`, printing its line when `diag` is on.
    pub fn record(&mut self, sid: ScriptId, status: &MirStatus, diag: bool) {
        if diag {
            crate::diag_line!("night: mir {sid} {status}");
        }
        match status {
            MirStatus::Compiled => self.compiled += 1,
            MirStatus::Legacy => self.legacy += 1,
            MirStatus::Declined(r) => *self.declined.entry(r.clone()).or_default() += 1,
        }
    }

    /// The summary line: totals, then declines by reason.
    pub fn summary(&self) -> String {
        let declined: usize = self.declined.values().sum();
        let mut s = format!(
            "night: mir summary compiled={} declined={declined} legacy={}",
            self.compiled, self.legacy
        );
        for (r, n) in &self.declined {
            s.push_str(&format!(" declined:{r}={n}"));
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn census() {
        let mut c = MirCensus::default();
        c.record(ScriptId::new(1), &status(MirMode::On), false);
        c.record(ScriptId::new(2), &status(MirMode::On), false);
        c.record(ScriptId::new(3), &MirStatus::Compiled, false);
        c.record(ScriptId::new(4), &status(MirMode::Off), false);
        assert_eq!(
            c.summary(),
            "night: mir summary compiled=1 declined=2 legacy=1 declined:no-builder=2"
        );
        assert_eq!(
            MirStatus::Declined("env".into()).to_string(),
            "declined:env"
        );
    }
}
