//! Which tier compiled each script, and the coverage census over them.
//!
//! Coverage is measured, never assumed (`DESIGN.md` §12): a script that
//! silently stays interpreted passes the same tests as one that compiled.
//! Every translated script therefore gets a [`TierStatus`] naming the tier
//! that compiled it (or the interpreter) and every decline on the way.
//! With the `tiers` diagnostic each is printed as
//! `night: tier <sid> <tier> [<declined tier>: <reason>]...`, followed by a
//! summary; under `--strict-coverage` an unexplained interpreted script
//! fails the compilation.

use std::collections::BTreeMap;

use crate::ids::ScriptId;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Tier {
    Mir,
    Baseline,
    Legacy,
    Interp,
}

impl std::fmt::Display for Tier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Tier::Mir => "mir",
            Tier::Baseline => "baseline",
            Tier::Legacy => "legacy",
            Tier::Interp => "interp",
        })
    }
}

/// One tier's refusal of a script.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Decline {
    pub tier: Tier,
    pub reason: String,
    /// The script *must* be interpreted (it contains `ForceInterpreter`),
    /// so this decline is not a coverage gap.
    pub allowed: bool,
}

impl Decline {
    pub fn new(tier: Tier, reason: impl Into<String>) -> Decline {
        Decline {
            tier,
            reason: reason.into(),
            allowed: false,
        }
    }

    /// The reason without its instance detail (a trailing parenthesized
    /// part), for grouping in the summary.
    fn class(&self) -> String {
        let r = self.reason.split(" (").next().unwrap_or(&self.reason);
        format!("{}: {r}", self.tier)
    }
}

/// Where one script ended up.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TierStatus {
    pub tier: Tier,
    pub declines: Vec<Decline>,
}

impl TierStatus {
    /// Interpreted for a reason the coverage gate does not accept.
    pub fn is_gap(&self) -> bool {
        self.tier == Tier::Interp && !self.declines.iter().any(|d| d.allowed)
    }
}

impl std::fmt::Display for TierStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.tier)?;
        for d in &self.declines {
            write!(f, " [{}: {}]", d.tier, d.reason)?;
        }
        Ok(())
    }
}

/// Per-tier counts and decline classes over a compilation, plus the
/// coverage gaps.
#[derive(Clone, Debug, Default)]
pub struct TierCensus {
    pub counts: BTreeMap<Tier, usize>,
    pub declines: BTreeMap<String, usize>,
    pub gaps: Vec<(ScriptId, TierStatus)>,
}

impl TierCensus {
    /// Count `status` for `sid`, printing its line when `diag` is on.
    pub fn record(&mut self, sid: ScriptId, status: TierStatus, diag: bool) {
        if diag {
            crate::diag_line!("night: tier {sid} {status}");
        }
        *self.counts.entry(status.tier).or_default() += 1;
        for d in &status.declines {
            *self.declines.entry(d.class()).or_default() += 1;
        }
        if status.is_gap() {
            self.gaps.push((sid, status));
        }
    }

    pub fn summary(&self) -> String {
        let n = |t| self.counts.get(&t).copied().unwrap_or(0);
        let mut s = format!(
            "night: tier summary mir={} baseline={} legacy={} interp={}",
            n(Tier::Mir),
            n(Tier::Baseline),
            n(Tier::Legacy),
            n(Tier::Interp)
        );
        for (class, count) in &self.declines {
            s.push_str(&format!(" [{class}]={count}"));
        }
        s
    }

    /// The strict-coverage verdict: an error naming the gaps, if any.
    pub fn check_strict(&self) -> Result<(), String> {
        if self.gaps.is_empty() {
            return Ok(());
        }
        const SHOWN: usize = 8;
        let listed: Vec<String> = self
            .gaps
            .iter()
            .take(SHOWN)
            .map(|(sid, st)| format!("script {sid}: {st}"))
            .collect();
        let more = self.gaps.len().saturating_sub(SHOWN);
        Err(format!(
            "strict coverage: {} script(s) interpreted: {}{}",
            self.gaps.len(),
            listed.join("; "),
            if more > 0 {
                format!("; and {more} more")
            } else {
                String::new()
            }
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn census_and_strictness() {
        let mut c = TierCensus::default();
        c.record(
            ScriptId::new(1),
            TierStatus {
                tier: Tier::Baseline,
                declines: vec![Decline::new(Tier::Mir, "no builder")],
            },
            false,
        );
        let forced = Decline {
            allowed: true,
            ..Decline::new(Tier::Baseline, "ForceInterpreter")
        };
        c.record(
            ScriptId::new(2),
            TierStatus {
                tier: Tier::Interp,
                declines: vec![forced],
            },
            false,
        );
        assert!(c.check_strict().is_ok());
        let st = TierStatus {
            tier: Tier::Interp,
            declines: vec![Decline::new(
                Tier::Legacy,
                "script too large (200000 bytecode bytes)",
            )],
        };
        assert_eq!(
            st.to_string(),
            "interp [legacy: script too large (200000 bytecode bytes)]"
        );
        c.record(ScriptId::new(3), st, false);
        assert_eq!(
            c.summary(),
            "night: tier summary mir=0 baseline=1 legacy=0 interp=2 \
             [baseline: ForceInterpreter]=1 [legacy: script too large]=1 [mir: no builder]=1"
        );
        let e = c.check_strict().unwrap_err();
        assert!(
            e.starts_with("strict coverage: 1 script(s) interpreted: script 3: interp"),
            "{e}"
        );
    }
}
