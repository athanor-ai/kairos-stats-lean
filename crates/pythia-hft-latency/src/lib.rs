//! # pythia-hft-latency
//!
//! Pipeline latency bounding and worst-case execution time analysis.
//!
//! ## Lean specifications
//!
//! Combines theorems from `Pythia.Finance.HFT.LatencyBound` and
//! `Pythia.Finance.HFT.Latency`:
//!
//! - **Pipeline bounded**: `Σ stages ≤ n * t_max` (`pipeline_bounded`)
//! - **Jitter bounded**: max-min ≤ `n * (t_max - t_min)` (`jitter_bounded`)
//! - **Batch amortization**: `N ≤ ceil(N/B) * B` (`batch_rounds`)
//! - **O(1) cancel with index** (`cancel_with_index_constant`)
//! - **O(k) match in fills** (`match_linear_in_fills`)
//!
//! ## Use case
//!
//! FPGA and ASIC designers need provable WCET bounds per pipeline
//! stage. This crate lets you declare stage latencies, then query
//! the total pipeline bound and jitter — backed by Lean proofs.

use std::time::Duration;

/// A pipeline stage with a name and worst-case latency.
#[derive(Debug, Clone)]
pub struct Stage {
    pub name: &'static str,
    pub wcet_ns: u64,
    pub best_ns: u64,
}

impl Stage {
    pub const fn new(name: &'static str, wcet_ns: u64, best_ns: u64) -> Self {
        Self { name, wcet_ns, best_ns }
    }

    pub fn jitter_ns(&self) -> u64 {
        self.wcet_ns - self.best_ns
    }
}

/// A sequential pipeline of stages with provable latency bounds.
///
/// All bounds are derived from `Pythia.Finance.HFT.LatencyBound`.
pub struct Pipeline {
    stages: Vec<Stage>,
}

impl Pipeline {
    pub fn new(stages: Vec<Stage>) -> Self {
        Self { stages }
    }

    /// Number of stages.
    pub fn len(&self) -> usize {
        self.stages.len()
    }

    pub fn is_empty(&self) -> bool {
        self.stages.is_empty()
    }

    /// Total worst-case latency: sum of all stage WCETs.
    ///
    /// # Lean theorem: `pipeline_additive`
    /// `0 ≤ Σ stages` when all stages are non-negative.
    pub fn total_wcet_ns(&self) -> u64 {
        self.stages.iter().map(|s| s.wcet_ns).sum()
    }

    /// Upper bound: n * max_stage_wcet.
    ///
    /// # Lean theorem: `pipeline_bounded`
    /// `Σ stages ≤ n * t_max`
    pub fn bound_ns(&self) -> u64 {
        let max_wcet = self.stages.iter().map(|s| s.wcet_ns).max().unwrap_or(0);
        (self.stages.len() as u64) * max_wcet
    }

    /// Total worst-case as Duration.
    pub fn total_wcet(&self) -> Duration {
        Duration::from_nanos(self.total_wcet_ns())
    }

    /// Total jitter: sum of per-stage jitters.
    ///
    /// # Lean theorem: `jitter_bounded`
    /// `jitter ≤ n * (t_max - t_min)`
    pub fn total_jitter_ns(&self) -> u64 {
        self.stages.iter().map(|s| s.jitter_ns()).sum()
    }

    /// Jitter upper bound: n * max_jitter.
    pub fn jitter_bound_ns(&self) -> u64 {
        let max_jitter = self.stages.iter().map(|s| s.jitter_ns()).max().unwrap_or(0);
        (self.stages.len() as u64) * max_jitter
    }

    /// Check if total WCET fits within a deadline.
    pub fn meets_deadline(&self, deadline_ns: u64) -> bool {
        self.total_wcet_ns() <= deadline_ns
    }
}

/// Batch amortization: number of rounds for N items in batches of B.
///
/// # Lean theorem: `batch_rounds`
/// `N ≤ ceil(N/B) * B`
#[inline(always)]
pub fn batch_rounds(n: u64, batch_size: u64) -> u64 {
    assert!(batch_size > 0, "batch size must be positive");
    (n + batch_size - 1) / batch_size
}

/// Cancel operation is O(1) with direct index.
///
/// # Lean theorem: `cancel_with_index_constant`
/// `ops ≤ 1`
#[inline(always)]
pub const fn cancel_cost() -> u64 {
    1
}

/// Match operation is O(k) in number of fills.
///
/// # Lean theorem: `match_linear_in_fills`
/// `ops ≤ fills`
#[inline(always)]
pub const fn match_cost(fills: u64) -> u64 {
    fills
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_pipeline() -> Pipeline {
        Pipeline::new(vec![
            Stage::new("decode", 50, 30),
            Stage::new("lookup", 100, 80),
            Stage::new("match", 200, 50),
            Stage::new("risk_check", 30, 20),
            Stage::new("send", 80, 60),
        ])
    }

    #[test]
    fn total_wcet_is_sum() {
        let p = sample_pipeline();
        assert_eq!(p.total_wcet_ns(), 50 + 100 + 200 + 30 + 80);
    }

    #[test]
    fn bound_ge_total() {
        let p = sample_pipeline();
        assert!(p.bound_ns() >= p.total_wcet_ns());
    }

    #[test]
    fn jitter_bounded() {
        let p = sample_pipeline();
        assert!(p.total_jitter_ns() <= p.jitter_bound_ns());
    }

    #[test]
    fn batch_rounds_covers_all() {
        for n in 0..=100 {
            for b in 1..=10 {
                assert!(n <= batch_rounds(n, b) * b);
            }
        }
    }

    #[test]
    fn cancel_is_o1() {
        assert_eq!(cancel_cost(), 1);
    }

    #[test]
    fn match_cost_linear() {
        assert_eq!(match_cost(5), 5);
    }

    #[test]
    fn meets_deadline() {
        let p = sample_pipeline();
        assert!(p.meets_deadline(500));
        assert!(!p.meets_deadline(400));
    }
}
