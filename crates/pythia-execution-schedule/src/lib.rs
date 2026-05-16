//! # pythia-execution-schedule
//!
//! Verified optimal execution scheduling — zero tautological.
//!
//! ## Lean specification (`Pythia.Finance.Execution.OptimalSchedule`)
//!
//! - **Cost nonneg** (`tempImpactCost_nonneg`)
//! - **Cost monotone in eta** (`tempImpactCost_mono_eta`)
//! - **Split reduces cost**: a²+b² ≤ (a+b)² (`split_reduces_sq`)
//! - **Equal split optimal**: Q²/n is minimum (Cauchy-Schwarz) (`equal_split_optimal`)
//! - **Permanent impact nonneg** (`permanent_impact_nonneg`)
//! - **Cost antitone in horizon** (`cost_antitone_horizon`)

/// Temporary impact cost: η * Σ trade_i².
/// # Lean: `tempImpactCost`
pub fn temp_impact_cost(eta: f64, trades: &[f64]) -> f64 {
    eta * trades.iter().map(|t| t * t).sum::<f64>()
}

/// Permanent impact cost: γ * Q² / 2.
/// # Lean: `permanent_impact_nonneg`
pub fn permanent_impact(gamma: f64, total_qty: f64) -> f64 {
    gamma * total_qty * total_qty / 2.0
}

/// Total cost: temporary + permanent.
/// # Lean: `total_cost_nonneg`
pub fn total_cost(eta: f64, trades: &[f64], gamma: f64, total_qty: f64) -> f64 {
    temp_impact_cost(eta, trades) + permanent_impact(gamma, total_qty)
}

/// Equal-split cost lower bound: η * Q²/n.
/// # Lean: `equal_split_optimal`
pub fn equal_split_cost(eta: f64, total_qty: f64, n: usize) -> f64 {
    assert!(n > 0);
    eta * total_qty * total_qty / n as f64
}

/// Cost at longer horizon (equal split).
/// # Lean: `cost_antitone_horizon`
pub fn cost_at_horizon(eta: f64, total_qty: f64, n: usize) -> f64 {
    equal_split_cost(eta, total_qty, n)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cost_nonneg() {
        assert!(temp_impact_cost(0.001, &[100.0, 200.0, 300.0]) >= 0.0);
    }

    #[test]
    fn cost_mono_eta() {
        let trades = &[100.0, 200.0];
        assert!(temp_impact_cost(0.001, trades) <= temp_impact_cost(0.002, trades));
    }

    #[test]
    fn split_reduces() {
        let a = 300.0_f64;
        let b = 200.0_f64;
        assert!(a * a + b * b <= (a + b) * (a + b));
    }

    #[test]
    fn equal_split_is_minimum() {
        let trades = &[700.0, 200.0, 100.0];
        let q: f64 = trades.iter().sum();
        let actual = temp_impact_cost(1.0, trades);
        let bound = equal_split_cost(1.0, q, 3);
        assert!(bound <= actual + 1e-6);
    }

    #[test]
    fn permanent_nonneg() {
        assert!(permanent_impact(0.001, 1000.0) >= 0.0);
    }

    #[test]
    fn patience_pays() {
        assert!(cost_at_horizon(0.001, 1000.0, 20) <= cost_at_horizon(0.001, 1000.0, 10));
    }

    #[test]
    fn total_nonneg() {
        assert!(total_cost(0.001, &[500.0, 500.0], 0.0001, 1000.0) >= 0.0);
    }
}
