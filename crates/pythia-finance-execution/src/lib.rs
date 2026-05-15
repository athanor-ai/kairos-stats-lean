//! # pythia-finance-execution
//!
//! Almgren-Chriss optimal execution with proven TWAP optimality.
//!
//! ## Lean specification (`Pythia.Finance.AlmgrenChrissOptimal`)
//!
//! - **TWAP completes order**: `Σ (Q/n) = Q` (`twapSchedule_sum`)
//! - **TWAP cost formula**: `η * Q²/n` (`twap_temporaryCost`)
//! - **Cauchy-Schwarz**: `Q² ≤ n * Σ x_i²` (`sum_sq_ge_sq_sum_div`)
//! - **TWAP is optimal**: any schedule costs ≥ TWAP cost (`twapIsOptimal`)

/// An execution schedule: trades across n periods.
#[derive(Debug, Clone)]
pub struct Schedule {
    pub trades: Vec<f64>,
}

impl Schedule {
    /// TWAP schedule: trade Q/n in each of n periods.
    ///
    /// # Lean: `twapSchedule`
    pub fn twap(total_qty: f64, n_periods: usize) -> Self {
        assert!(n_periods > 0);
        let per_period = total_qty / n_periods as f64;
        Self { trades: vec![per_period; n_periods] }
    }

    /// Total quantity traded.
    pub fn total_qty(&self) -> f64 {
        self.trades.iter().sum()
    }

    /// Number of periods.
    pub fn n_periods(&self) -> usize {
        self.trades.len()
    }

    /// Sum of squared trades (the quantity TWAP minimizes).
    pub fn sum_of_squares(&self) -> f64 {
        self.trades.iter().map(|t| t * t).sum()
    }

    /// Temporary impact cost: η * Σ x_i².
    ///
    /// # Lean: `temporaryCost`
    pub fn temporary_cost(&self, eta: f64) -> f64 {
        eta * self.sum_of_squares()
    }

    /// TWAP cost for the same total quantity.
    ///
    /// # Lean: `twap_temporaryCost`
    /// `η * Q²/n`
    pub fn twap_cost_lower_bound(&self, eta: f64) -> f64 {
        let q = self.total_qty();
        eta * q * q / self.n_periods() as f64
    }

    /// Check TWAP optimality: actual cost ≥ TWAP lower bound.
    ///
    /// # Lean: `twapIsOptimal`
    pub fn is_at_least_twap_cost(&self, eta: f64) -> bool {
        self.temporary_cost(eta) >= self.twap_cost_lower_bound(eta) - 1e-10
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn twap_completes_order() {
        let s = Schedule::twap(1000.0, 10);
        assert!((s.total_qty() - 1000.0).abs() < 1e-10);
    }

    #[test]
    fn twap_cost_formula() {
        let s = Schedule::twap(1000.0, 10);
        let eta = 0.001;
        let expected = eta * 1000.0 * 1000.0 / 10.0;
        assert!((s.temporary_cost(eta) - expected).abs() < 1e-6);
    }

    #[test]
    fn twap_is_optimal() {
        let eta = 0.001;
        let aggressive = Schedule { trades: vec![500.0, 300.0, 200.0] };
        assert!(aggressive.temporary_cost(eta) >= aggressive.twap_cost_lower_bound(eta) - 1e-10);
    }

    #[test]
    fn front_loaded_costs_more() {
        let eta = 0.001;
        let twap = Schedule::twap(1000.0, 4);
        let front = Schedule { trades: vec![700.0, 200.0, 50.0, 50.0] };
        assert!(front.temporary_cost(eta) > twap.temporary_cost(eta));
    }
}
