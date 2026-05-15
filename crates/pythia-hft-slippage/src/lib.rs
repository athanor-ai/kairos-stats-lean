//! # pythia-hft-slippage
//!
//! Execution quality analysis with proven slippage bounds.
//!
//! ## Lean specification (`Pythia.Finance.HFT.SlippageModel`)
//!
//! - **Slippage bounded by half-spread** (`slippage_bounded_by_half_spread`)
//! - **Zero slippage at mid** (`slippage_zero_at_expected`)
//! - **Slippage additive across fills** (`slippage_sum`)
//! - **Buy impact nonneg** (`buy_impact_nonneg`)
//! - **Adverse selection nonneg** (`adverse_selection_nonneg`)

/// Slippage measurement for a single fill.
#[derive(Debug, Clone, Copy)]
pub struct Fill {
    pub actual_price: f64,
    pub expected_price: f64,
    pub qty: f64,
}

impl Fill {
    /// Slippage = actual - expected.
    ///
    /// # Lean: `slippage`
    #[inline(always)]
    pub fn slippage(&self) -> f64 {
        self.actual_price - self.expected_price
    }

    /// Slippage cost in currency terms.
    pub fn slippage_cost(&self) -> f64 {
        self.slippage() * self.qty
    }
}

/// Implementation shortfall decomposition.
#[derive(Debug, Clone, Copy)]
pub struct Shortfall {
    pub delay_cost: f64,
    pub market_impact: f64,
    pub timing_cost: f64,
}

impl Shortfall {
    /// Total cost = delay + impact + timing.
    ///
    /// # Lean: `implementation_shortfall`
    #[inline(always)]
    pub fn total(&self) -> f64 {
        self.delay_cost + self.market_impact + self.timing_cost
    }
}

/// Compute total slippage across multiple fills.
///
/// # Lean: `slippage_sum`
pub fn total_slippage(fills: &[Fill]) -> f64 {
    fills.iter().map(|f| f.slippage()).sum()
}

/// Market impact from a buy order.
///
/// # Lean: `buy_impact_nonneg`
/// `0 ≤ post_trade - pre_trade` when buy pushes price up.
pub fn buy_impact(pre_trade_price: f64, post_trade_price: f64) -> f64 {
    post_trade_price - pre_trade_price
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_slippage_at_mid() {
        let f = Fill { actual_price: 100.0, expected_price: 100.0, qty: 50.0 };
        assert_eq!(f.slippage(), 0.0);
    }

    #[test]
    fn slippage_bounded_by_spread() {
        let mid = 100.0;
        let half_spread = 0.05;
        let f = Fill { actual_price: mid + 0.03, expected_price: mid, qty: 100.0 };
        assert!(f.slippage().abs() <= half_spread);
    }

    #[test]
    fn slippage_additive() {
        let fills = vec![
            Fill { actual_price: 100.02, expected_price: 100.0, qty: 10.0 },
            Fill { actual_price: 100.01, expected_price: 100.0, qty: 20.0 },
        ];
        let total = total_slippage(&fills);
        let individual_sum: f64 = fills.iter().map(|f| f.slippage()).sum();
        assert!((total - individual_sum).abs() < 1e-10);
    }

    #[test]
    fn buy_impact_nonneg() {
        assert!(buy_impact(100.0, 100.05) >= 0.0);
    }

    #[test]
    fn shortfall_decomposition() {
        let s = Shortfall { delay_cost: 0.01, market_impact: 0.03, timing_cost: 0.005 };
        assert!((s.total() - 0.045).abs() < 1e-10);
    }
}
