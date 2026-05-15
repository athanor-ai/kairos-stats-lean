//! # pythia-stochastic-regime
//!
//! Verified Markov regime switching model.
//!
//! ## Lean specification (`Pythia.Finance.Stochastic.RegimeDetection`)
//!
//! - **Stationary dist positive** (`stationary_dist_pos`)
//! - **Stationary dist sums to 1** (`stationary_dist_sum`)
//! - **Expected duration positive** (`expected_duration_pos`)
//! - **Regime-weighted variance nonneg** (`regime_weighted_var_nonneg`)

/// 2-state Markov regime model.
#[derive(Debug, Clone, Copy)]
pub struct RegimeModel {
    pub p12: f64,
    pub p21: f64,
}

impl RegimeModel {
    pub fn new(p12: f64, p21: f64) -> Self {
        assert!(p12 > 0.0 && p12 <= 1.0);
        assert!(p21 > 0.0 && p21 <= 1.0);
        Self { p12, p21 }
    }

    /// Stationary probability of regime 1: p21/(p12+p21).
    /// # Lean: `stationary_dist_pos`
    pub fn pi1(&self) -> f64 { self.p21 / (self.p12 + self.p21) }

    /// Stationary probability of regime 2: p12/(p12+p21).
    pub fn pi2(&self) -> f64 { self.p12 / (self.p12 + self.p21) }

    /// Expected duration in regime 1: 1/p12.
    /// # Lean: `expected_duration_pos`
    pub fn duration1(&self) -> f64 { 1.0 / self.p12 }

    /// Expected duration in regime 2: 1/p21.
    pub fn duration2(&self) -> f64 { 1.0 / self.p21 }

    /// Regime-weighted variance: π1*v1 + π2*v2.
    /// # Lean: `regime_weighted_var_nonneg`
    pub fn weighted_variance(&self, var1: f64, var2: f64) -> f64 {
        self.pi1() * var1 + self.pi2() * var2
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stationary_sums_to_one() {
        let m = RegimeModel::new(0.1, 0.2);
        assert!((m.pi1() + m.pi2() - 1.0).abs() < 1e-10);
    }

    #[test]
    fn stationary_positive() {
        let m = RegimeModel::new(0.1, 0.2);
        assert!(m.pi1() > 0.0);
        assert!(m.pi2() > 0.0);
    }

    #[test]
    fn duration_positive() {
        let m = RegimeModel::new(0.1, 0.2);
        assert!(m.duration1() > 0.0);
        assert!(m.duration2() > 0.0);
    }

    #[test]
    fn weighted_var_nonneg() {
        let m = RegimeModel::new(0.1, 0.2);
        assert!(m.weighted_variance(0.01, 0.04) >= 0.0);
    }

    #[test]
    fn higher_persistence_longer_duration() {
        let fast = RegimeModel::new(0.3, 0.2);
        let slow = RegimeModel::new(0.05, 0.2);
        assert!(slow.duration1() > fast.duration1());
    }
}
