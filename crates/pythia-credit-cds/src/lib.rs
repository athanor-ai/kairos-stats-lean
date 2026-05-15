//! # pythia-credit-cds
//!
//! Verified CDS pricing under constant hazard rate model.
//!
//! ## Lean specification (`Pythia.Finance.CreditDefaultSwap`)
//!
//! - **Spread nonneg**: s = λ(1-R) ≥ 0 (`spread_hazard_recovery`)
//! - **Spread monotone in recovery**: higher R → lower spread (`spread_recovery_monotone`)
//! - **Survival probability positive**: Q(t) = exp(-λt) > 0 (`survival_prob_pos`)
//! - **Default probability bounded**: P(def) ≤ 1 (`default_prob_bound`)
//! - **Break-even**: s = (1-R)*default_leg/risky_annuity (`break_even`)

/// CDS under constant hazard rate model.
#[derive(Debug, Clone, Copy)]
pub struct CDS {
    pub hazard_rate: f64,
    pub recovery: f64,
}

impl CDS {
    pub fn new(hazard_rate: f64, recovery: f64) -> Self {
        assert!(hazard_rate >= 0.0);
        assert!((0.0..=1.0).contains(&recovery));
        Self { hazard_rate, recovery }
    }

    /// CDS spread approximation: s = λ(1-R).
    ///
    /// # Lean: `spread_hazard_recovery`
    #[inline(always)]
    pub fn spread(&self) -> f64 {
        self.hazard_rate * (1.0 - self.recovery)
    }

    /// Survival probability at time t: exp(-λt).
    ///
    /// # Lean: `survival_prob_pos`
    #[inline(always)]
    pub fn survival_prob(&self, t: f64) -> f64 {
        (-self.hazard_rate * t).exp()
    }

    /// Default probability by time t: 1 - exp(-λt).
    ///
    /// # Lean: `default_prob_bound`
    #[inline(always)]
    pub fn default_prob(&self, t: f64) -> f64 {
        1.0 - self.survival_prob(t)
    }

    /// Break-even spread from protection and premium legs.
    ///
    /// # Lean: `break_even`
    pub fn break_even_spread(&self, default_leg: f64, risky_annuity: f64) -> f64 {
        assert!(risky_annuity > 0.0);
        (1.0 - self.recovery) * default_leg / risky_annuity
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spread_nonneg() {
        let cds = CDS::new(0.02, 0.4);
        assert!(cds.spread() >= 0.0);
    }

    #[test]
    fn spread_monotone_recovery() {
        let low_r = CDS::new(0.02, 0.3);
        let high_r = CDS::new(0.02, 0.6);
        assert!(high_r.spread() <= low_r.spread());
    }

    #[test]
    fn survival_positive() {
        let cds = CDS::new(0.05, 0.4);
        assert!(cds.survival_prob(5.0) > 0.0);
    }

    #[test]
    fn default_prob_bounded() {
        let cds = CDS::new(0.05, 0.4);
        let p = cds.default_prob(10.0);
        assert!(p <= 1.0);
        assert!(p >= 0.0);
    }

    #[test]
    fn break_even() {
        let cds = CDS::new(0.02, 0.4);
        let be = cds.break_even_spread(0.05, 4.0);
        assert!(be >= 0.0);
    }
}
