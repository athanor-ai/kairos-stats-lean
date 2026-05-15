//! Risk-neutral pricing operator.
//!
//! Lean spec: `Pythia.Finance.RiskNeutralMeasure`
//!
//! Theorems modelled:
//! - `rnPrice_add`: linearity of pricing
//! - `rnPrice_smul`: scalar homogeneity
//! - `rnPrice_mono`: dominating payoff => higher price
//! - `rnPrice_nonneg`: nonneg payoff => nonneg price
//! - `rnPrice_pos`: strict positivity under positive measure
//! - `rnPrice_zero`: zero payoff => zero price
//! - `rnPrice_eq_of_payoff_eq`: replication — equal payoffs => equal prices

/// A discrete risk-neutral pricing environment.
///
/// States are indexed 0..n, each with a probability and a discount factor.
#[derive(Debug, Clone)]
pub struct RnPricer {
    /// Risk-neutral probabilities for each state (must sum to 1, each >= 0).
    pub probabilities: Vec<f64>,
    /// Discount factor (e.g. 1/(1+r)).
    pub discount: f64,
}

impl RnPricer {
    /// Create a new pricer. Returns `None` if probabilities are invalid.
    pub fn new(probabilities: Vec<f64>, discount: f64) -> Option<Self> {
        if probabilities.is_empty() || discount <= 0.0 {
            return None;
        }
        if probabilities.iter().any(|&p| p < 0.0) {
            return None;
        }
        let sum: f64 = probabilities.iter().sum();
        if (sum - 1.0).abs() > 1e-9 {
            return None;
        }
        Some(Self { probabilities, discount })
    }

    /// Number of states.
    pub fn num_states(&self) -> usize {
        self.probabilities.len()
    }

    /// Compute risk-neutral price: discount * E_Q[payoff].
    ///
    /// Lean: `rnPrice`
    /// `payoff` must have length == `num_states`.
    pub fn price(&self, payoff: &[f64]) -> Option<f64> {
        if payoff.len() != self.num_states() {
            return None;
        }
        let expectation: f64 = self
            .probabilities
            .iter()
            .zip(payoff.iter())
            .map(|(p, x)| p * x)
            .sum();
        Some(self.discount * expectation)
    }

    /// Check whether all probabilities are strictly positive.
    pub fn is_strictly_positive(&self) -> bool {
        self.probabilities.iter().all(|&p| p > 0.0)
    }
}

/// Lean: `rnPrice_add` — price(X + Y) = price(X) + price(Y).
pub fn payoff_add(a: &[f64], b: &[f64]) -> Option<Vec<f64>> {
    if a.len() != b.len() {
        return None;
    }
    Some(a.iter().zip(b.iter()).map(|(x, y)| x + y).collect())
}

/// Lean: `rnPrice_smul` — price(c * X) = c * price(X).
pub fn payoff_smul(c: f64, a: &[f64]) -> Vec<f64> {
    a.iter().map(|x| c * x).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pricer_2state() -> RnPricer {
        // q=0.6 up, 0.4 down, discount=0.95
        RnPricer::new(vec![0.6, 0.4], 0.95).unwrap()
    }

    #[test]
    fn test_rn_price_zero() {
        // Lean: rnPrice_zero
        let p = pricer_2state();
        assert!((p.price(&[0.0, 0.0]).unwrap()).abs() < 1e-15);
    }

    #[test]
    fn test_rn_price_nonneg() {
        // Lean: rnPrice_nonneg
        let p = pricer_2state();
        assert!(p.price(&[10.0, 0.0]).unwrap() >= 0.0);
        assert!(p.price(&[0.0, 5.0]).unwrap() >= 0.0);
    }

    #[test]
    fn test_rn_price_add() {
        // Lean: rnPrice_add
        let p = pricer_2state();
        let x = [10.0, 2.0];
        let y = [3.0, 7.0];
        let xy = payoff_add(&x, &y).unwrap();
        let lhs = p.price(&xy).unwrap();
        let rhs = p.price(&x).unwrap() + p.price(&y).unwrap();
        assert!((lhs - rhs).abs() < 1e-12);
    }

    #[test]
    fn test_rn_price_smul() {
        // Lean: rnPrice_smul
        let p = pricer_2state();
        let x = [10.0, 2.0];
        let c = 3.5;
        let cx = payoff_smul(c, &x);
        let lhs = p.price(&cx).unwrap();
        let rhs = c * p.price(&x).unwrap();
        assert!((lhs - rhs).abs() < 1e-12);
    }

    #[test]
    fn test_rn_price_mono() {
        // Lean: rnPrice_mono — if X >= Y state-by-state then price(X) >= price(Y)
        let p = pricer_2state();
        let x = [10.0, 5.0];
        let y = [8.0, 3.0];
        assert!(p.price(&x).unwrap() >= p.price(&y).unwrap());
    }

    #[test]
    fn test_rn_price_pos() {
        // Lean: rnPrice_pos — strictly positive measure + strictly positive payoff => positive price
        let p = pricer_2state();
        assert!(p.is_strictly_positive());
        assert!(p.price(&[1.0, 1.0]).unwrap() > 0.0);
    }

    #[test]
    fn test_rn_price_eq_of_payoff_eq() {
        // Lean: rnPrice_eq_of_payoff_eq — replication
        let p = pricer_2state();
        let x = [7.0, 3.0];
        let y = [7.0, 3.0];
        assert!((p.price(&x).unwrap() - p.price(&y).unwrap()).abs() < 1e-15);
    }
}
