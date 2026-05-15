//! # pythia-finance-ftap
//!
//! First Fundamental Theorem of Asset Pricing (finite, one-period).
//!
//! ## Lean specification (`Pythia.Finance.FTAP`)
//!
//! - **Risk-neutral pricing**: `p_i = Σ_j q_j * D_ij` (`isRiskNeutralPrice`)
//! - **Portfolio pricing**: `θ·p = Σ_j q_j * (Σ_i θ_i * D_ij)` (`portfolio_pricing`)
//! - **No arbitrage**: risk-neutral measure ⟹ no free lunch (`riskNeutralImpliesNoArbitrage`)
//!
//! The deep result: any portfolio with nonneg payoff in all states and
//! nonpositive cost must have zero payoff and zero cost.

/// A finite one-period market: n assets, m states.
pub struct Market {
    pub payoffs: Vec<Vec<f64>>,
    pub prices: Vec<f64>,
}

/// A risk-neutral probability measure: strictly positive, sums to 1.
pub struct RiskNeutralMeasure {
    pub q: Vec<f64>,
}

impl RiskNeutralMeasure {
    /// Validate: all positive, sums to 1.
    pub fn is_valid(&self) -> bool {
        self.q.iter().all(|&qi| qi > 0.0)
            && (self.q.iter().sum::<f64>() - 1.0).abs() < 1e-10
    }

    /// Price an asset under the risk-neutral measure.
    ///
    /// # Lean: `isRiskNeutralPrice`
    /// `p_i = Σ_j q_j * D_ij`
    pub fn price(&self, payoffs: &[f64]) -> f64 {
        assert_eq!(self.q.len(), payoffs.len());
        self.q.iter().zip(payoffs).map(|(q, d)| q * d).sum()
    }

    /// Price a portfolio: θ·p = Σ_j q_j * (Σ_i θ_i * D_ij).
    ///
    /// # Lean: `portfolio_pricing`
    pub fn portfolio_value(&self, market: &Market, theta: &[f64]) -> f64 {
        let m = self.q.len();
        let mut total = 0.0;
        for j in 0..m {
            let payoff_j: f64 = theta.iter().enumerate()
                .map(|(i, &t)| t * market.payoffs[i][j])
                .sum();
            total += self.q[j] * payoff_j;
        }
        total
    }
}

/// Check the no-arbitrage condition: does a portfolio have nonneg payoff
/// in all states and nonpositive cost?
///
/// # Lean: `riskNeutralImpliesNoArbitrage`
/// If yes under risk-neutral pricing, cost must be exactly 0 and payoff
/// must be 0 in every state.
pub fn check_arbitrage(
    market: &Market, rnm: &RiskNeutralMeasure, theta: &[f64],
) -> ArbitrageCheck {
    let n = market.prices.len();
    let m = rnm.q.len();
    let cost: f64 = theta.iter().zip(&market.prices).map(|(t, p)| t * p).sum();
    let payoffs: Vec<f64> = (0..m)
        .map(|j| (0..n).map(|i| theta[i] * market.payoffs[i][j]).sum())
        .collect();
    let all_nonneg = payoffs.iter().all(|&p| p >= -1e-12);
    if cost <= 1e-12 && all_nonneg {
        let all_zero = payoffs.iter().all(|&p| p.abs() < 1e-10);
        if all_zero && cost.abs() < 1e-10 {
            ArbitrageCheck::NoArbitrage
        } else {
            ArbitrageCheck::PotentialArbitrage { cost, payoffs }
        }
    } else {
        ArbitrageCheck::NotApplicable
    }
}

#[derive(Debug)]
pub enum ArbitrageCheck {
    NoArbitrage,
    PotentialArbitrage { cost: f64, payoffs: Vec<f64> },
    NotApplicable,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_market() -> (Market, RiskNeutralMeasure) {
        let market = Market {
            payoffs: vec![vec![1.1, 0.9], vec![1.0, 1.0]],
            prices: vec![1.0, 0.95],
        };
        let rnm = RiskNeutralMeasure { q: vec![0.5, 0.5] };
        (market, rnm)
    }

    #[test]
    fn risk_neutral_pricing() {
        let (market, rnm) = sample_market();
        let p0 = rnm.price(&market.payoffs[0]);
        assert!((p0 - 1.0).abs() < 1e-10);
    }

    #[test]
    fn zero_portfolio_no_arbitrage() {
        let (market, rnm) = sample_market();
        let theta = vec![0.0, 0.0];
        match check_arbitrage(&market, &rnm, &theta) {
            ArbitrageCheck::NoArbitrage => {}
            _ => panic!("zero portfolio should be no-arbitrage"),
        }
    }

    #[test]
    fn valid_risk_neutral_measure() {
        let rnm = RiskNeutralMeasure { q: vec![0.3, 0.7] };
        assert!(rnm.is_valid());
    }

    #[test]
    fn invalid_measure_zero_weight() {
        let rnm = RiskNeutralMeasure { q: vec![0.0, 1.0] };
        assert!(!rnm.is_valid());
    }
}
