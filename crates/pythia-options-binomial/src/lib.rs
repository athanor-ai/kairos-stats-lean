//! Cox-Ross-Rubinstein One-Step Binomial Option Pricing
//!
//! Implements the algebraic kernel from:
//! Pythia/Finance/Options/CRRBinomialStep.lean
//!
//! V0 = exp(-r*dt) * (q * Vu + (1 - q) * Vd)
//! q  = (exp(r*dt) - d) / (u - d)

/// CRR one-step option price: discounted risk-neutral expectation.
///   crrStepPrice(r, dt, q, vu, vd) = exp(-r*dt) * (q*vu + (1-q)*vd)
pub fn crr_step_price(r: f64, dt: f64, q: f64, vu: f64, vd: f64) -> f64 {
    (-r * dt).exp() * (q * vu + (1.0 - q) * vd)
}

/// CRR risk-neutral up-probability:
///   q = (exp(r*dt) - d) / (u - d)
pub fn crr_risk_neutral_prob(r: f64, dt: f64, u: f64, d: f64) -> f64 {
    ((r * dt).exp() - d) / (u - d)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: crrStepPrice_equal_payoffs: Vu = Vd = V => price = exp(-r*dt)*V
    #[test]
    fn test_equal_payoffs() {
        let r = 0.05;
        let dt = 0.25;
        let q = 0.6;
        let v = 10.0;
        let price = crr_step_price(r, dt, q, v, v);
        let expected = (-r * dt).exp() * v;
        assert!((price - expected).abs() < 1e-12);
    }

    /// Lean: crrStepPrice_zero_rate: at r=0, price = q*Vu + (1-q)*Vd
    #[test]
    fn test_zero_rate() {
        let q = 0.55;
        let vu = 12.0;
        let vd = 8.0;
        let price = crr_step_price(0.0, 1.0, q, vu, vd);
        let expected = q * vu + (1.0 - q) * vd;
        assert!((price - expected).abs() < 1e-12);
    }

    /// Lean: crrStepPrice_linear_payoff: scaling payoffs by alpha scales price by alpha
    #[test]
    fn test_linear_payoff() {
        let r = 0.03;
        let dt = 0.5;
        let q = 0.5;
        let vu = 15.0;
        let vd = 5.0;
        let alpha = 3.0;
        let price_base = crr_step_price(r, dt, q, vu, vd);
        let price_scaled = crr_step_price(r, dt, q, alpha * vu, alpha * vd);
        assert!((price_scaled - alpha * price_base).abs() < 1e-12);
    }

    /// Lean: crrRiskNeutralProb_zero_rate: at r=0, q = (1-d)/(u-d)
    #[test]
    fn test_risk_neutral_prob_zero_rate() {
        let u = 1.2;
        let d = 0.8;
        let q = crr_risk_neutral_prob(0.0, 1.0, u, d);
        let expected = (1.0 - d) / (u - d);
        assert!((q - expected).abs() < 1e-12);
    }

    /// Lean: crrRiskNeutralProb_nonneg: q >= 0 under no-arb condition d <= exp(r*dt)
    #[test]
    fn test_risk_neutral_prob_nonneg() {
        let r = 0.05;
        let dt = 1.0;
        let u = 1.3;
        let d = 0.9; // d < exp(0.05) ~ 1.051
        let q = crr_risk_neutral_prob(r, dt, u, d);
        assert!(q >= 0.0);
    }

    /// Lean: crrRiskNeutralProb_le_one: q <= 1 under no-arb condition exp(r*dt) <= u
    #[test]
    fn test_risk_neutral_prob_le_one() {
        let r = 0.05;
        let dt = 1.0;
        let u = 1.3; // exp(0.05) ~ 1.051 <= 1.3
        let d = 0.9;
        let q = crr_risk_neutral_prob(r, dt, u, d);
        assert!(q <= 1.0);
    }
}
