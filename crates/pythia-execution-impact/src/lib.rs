//! Square-Root Market Impact (Kyle-Obizhaeva)
//!
//! Implements the algebraic kernel from:
//! Pythia/Finance/Execution/MarketImpact.lean
//!
//! impactSq(sigma_sq, Q, V) = sigma_sq * Q / V

/// Squared market impact: sigma_sq * Q / V.
/// The actual impact is sigma * sqrt(Q/V); this is the squared form
/// for algebraic tractability.
pub fn impact_sq(sigma_sq: f64, q: f64, v: f64) -> f64 {
    sigma_sq * q / v
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Lean: impactSq_pos: strictly positive when all inputs > 0
    #[test]
    fn test_impact_sq_pos() {
        let result = impact_sq(0.04, 1000.0, 1_000_000.0);
        assert!(result > 0.0);
    }

    /// Lean: impactSq_zero_at_zero_quantity: trading zero => zero impact
    #[test]
    fn test_zero_quantity() {
        let result = impact_sq(0.04, 0.0, 1_000_000.0);
        assert!((result - 0.0).abs() < 1e-15);
    }

    /// Lean: impactSq_mono_quantity: monotone in Q
    #[test]
    fn test_mono_quantity() {
        let v = 1_000_000.0;
        let sigma_sq = 0.04;
        let i1 = impact_sq(sigma_sq, 100.0, v);
        let i2 = impact_sq(sigma_sq, 500.0, v);
        assert!(i1 <= i2);
    }

    /// Lean: impactSq_antitone_volume: antitone in V (deeper market => less impact)
    #[test]
    fn test_antitone_volume() {
        let sigma_sq = 0.04;
        let q = 1000.0;
        let i1 = impact_sq(sigma_sq, q, 500_000.0);
        let i2 = impact_sq(sigma_sq, q, 2_000_000.0);
        assert!(i1 >= i2);
    }

    /// Lean: impactSq_scale: scaling sigma_sq by c scales impact by c
    #[test]
    fn test_scale() {
        let sigma_sq = 0.04;
        let q = 1000.0;
        let v = 1_000_000.0;
        let c = 3.0;
        let base = impact_sq(sigma_sq, q, v);
        let scaled = impact_sq(c * sigma_sq, q, v);
        assert!((scaled - c * base).abs() < 1e-15);
    }

    /// Lean: impactSq_linear_quantity: impact(Q1+Q2) = impact(Q1) + impact(Q2)
    #[test]
    fn test_linear_quantity() {
        let sigma_sq = 0.04;
        let v = 1_000_000.0;
        let q1 = 300.0;
        let q2 = 700.0;
        let combined = impact_sq(sigma_sq, q1 + q2, v);
        let sum = impact_sq(sigma_sq, q1, v) + impact_sq(sigma_sq, q2, v);
        assert!((combined - sum).abs() < 1e-15);
    }
}
