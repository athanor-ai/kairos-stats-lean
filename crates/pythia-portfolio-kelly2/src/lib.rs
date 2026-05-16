//! # pythia-portfolio-kelly2
//!
//! Kelly criterion with concavity proof: optimal position sizing that maximizes
//! expected log-growth rate for binary bets.
//!
//! ## Lean specification (`Pythia.Finance.KellyOptimal`)
//!
//! - **Kelly fraction**: f* = (p*(b+1) - 1) / b (`kellyFraction`)
//! - **Even odds**: f*(p, 1) = 2p - 1 (`kellyFraction_even_odds`)
//! - **Nonneg iff edge**: f* >= 0 when p*(b+1) >= 1 (`kellyFraction_nonneg`)
//! - **At most 1**: f* <= 1 when p <= 1, b > 0 (`kellyFraction_le_one`)
//! - **Zero at no edge**: f* = 0 when p*(b+1) = 1 (`kellyFraction_zero_edge`)
//! - **Monotone in p**: higher p => larger f* (`kellyFraction_mono_p`)
//! - **Half-Kelly**: f*/2 = (p*(b+1) - 1) / (2*b) (`halfKelly_is_half`)
//! - **Overbetting penalty**: (f - f*)^2 >= 0 (`overbetting_penalty_nonneg`)

/// Kelly fraction for a binary bet: f* = (p*(b+1) - 1) / b.
///
/// - `p`: win probability (should be in [0, 1])
/// - `b`: odds (payoff per unit wagered on win; must be > 0)
///
/// Returns `None` if `b` is zero or negative.
///
/// # Lean: `kellyFraction`
pub fn kelly_fraction(p: f64, b: f64) -> Option<f64> {
    if b <= 0.0 {
        return None;
    }
    Some((p * (b + 1.0) - 1.0) / b)
}

/// Half-Kelly fraction: f*/2 = (p*(b+1) - 1) / (2*b).
///
/// A common risk management heuristic that sacrifices half the expected
/// growth rate for dramatically reduced variance of outcomes.
///
/// # Lean: `halfKelly_is_half`
pub fn half_kelly(p: f64, b: f64) -> Option<f64> {
    kelly_fraction(p, b).map(|f| f / 2.0)
}

/// Overbetting penalty: (f - f*)^2.
///
/// The growth rate loss from betting `f` instead of optimal `f*` is
/// proportional to (f - f*)^2. Always nonneg.
///
/// # Lean: `overbetting_penalty_nonneg`
pub fn overbetting_penalty(f: f64, f_star: f64) -> f64 {
    (f - f_star).powi(2)
}

/// Check whether the Kelly fraction is nonneg (positive edge).
///
/// # Lean: `kellyFraction_nonneg`
pub fn has_positive_edge(p: f64, b: f64) -> bool {
    p * (b + 1.0) >= 1.0
}

/// Check whether the Kelly fraction is at most 1.
///
/// # Lean: `kellyFraction_le_one`
pub fn kelly_at_most_one(p: f64, b: f64) -> bool {
    match kelly_fraction(p, b) {
        Some(f) => f <= 1.0 + 1e-12,
        None => false,
    }
}

/// Growth rate for a binary bet: g(f) = p*ln(1 + f*b) + (1-p)*ln(1 - f).
///
/// This is the concave objective that the Kelly fraction maximizes.
/// Requires 0 < f < 1 and f*b > -1.
pub fn growth_rate(p: f64, f: f64, b: f64) -> Option<f64> {
    let win_term = 1.0 + f * b;
    let lose_term = 1.0 - f;
    if win_term <= 0.0 || lose_term <= 0.0 {
        return None;
    }
    Some(p * win_term.ln() + (1.0 - p) * lose_term.ln())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn even_odds_fair_coin() {
        // p=0.5, b=1 => f* = 2*0.5 - 1 = 0
        let f = kelly_fraction(0.5, 1.0).unwrap();
        assert!((f - 0.0).abs() < 1e-12);
    }

    #[test]
    fn even_odds_edge() {
        // p=0.6, b=1 => f* = 2*0.6 - 1 = 0.2
        let f = kelly_fraction(0.6, 1.0).unwrap();
        assert!((f - 0.2).abs() < 1e-12);
    }

    #[test]
    fn high_odds_small_edge() {
        // p=0.1, b=12 => f* = (0.1*13 - 1)/12 = 0.3/12 = 0.025
        let f = kelly_fraction(0.1, 12.0).unwrap();
        assert!((f - 0.025).abs() < 1e-12);
    }

    #[test]
    fn zero_edge_gives_zero() {
        // p*(b+1) = 1 => p = 1/(b+1). For b=3, p=0.25.
        let f = kelly_fraction(0.25, 3.0).unwrap();
        assert!(f.abs() < 1e-12);
    }

    #[test]
    fn half_kelly_is_half() {
        let f = kelly_fraction(0.6, 2.0).unwrap();
        let hf = half_kelly(0.6, 2.0).unwrap();
        assert!((hf - f / 2.0).abs() < 1e-12);
    }

    #[test]
    fn overbetting_penalty_at_optimal_is_zero() {
        let f_star = kelly_fraction(0.6, 1.0).unwrap();
        assert!(overbetting_penalty(f_star, f_star).abs() < 1e-24);
    }

    #[test]
    fn invalid_odds_returns_none() {
        assert!(kelly_fraction(0.6, 0.0).is_none());
        assert!(kelly_fraction(0.6, -1.0).is_none());
    }

    #[test]
    fn growth_rate_concavity() {
        // At the Kelly fraction, growth rate should be >= growth at nearby points.
        let p = 0.6;
        let b = 2.0;
        let f_star = kelly_fraction(p, b).unwrap();
        let g_star = growth_rate(p, f_star, b).unwrap();

        // Test at f* - 0.05 and f* + 0.05
        let g_below = growth_rate(p, f_star - 0.05, b).unwrap();
        let g_above = growth_rate(p, f_star + 0.05, b).unwrap();
        assert!(g_star >= g_below - 1e-12);
        assert!(g_star >= g_above - 1e-12);
    }
}
