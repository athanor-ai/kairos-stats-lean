//! # pythia-portfolio-treynor
//!
//! Verified Treynor ratio (systematic-risk-adjusted excess return) properties.
//!
//! ## Lean specification (`Pythia.Finance.Portfolio.TreynorRatio`)
//!
//! - **Zero-excess**: `treynorRatio_zero_excess` — T(rf, rf, beta) = 0
//! - **Linear in r_p**: `treynorRatio_linear_rp` — shift by dr shifts T by dr/beta
//! - **Translation invariance**: `treynorRatio_translation` — same shift on r_p and r_f cancels

/// Treynor ratio: (r_p - r_f) / beta.
///
/// # Lean: `treynorRatio`
#[inline(always)]
pub fn treynor_ratio(rp: f64, rf: f64, beta: f64) -> f64 {
    (rp - rf) / beta
}

/// Zero-excess specialisation: when r_p = r_f, T = 0.
///
/// # Lean: `treynorRatio_zero_excess`
#[inline(always)]
pub fn treynor_ratio_zero_excess(rf: f64, beta: f64) -> f64 {
    treynor_ratio(rf, rf, beta)
}

/// Linearity: T(rp + dr, rf, beta) = T(rp, rf, beta) + dr/beta.
///
/// # Lean: `treynorRatio_linear_rp`
#[inline(always)]
pub fn treynor_ratio_shifted(rp: f64, dr: f64, rf: f64, beta: f64) -> f64 {
    treynor_ratio(rp + dr, rf, beta)
}

/// Translation invariance: T(rp + c, rf + c, beta) = T(rp, rf, beta).
///
/// # Lean: `treynorRatio_translation`
#[inline(always)]
pub fn treynor_ratio_translated(rp: f64, rf: f64, c: f64, beta: f64) -> f64 {
    treynor_ratio(rp + c, rf + c, beta)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EPS: f64 = 1e-12;

    /// Basic computation test
    #[test]
    fn test_basic_computation() {
        let result = treynor_ratio(0.12, 0.03, 1.2);
        let expected = (0.12 - 0.03) / 1.2;
        assert!((result - expected).abs() < EPS);
    }

    /// Lean: `treynorRatio_zero_excess` — at r_p = r_f the ratio is zero
    #[test]
    fn test_zero_excess() {
        let result = treynor_ratio_zero_excess(0.05, 1.5);
        assert!(result.abs() < EPS);
    }

    /// Lean: `treynorRatio_linear_rp` — shifting r_p by dr shifts T by dr/beta
    #[test]
    fn test_linearity() {
        let rp = 0.10;
        let rf = 0.03;
        let beta = 1.2;
        let dr = 0.02;
        let base = treynor_ratio(rp, rf, beta);
        let shifted = treynor_ratio_shifted(rp, dr, rf, beta);
        let expected = base + dr / beta;
        assert!((shifted - expected).abs() < EPS);
    }

    /// Lean: `treynorRatio_translation` — equal shift cancels
    #[test]
    fn test_translation_invariance() {
        let rp = 0.10;
        let rf = 0.03;
        let beta = 0.8;
        let c = 0.05;
        let base = treynor_ratio(rp, rf, beta);
        let translated = treynor_ratio_translated(rp, rf, c, beta);
        assert!((base - translated).abs() < EPS);
    }

    /// Negative beta produces negative ratio for positive excess
    #[test]
    fn test_negative_beta() {
        let result = treynor_ratio(0.10, 0.03, -1.0);
        assert!(result < 0.0);
    }

    /// High beta dilutes the ratio
    #[test]
    fn test_high_beta_dilution() {
        let low_beta = treynor_ratio(0.10, 0.03, 0.5);
        let high_beta = treynor_ratio(0.10, 0.03, 2.0);
        assert!(low_beta > high_beta);
    }
}
