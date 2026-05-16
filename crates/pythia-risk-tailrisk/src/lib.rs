//! # pythia-risk-tailrisk
//!
//! Tail risk Euler decomposition for Expected Shortfall (ES).
//!
//! ## Lean specification (`Pythia.Finance.Risk.TailRiskDecomp`)
//!
//! - **Euler decomposition**: contributions sum to total ES (`esDecomp_sum_eq_total`)
//! - **Contribution bounded**: each contrib <= total under nonneg (`esContrib_le_total`)
//! - **Contrib nonneg under PSD**: w >= 0, margES >= 0 => contrib >= 0 (`esContrib_nonneg_of_psd`)
//! - **Scaling**: scale weights by c scales ES by c (`esDecomp_scale`)
//! - **Fractions sum to 1**: contrib_i / ES_total sums to 1 (`esContrib_frac_sum_one`)
//! - **Zero weights**: all zero weights => ES = 0 (`esDecomp_zero_weights`)
//! - **Single asset**: single-asset contribution equals total (`esDecomp_single_asset`)
//! - **Total nonneg under PSD**: all contribs nonneg => total nonneg (`esDecomp_nonneg_of_psd`)

/// Total portfolio ES as the sum of component contributions.
///
/// # Lean: `esTotal`
pub fn es_total(contrib: &[f64]) -> f64 {
    contrib.iter().sum()
}

/// Component ES contribution: weight * marginal ES.
///
/// # Lean: `esContrib`
pub fn es_contrib(w: f64, marginal_es: f64) -> f64 {
    w * marginal_es
}

/// Portfolio ES via Euler decomposition: sum_i (w_i * marginalES_i).
///
/// # Lean: `esDecomp`
pub fn es_decomp(w: &[f64], marginal_es: &[f64]) -> f64 {
    assert_eq!(w.len(), marginal_es.len(), "weight and marginal ES vectors must have same length");
    w.iter().zip(marginal_es.iter()).map(|(wi, mi)| wi * mi).sum()
}

/// Component contributions from weights and marginal ES vectors.
///
/// Returns a vector where contrib_i = w_i * marginalES_i.
pub fn es_contributions(w: &[f64], marginal_es: &[f64]) -> Vec<f64> {
    assert_eq!(w.len(), marginal_es.len());
    w.iter().zip(marginal_es.iter()).map(|(wi, mi)| wi * mi).collect()
}

/// Fractional contribution: contrib_i / es_total.
///
/// Returns None if total ES is zero or negative.
///
/// # Lean: `esContrib_frac_sum_one`
pub fn es_frac_contributions(contrib: &[f64]) -> Option<Vec<f64>> {
    let total = es_total(contrib);
    if total <= 0.0 {
        return None;
    }
    Some(contrib.iter().map(|c| c / total).collect())
}

/// Check if each contribution is bounded by total (under nonneg assumption).
///
/// # Lean: `esContrib_le_total`
pub fn contrib_bounded_by_total(contrib: &[f64]) -> bool {
    if contrib.iter().any(|c| *c < 0.0) {
        return false; // precondition violated
    }
    let total = es_total(contrib);
    contrib.iter().all(|c| *c <= total + 1e-12)
}

/// Scale all weights by a constant and return new decomposed ES.
///
/// # Lean: `esDecomp_scale`
pub fn es_decomp_scaled(c: f64, w: &[f64], marginal_es: &[f64]) -> f64 {
    c * es_decomp(w, marginal_es)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn euler_decomp_sums_to_total() {
        // Lean: `esDecomp_sum_eq_total`
        let w = vec![0.3, 0.5, 0.2];
        let marginal_es = vec![0.05, 0.08, 0.03];
        let contrib = es_contributions(&w, &marginal_es);
        let total_from_contrib = es_total(&contrib);
        let total_from_decomp = es_decomp(&w, &marginal_es);
        assert!((total_from_contrib - total_from_decomp).abs() < 1e-12);
    }

    #[test]
    fn contrib_le_total_nonneg() {
        // Lean: `esContrib_le_total`
        let contrib = vec![0.015, 0.040, 0.006];
        assert!(contrib_bounded_by_total(&contrib));
    }

    #[test]
    fn contrib_nonneg_of_psd() {
        // Lean: `esContrib_nonneg_of_psd`
        let w = 0.4;
        let marginal = 0.06;
        assert!(es_contrib(w, marginal) >= 0.0);
    }

    #[test]
    fn scaling_property() {
        // Lean: `esDecomp_scale`
        let w = vec![0.3, 0.5, 0.2];
        let marginal_es = vec![0.05, 0.08, 0.03];
        let c = 2.5;
        let scaled_w: Vec<f64> = w.iter().map(|wi| c * wi).collect();
        let es_scaled = es_decomp(&scaled_w, &marginal_es);
        let es_original = es_decomp(&w, &marginal_es);
        assert!((es_scaled - c * es_original).abs() < 1e-12);
    }

    #[test]
    fn frac_contributions_sum_to_one() {
        // Lean: `esContrib_frac_sum_one`
        let contrib = vec![0.015, 0.040, 0.006];
        let fracs = es_frac_contributions(&contrib).unwrap();
        let sum: f64 = fracs.iter().sum();
        assert!((sum - 1.0).abs() < 1e-12);
    }

    #[test]
    fn zero_weights_give_zero_es() {
        // Lean: `esDecomp_zero_weights`
        let w = vec![0.0, 0.0, 0.0];
        let marginal_es = vec![0.05, 0.08, 0.03];
        let es = es_decomp(&w, &marginal_es);
        assert!(es.abs() < 1e-12);
    }

    #[test]
    fn single_asset_contrib_equals_total() {
        // Lean: `esDecomp_single_asset`
        let w = vec![0.0, 0.0, 0.7, 0.0];
        let marginal_es = vec![0.05, 0.08, 0.10, 0.03];
        let es = es_decomp(&w, &marginal_es);
        assert!((es - 0.7 * 0.10).abs() < 1e-12);
    }
}
