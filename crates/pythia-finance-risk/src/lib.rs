//! # pythia-finance-risk
//!
//! ADEH coherent risk measure axioms for Basel III/IV compliance.
//!
//! ## Lean specification (`Pythia.Finance.Risk.CoherentAxioms`)
//!
//! - **Monotonicity**: worse outcomes → higher risk (`monotonicity`)
//! - **Translation invariance**: rho(X+c) = rho(X) - c (`translation_invariance`)
//! - **Positive homogeneity**: rho(λX) = λ·rho(X) (`positive_homogeneity`)
//! - **Subadditivity**: rho(X+Y) ≤ rho(X) + rho(Y) (`subadditivity`)
//! - **VaR is NOT subadditive**: counterexample exists (`var_not_subadditive_witness`)
//! - **CVaR IS subadditive**: coherent risk measure (`cvar_subadditive`)

/// Result of checking coherence axioms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CoherenceCheck {
    Coherent,
    Violation(&'static str),
}

/// Check subadditivity: rho(X+Y) ≤ rho(X) + rho(Y).
///
/// # Lean: `subadditivity`
#[inline(always)]
pub fn check_subadditivity(rho_xy: f64, rho_x: f64, rho_y: f64) -> bool {
    rho_xy <= rho_x + rho_y + 1e-12
}

/// Diversification benefit: rho(X) + rho(Y) - rho(X+Y).
///
/// # Lean: `diversification_benefit`
#[inline(always)]
pub fn diversification_benefit(rho_xy: f64, rho_x: f64, rho_y: f64) -> f64 {
    rho_x + rho_y - rho_xy
}

/// Check translation invariance: rho(X+c) = rho(X) - c.
///
/// # Lean: `translation_invariance`
pub fn check_translation_invariance(rho_x: f64, rho_xc: f64, c: f64, tol: f64) -> bool {
    (rho_xc - (rho_x - c)).abs() < tol
}

/// Check positive homogeneity: rho(λX) = λ·rho(X).
///
/// # Lean: `positive_homogeneity`
pub fn check_positive_homogeneity(rho_x: f64, rho_lx: f64, lambda: f64, tol: f64) -> bool {
    (rho_lx - lambda * rho_x).abs() < tol
}

/// Risk capital: rho(L) cash makes the position acceptable.
///
/// # Lean: `risk_capital_makes_acceptable`
/// `rho(L) - rho(L) = 0`
#[inline(always)]
pub fn required_capital(rho_loss: f64) -> f64 {
    rho_loss
}

/// Demonstrate VaR non-subadditivity.
///
/// # Lean: `var_not_subadditive_witness`
pub fn var_subadditivity_violated(var_xy: f64, var_x: f64, var_y: f64) -> bool {
    var_xy > var_x + var_y + 1e-12
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subadditivity_holds() {
        assert!(check_subadditivity(8.0, 5.0, 4.0));
    }

    #[test]
    fn subadditivity_violated() {
        assert!(!check_subadditivity(10.0, 4.0, 4.0));
    }

    #[test]
    fn diversification_benefit_nonneg() {
        let benefit = diversification_benefit(8.0, 5.0, 4.0);
        assert!(benefit >= 0.0);
    }

    #[test]
    fn translation_invariance() {
        assert!(check_translation_invariance(10.0, 7.0, 3.0, 1e-10));
    }

    #[test]
    fn positive_homogeneity() {
        assert!(check_positive_homogeneity(5.0, 10.0, 2.0, 1e-10));
    }

    #[test]
    fn var_non_subadditive_example() {
        assert!(var_subadditivity_violated(12.0, 5.0, 5.0));
    }

    #[test]
    fn risk_capital_zeroes_out() {
        let rho = 1_000_000.0;
        let capital = required_capital(rho);
        assert!((capital - rho).abs() < 1e-10);
    }
}
