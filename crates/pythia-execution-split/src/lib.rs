//! # pythia-execution-split
//!
//! Verified optimal order splitting.
//!
//! ## Lean specification (`Pythia.Finance.Execution.OptimalSplit`)
//!
//! - **Equal split optimal**: Q²/n ≤ Σ child² (Cauchy-Schwarz) (`equal_split_optimal`)
//! - **Split reduces impact**: n1²+n2² ≤ N² (`split_reduces_impact`)
//! - **Hidden quantity nonneg** (iceberg) (`hidden_nonneg`)

/// Sum of squared child orders (impact proxy).
pub fn sum_of_squares(children: &[f64]) -> f64 {
    children.iter().map(|c| c * c).sum()
}

/// Optimal (equal) split: each child = Q/n.
pub fn equal_split(total: f64, n: usize) -> Vec<f64> {
    assert!(n > 0);
    vec![total / n as f64; n]
}

/// Lower bound on sum of squares: Q²/n (achieved by equal split).
/// # Lean: `equal_split_optimal`
pub fn impact_lower_bound(total: f64, n: usize) -> f64 {
    total * total / n as f64
}

/// Check that splitting reduces impact: sum_sq(children) ≤ total².
/// # Lean: `split_reduces_impact`
pub fn split_reduces_impact(children: &[f64], total: f64) -> bool {
    sum_of_squares(children) <= total * total + 1e-10
}

/// Iceberg order: display ≤ total, hidden = total - display.
/// # Lean: `hidden_nonneg`
pub fn iceberg_hidden(total: f64, display: f64) -> f64 {
    assert!(display <= total + 1e-12);
    total - display
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_split_achieves_bound() {
        let children = equal_split(1000.0, 5);
        let ss = sum_of_squares(&children);
        let bound = impact_lower_bound(1000.0, 5);
        assert!((ss - bound).abs() < 1e-6);
    }

    #[test]
    fn split_reduces() {
        assert!(split_reduces_impact(&[500.0, 500.0], 1000.0));
    }

    #[test]
    fn unequal_above_bound() {
        let ss = sum_of_squares(&[700.0, 300.0]);
        let bound = impact_lower_bound(1000.0, 2);
        assert!(ss >= bound - 1e-6);
    }

    #[test]
    fn iceberg_hidden_nonneg() {
        assert!(iceberg_hidden(1000.0, 100.0) >= 0.0);
    }

    #[test]
    fn more_splits_less_impact() {
        let ss2 = sum_of_squares(&equal_split(1000.0, 2));
        let ss10 = sum_of_squares(&equal_split(1000.0, 10));
        assert!(ss10 < ss2);
    }
}
