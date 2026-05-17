//! # pythia-fundamentals-gordon
//!
//! Verified Gordon growth model (constant-dividend-growth equity valuation).
//!
//! ## Lean specification (`Pythia.Finance.Fundamentals.GordonGrowth`)
//!
//! - **Zero-growth specialisation**: g=0 => P = D1/r (`gordonGrowthPrice_zero_growth`)
//! - **Linear in dividend** (`gordonGrowthPrice_linear_D`)
//! - **Scale-invariance in dividend** (`gordonGrowthPrice_scale_D`)

/// Gordon growth equity price: D1 / (r - g).
///
/// Requires r > g for convergence.
///
/// # Lean: `gordonGrowthPrice`
#[inline(always)]
pub fn gordon_price(d1: f64, r: f64, g: f64) -> f64 {
    d1 / (r - g)
}

/// Dividend yield implied by Gordon model: D1 / P = r - g.
pub fn implied_dividend_yield(r: f64, g: f64) -> f64 {
    r - g
}

/// Price/earnings ratio implied by Gordon model with payout ratio p:
/// P/E = p / (r - g).
pub fn implied_pe_ratio(payout_ratio: f64, r: f64, g: f64) -> f64 {
    payout_ratio / (r - g)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_growth_is_perpetuity() {
        let d1 = 5.0;
        let r = 0.10;
        let price = gordon_price(d1, r, 0.0);
        assert!((price - d1 / r).abs() < 1e-10);
    }

    #[test]
    fn linear_in_dividend() {
        let d1 = 3.0;
        let dd = 2.0;
        let r = 0.12;
        let g = 0.04;
        let combined = gordon_price(d1 + dd, r, g);
        let separate = gordon_price(d1, r, g) + dd / (r - g);
        assert!((combined - separate).abs() < 1e-10);
    }

    #[test]
    fn scale_invariance() {
        let d1 = 4.0;
        let alpha = 2.5;
        let r = 0.10;
        let g = 0.03;
        let scaled = gordon_price(alpha * d1, r, g);
        let expected = alpha * gordon_price(d1, r, g);
        assert!((scaled - expected).abs() < 1e-10);
    }

    #[test]
    fn price_positive_when_valid() {
        // d1 > 0, r > g => price > 0
        assert!(gordon_price(5.0, 0.10, 0.03) > 0.0);
    }

    #[test]
    fn higher_growth_higher_price() {
        let d1 = 4.0;
        let r = 0.12;
        assert!(gordon_price(d1, r, 0.05) < gordon_price(d1, r, 0.08));
    }

    #[test]
    fn implied_yield_consistent() {
        let r = 0.10;
        let g = 0.03;
        let d1 = 5.0;
        let price = gordon_price(d1, r, g);
        let yield_from_price = d1 / price;
        assert!((yield_from_price - implied_dividend_yield(r, g)).abs() < 1e-10);
    }
}
