//! # pythia-execution-router
//!
//! Verified smart order routing for best execution.
//!
//! ## Lean specification (`Pythia.Finance.Execution.SmartOrderRouter`)
//!
//! - **Best price selection** (`best_price_le_all`)
//! - **Price improvement nonneg** (`price_improvement_nonneg`)
//! - **Routing preserves quantity** (`routing_preserves_qty`)
//! - **WAFP between best and worst** (`wafp_between`)

/// A venue with price and available quantity.
#[derive(Debug, Clone, Copy)]
pub struct Venue {
    pub price: f64,
    pub available: f64,
    pub fee: f64,
}

impl Venue {
    pub fn total_cost(&self) -> f64 { self.price + self.fee }
}

/// Find the best venue (lowest total cost for buys).
/// # Lean: `best_price_le_all`
pub fn best_venue(venues: &[Venue]) -> Option<usize> {
    venues.iter().enumerate().min_by(|(_, a), (_, b)|
        a.total_cost().partial_cmp(&b.total_cost()).unwrap()
    ).map(|(i, _)| i)
}

/// Price improvement: NBBO - fill price.
/// # Lean: `price_improvement_nonneg`
pub fn price_improvement(nbbo: f64, fill_price: f64) -> f64 {
    nbbo - fill_price
}

/// WAFP across fills.
/// # Lean: `wafp_between`
pub fn wafp(fills: &[(f64, f64)]) -> f64 {
    let num: f64 = fills.iter().map(|(p, q)| p * q).sum();
    let den: f64 = fills.iter().map(|(_, q)| q).sum();
    if den > 0.0 { num / den } else { 0.0 }
}

/// Check routing preserves quantity.
/// # Lean: `routing_preserves_qty`
pub fn check_qty_preserved(fills: &[f64], total: f64, tol: f64) -> bool {
    (fills.iter().sum::<f64>() - total).abs() < tol
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn best_venue_cheapest() {
        let venues = vec![
            Venue { price: 100.05, available: 500.0, fee: 0.001 },
            Venue { price: 100.02, available: 300.0, fee: 0.001 },
            Venue { price: 100.08, available: 200.0, fee: 0.000 },
        ];
        assert_eq!(best_venue(&venues), Some(1));
    }

    #[test]
    fn price_improvement_nonneg() {
        assert!(price_improvement(100.05, 100.02) >= 0.0);
    }

    #[test]
    fn qty_preserved() {
        assert!(check_qty_preserved(&[300.0, 200.0, 500.0], 1000.0, 1e-10));
    }

    #[test]
    fn wafp_between_prices() {
        let fills = vec![(100.0, 500.0), (101.0, 300.0), (100.5, 200.0)];
        let w = wafp(&fills);
        assert!(w >= 100.0 && w <= 101.0);
    }

    #[test]
    fn fee_matters() {
        let cheap_price_high_fee = Venue { price: 100.00, available: 100.0, fee: 0.05 };
        let mid_price_low_fee = Venue { price: 100.03, available: 100.0, fee: 0.001 };
        assert!(mid_price_low_fee.total_cost() < cheap_price_high_fee.total_cost());
    }
}
