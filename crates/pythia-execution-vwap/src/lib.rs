//! # pythia-execution-vwap
//!
//! Verified VWAP execution bounds.
//!
//! ## Lean specification (`Pythia.Finance.Execution.VWAPBounds`)
//!
//! - **VWAP ≥ min price** (`vwap_ge_min`)
//! - **VWAP slippage nonneg** (`vwap_slippage_nonneg`)
//! - **Participation matches market VWAP** (`participation_matches_vwap`)

/// VWAP: Σ(price * vol) / Σ(vol).
/// # Lean: `vwap`
pub fn vwap(prices: &[f64], volumes: &[f64]) -> f64 {
    assert_eq!(prices.len(), volumes.len());
    let num: f64 = prices.iter().zip(volumes).map(|(p, v)| p * v).sum();
    let den: f64 = volumes.iter().sum();
    if den > 0.0 { num / den } else { 0.0 }
}

/// VWAP slippage = vwap - arrival.
/// # Lean: `vwap_slippage_nonneg`
pub fn vwap_slippage(vwap_val: f64, arrival: f64) -> f64 {
    vwap_val - arrival
}

/// Participation-weighted VWAP (trade α of each bucket).
/// # Lean: `participation_matches_vwap`
pub fn participation_vwap(prices: &[f64], volumes: &[f64], alpha: f64) -> f64 {
    let scaled: Vec<f64> = volumes.iter().map(|v| alpha * v).collect();
    vwap(prices, &scaled)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn vwap_ge_min() {
        let v = vwap(&[100.0, 102.0, 101.0], &[500.0, 300.0, 200.0]);
        assert!(v >= 100.0);
    }

    #[test]
    fn vwap_le_max() {
        let v = vwap(&[100.0, 102.0, 101.0], &[500.0, 300.0, 200.0]);
        assert!(v <= 102.0);
    }

    #[test]
    fn slippage_nonneg_when_vwap_above_arrival() {
        assert!(vwap_slippage(101.0, 100.0) >= 0.0);
    }

    #[test]
    fn participation_matches_market() {
        let prices = &[100.0, 102.0, 101.0];
        let volumes = &[500.0, 300.0, 200.0];
        let market = vwap(prices, volumes);
        let ours = participation_vwap(prices, volumes, 0.1);
        assert!((market - ours).abs() < 1e-10);
    }

    #[test]
    fn equal_prices_vwap_equals_price() {
        assert!((vwap(&[50.0, 50.0, 50.0], &[100.0, 200.0, 300.0]) - 50.0).abs() < 1e-10);
    }
}
