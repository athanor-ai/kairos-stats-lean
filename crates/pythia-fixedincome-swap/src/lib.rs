//! # pythia-fixedincome-swap
//!
//! Verified interest rate swap pricing.
//!
//! ## Lean specification (`Pythia.Finance.FixedIncome.SwapPricing`)
//!
//! - **Fixed leg nonneg** (`fixed_leg_nonneg`)
//! - **Floating leg = 1 - D(Tn), bounded** (`floating_leg_bounded`)
//! - **Par swap rate → zero NPV** (`par_swap_zero_value`)
//! - **Payer antitone in rate** (`payer_antitone_rate`)
//! - **DV01 nonneg** (`swap_dv01_nonneg`)

/// IRS fixed leg PV: c * Σ D(Ti) * δi.
/// # Lean: `fixed_leg_nonneg`
pub fn fixed_leg_pv(coupon: f64, disc_deltas: &[f64]) -> f64 {
    coupon * disc_deltas.iter().sum::<f64>()
}

/// IRS floating leg PV: 1 - D(Tn).
/// # Lean: `floating_leg_bounded`
pub fn floating_leg_pv(d_tn: f64) -> f64 {
    1.0 - d_tn
}

/// Par swap rate: c* = (1 - D(Tn)) / annuity.
/// # Lean: `par_swap_zero_value`
pub fn par_rate(d_tn: f64, annuity: f64) -> f64 {
    assert!(annuity > 0.0);
    (1.0 - d_tn) / annuity
}

/// Payer swap value: PV_float - c * annuity.
/// # Lean: `payer_antitone_rate`
pub fn payer_value(pv_float: f64, coupon: f64, annuity: f64) -> f64 {
    pv_float - coupon * annuity
}

/// Receiver swap value: c * annuity - PV_float.
/// # Lean: `receiver_swap_value`
pub fn receiver_value(pv_float: f64, coupon: f64, annuity: f64) -> f64 {
    coupon * annuity - pv_float
}

/// DV01 ≈ annuity (value change per 1bp rate move).
/// # Lean: `swap_dv01_nonneg`
pub fn dv01(annuity: f64) -> f64 {
    annuity * 0.0001
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_leg_nonneg() {
        assert!(fixed_leg_pv(0.03, &[0.95, 0.90, 0.85]) >= 0.0);
    }

    #[test]
    fn floating_bounded() {
        let fl = floating_leg_pv(0.90);
        assert!(fl >= 0.0 && fl <= 1.0);
    }

    #[test]
    fn par_rate_zeroes_npv() {
        let d_tn = 0.85;
        let annuity = 2.7;
        let c = par_rate(d_tn, annuity);
        let pv_fix = c * annuity;
        let pv_flt = 1.0 - d_tn;
        assert!((pv_fix - pv_flt).abs() < 1e-10);
    }

    #[test]
    fn payer_receiver_opposite() {
        let pv = payer_value(0.15, 0.03, 2.7);
        let rv = receiver_value(0.15, 0.03, 2.7);
        assert!((pv + rv).abs() < 1e-10);
    }

    #[test]
    fn payer_antitone() {
        let annuity = 2.7;
        let pv_float = 0.15;
        assert!(payer_value(pv_float, 0.04, annuity) <= payer_value(pv_float, 0.03, annuity));
    }

    #[test]
    fn dv01_nonneg() {
        assert!(dv01(2.7) >= 0.0);
    }
}
