//! # pythia-fundamentals-npv
//!
//! Verified net present value under continuous compounding.
//!
//! ## Lean specification (`Pythia.Finance.Fundamentals.NetPresentValue`)
//!
//! - **Zero cashflow**: NPV of all-zero stream = 0
//! - **Linearity**: NPV(alpha * cf, t, r) = alpha * NPV(cf, t, r)
//! - **Additivity**: NPV(cf1 + cf2, t, r) = NPV(cf1, t, r) + NPV(cf2, t, r)
//! - **Rate antitonicity**: higher r -> lower NPV (for nonneg cf, nonneg t)

/// Net present value of a cashflow stream under continuous compounding.
///
/// `NPV = sum_i cf[i] * exp(-r * t[i])`
///
/// # Lean: `netPresentValue`
pub fn net_present_value(cf: &[f64], t: &[f64], r: f64) -> f64 {
    assert_eq!(cf.len(), t.len());
    cf.iter()
        .zip(t.iter())
        .map(|(&c, &ti)| c * (-r * ti).exp())
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn zero_cashflow_gives_zero_npv() {
        let cf = [0.0, 0.0, 0.0];
        let t = [1.0, 2.0, 3.0];
        assert_eq!(net_present_value(&cf, &t, 0.05), 0.0);
    }

    #[test]
    fn linearity_scalar() {
        let cf = [100.0, 200.0, 150.0];
        let t = [1.0, 2.0, 3.0];
        let r = 0.05;
        let alpha = 3.0;
        let scaled_cf: Vec<f64> = cf.iter().map(|&c| alpha * c).collect();
        let npv_base = net_present_value(&cf, &t, r);
        let npv_scaled = net_present_value(&scaled_cf, &t, r);
        assert!((npv_scaled - alpha * npv_base).abs() < 1e-10);
    }

    #[test]
    fn additivity() {
        let cf1 = [100.0, 200.0];
        let cf2 = [50.0, 75.0];
        let t = [1.0, 2.0];
        let r = 0.05;
        let combined: Vec<f64> = cf1.iter().zip(cf2.iter()).map(|(&a, &b)| a + b).collect();
        let npv1 = net_present_value(&cf1, &t, r);
        let npv2 = net_present_value(&cf2, &t, r);
        let npv_combined = net_present_value(&combined, &t, r);
        assert!((npv_combined - (npv1 + npv2)).abs() < 1e-10);
    }

    #[test]
    fn rate_antitonicity() {
        let cf = [100.0, 100.0, 100.0];
        let t = [1.0, 2.0, 3.0];
        let npv_low = net_present_value(&cf, &t, 0.03);
        let npv_high = net_present_value(&cf, &t, 0.10);
        assert!(npv_high <= npv_low);
    }

    #[test]
    fn zero_rate_gives_sum_of_cashflows() {
        let cf = [100.0, 200.0, 300.0];
        let t = [1.0, 2.0, 3.0];
        let npv = net_present_value(&cf, &t, 0.0);
        let sum: f64 = cf.iter().sum();
        assert!((npv - sum).abs() < 1e-12);
    }

    #[test]
    fn single_cashflow_matches_discounting() {
        let fv = 1000.0;
        let time = 5.0;
        let r = 0.08;
        let npv = net_present_value(&[fv], &[time], r);
        let expected = fv * (-r * time).exp();
        assert!((npv - expected).abs() < 1e-12);
    }
}
