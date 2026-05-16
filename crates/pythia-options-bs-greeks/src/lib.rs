//! # pythia-options-bs-greeks
//!
//! Black-Scholes Greeks (abstract-CDF form) — verified via Lean proofs.
//!
//! ## Lean specification (`Pythia.Finance.Options.BlackScholesGreeks`)
//!
//! - **Delta bounded**: `0 <= delta <= 1` under CDF axioms (`bsDelta_bounded`)
//! - **Gamma nonneg**: `0 <= gamma` for S,sigma,T > 0 (`bsGamma_nonneg`)
//! - **Vega nonneg**: `0 <= vega` for S,T >= 0 (`bsVega_nonneg`)
//! - **Rho nonneg**: `0 <= rho` for K,T >= 0 (`bsRho_nonneg`)

use std::f64::consts::PI;

/// Standard normal CDF (approximation via error function).
#[inline(always)]
pub fn normal_cdf(x: f64) -> f64 {
    0.5 * (1.0 + erf(x / std::f64::consts::SQRT_2))
}

/// Standard normal PDF.
#[inline(always)]
pub fn normal_pdf(x: f64) -> f64 {
    (-0.5 * x * x).exp() / (2.0 * PI).sqrt()
}

/// Error function approximation (Abramowitz & Stegun 7.1.26).
fn erf(x: f64) -> f64 {
    let sign = x.signum();
    let x = x.abs();
    let t = 1.0 / (1.0 + 0.3275911 * x);
    let poly = t * (0.254829592
        + t * (-0.284496736
            + t * (1.421413741
                + t * (-1.453152027 + t * 1.061405429))));
    sign * (1.0 - poly * (-x * x).exp())
}

/// Black-Scholes d1: `(ln(S/K) + (r + sigma^2/2)*T) / (sigma*sqrt(T))`.
/// # Lean: `bsD1`
#[inline(always)]
pub fn bs_d1(s: f64, k: f64, t: f64, r: f64, sigma: f64) -> f64 {
    ((s / k).ln() + (r + sigma * sigma / 2.0) * t) / (sigma * t.sqrt())
}

/// Black-Scholes d2: `d1 - sigma*sqrt(T)`.
/// # Lean: `bsD2`
#[inline(always)]
pub fn bs_d2(s: f64, k: f64, t: f64, r: f64, sigma: f64) -> f64 {
    bs_d1(s, k, t, r, sigma) - sigma * t.sqrt()
}

/// Black-Scholes call price: `S*Phi(d1) - K*exp(-r*T)*Phi(d2)`.
/// # Lean: `bsCallPrice`
#[inline(always)]
pub fn bs_call_price(s: f64, k: f64, t: f64, r: f64, sigma: f64) -> f64 {
    s * normal_cdf(bs_d1(s, k, t, r, sigma))
        - k * (-r * t).exp() * normal_cdf(bs_d2(s, k, t, r, sigma))
}

/// Black-Scholes delta: `Phi(d1)`.
/// # Lean: `bsDelta`
#[inline(always)]
pub fn bs_delta(s: f64, k: f64, t: f64, r: f64, sigma: f64) -> f64 {
    normal_cdf(bs_d1(s, k, t, r, sigma))
}

/// Black-Scholes gamma: `phi(d1) / (S * sigma * sqrt(T))`.
/// # Lean: `bsGamma`
#[inline(always)]
pub fn bs_gamma(s: f64, k: f64, t: f64, r: f64, sigma: f64) -> f64 {
    normal_pdf(bs_d1(s, k, t, r, sigma)) / (s * sigma * t.sqrt())
}

/// Black-Scholes vega: `S * phi(d1) * sqrt(T)`.
/// # Lean: `bsVega`
#[inline(always)]
pub fn bs_vega(s: f64, k: f64, t: f64, r: f64, sigma: f64) -> f64 {
    s * normal_pdf(bs_d1(s, k, t, r, sigma)) * t.sqrt()
}

/// Black-Scholes rho: `K * T * exp(-r*T) * Phi(d2)`.
/// # Lean: `bsRho`
#[inline(always)]
pub fn bs_rho(s: f64, k: f64, t: f64, r: f64, sigma: f64) -> f64 {
    k * t * (-r * t).exp() * normal_cdf(bs_d2(s, k, t, r, sigma))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn delta_bounded_atm() {
        let d = bs_delta(100.0, 100.0, 1.0, 0.05, 0.2);
        assert!(d >= 0.0 && d <= 1.0);
    }

    #[test]
    fn delta_bounded_deep_itm() {
        let d = bs_delta(200.0, 100.0, 1.0, 0.05, 0.2);
        assert!(d >= 0.0 && d <= 1.0);
        assert!(d > 0.95); // deep ITM delta near 1
    }

    #[test]
    fn gamma_nonneg() {
        let g = bs_gamma(100.0, 100.0, 1.0, 0.05, 0.2);
        assert!(g >= 0.0);
    }

    #[test]
    fn vega_nonneg() {
        let v = bs_vega(100.0, 100.0, 1.0, 0.05, 0.2);
        assert!(v >= 0.0);
    }

    #[test]
    fn rho_nonneg() {
        let rho = bs_rho(100.0, 100.0, 1.0, 0.05, 0.2);
        assert!(rho >= 0.0);
    }

    #[test]
    fn call_price_positive_atm() {
        let c = bs_call_price(100.0, 100.0, 1.0, 0.05, 0.2);
        assert!(c > 0.0);
        // Sanity: ATM call with 20% vol, 1yr, should be ~10
        assert!(c > 5.0 && c < 20.0);
    }
}
