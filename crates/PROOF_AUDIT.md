# Proof Audit — Lean Theorem Quality Classification

Generated 2026-05-15 by cross-review (maurice reviewing ronald's Lean specs).

Each crate's proptest properties are derived from Lean theorems. This audit
classifies whether those theorems contain real mathematical proof content
or are tautological (hypothesis restated as conclusion, `:= h`).

## Legend

- **REAL**: Non-trivial Lean proof (induction, contradiction, Cauchy-Schwarz, nlinarith on meaningful goals, etc.)
- **MIXED**: Some theorems real, some tautological
- **SCAFFOLDING**: All or most theorems are tautological (`:= h`)

## Crates with REAL proof content (proptest backed by genuine theorems)

| Crate | Key Lean proof technique |
|-------|------------------------|
| pythia-hft-fixedpoint | field_simp + nlinarith on ℚ division (mul_rescale_error) |
| pythia-hft-fixedpoint-strong | abs_add + linarith (add_error_bound), abs_mul calc chain |
| pythia-hft-checksum | generalized induction (checksum_bounded), simp [Nat.xor_assoc] |
| pythia-hft-fastmath | Mathlib norm_exp_sub_one_sub_id_le + nlinarith (exp_linear_error) |
| pythia-hft-latency | Nat.div_add_mod + omega (batch_rounds) |
| pythia-hft-riskgate | *(pre-existing, sorry-free before this session)* |
| pythia-hft-orderbook | *(pre-existing, sorry-free before this session)* |
| pythia-finance-ftap | Finset.add_sum_erase + mul_pos + by_contra (riskNeutralImpliesNoArbitrage) |
| pythia-finance-execution | Cauchy-Schwarz via sum_mul_sq_le_sq_mul_sq (twapIsOptimal) |
| pythia-finance-rnpricing | sum_add_distrib (linearity), Finset.sum + mul_pos (strict positivity) |
| pythia-finance-portfolio | field_simp + ring (FOC), nlinarith [sq_nonneg] (diversification) |
| pythia-options-parity | split_ifs + linarith (put_call_payoff_identity) |
| pythia-options-blackscholes | mul_le_of_le_one_right (deep ITM positivity) |
| pythia-options-hedging | mul_nonneg + sq_nonneg chains (gammaPnL_nonneg, vol_arb_profit) |
| pythia-stochastic-gbm | Real.exp_pos (positivity), log_exp (log return), exp_le_exp (monotonicity) |
| pythia-stochastic-heston | mul_neg_of_neg_of_pos (mean reversion direction) |
| pythia-stochastic-ou | ring (at_mean), simp [exp_zero] (boundary) |
| pythia-credit-cds | mul_nonneg (spread nonneg), field_simp (break_even) |
| pythia-credit-hazard | exp_le_exp + neg_le_neg (survivalProb_antitone) |
| pythia-fixedincome-yield | div_nonneg + le_div_iff (discrete_forward_nonneg) |
| pythia-risk-es | mul_le_mul_of_nonneg_left (ES dominates VaR) |
| pythia-risk-var | ring (pos homogeneity, translation — algebraic identities) |
| pythia-execution-vwap | le_div_iff + Finset.sum_le_sum (vwap_ge_min) |
| pythia-execution-split | Cauchy-Schwarz (equal_split_optimal), nlinarith [sq_nonneg] (split_reduces) |

## Crates with MIXED content (some real, some tautological)

| Crate | Real theorems | Tautological theorems |
|-------|--------------|----------------------|
| pythia-hft-marketmaking | spread_profit_nonneg (mul_nonneg), inventory_skew_direction (linarith) | — |
| pythia-hft-signal | combinedSignal_bounded (calc chain with Finset.sum_le_sum) | — |
| pythia-hft-position | within_limit (abs_le) | net_position_additive (rfl) |
| pythia-hft-session | all `by decide` — real but trivial | — |
| pythia-options-volpnl | daily_gamma_pnl_pos (mul_nonneg chain), cumulative (sum_nonneg) | theta_gamma_offset (:= h) |
| pythia-stochastic-regime | stationary_dist_sum (div_add_div_same), expected_duration_pos | transition_row_sum (:= h), high_vol_regime_riskier (:= h) |
| pythia-stochastic-mc | mc_se_antitone (div_le_div), antithetic_reduces (linarith) | mc_in_ci (:= h), quadruple_halves_se (rfl) |
| pythia-portfolio-riskbudget | contribution_le_total (Finset.single_le_sum), equal_risk (nsmul) | euler_sum (:= h), mcr_nonneg (:= h) |
| pythia-portfolio-leverage | gross_ge_abs_net (Finset.abs_sum_le_sum_abs), leverage_within_limit (div_le_iff) | net_leverage_identity (:= h) |
| pythia-risk-margin | margin_ratio_decreases logic, liquidation_qty_nonneg (div_nonneg) | equity_identity (:= h) |
| pythia-risk-correlation | uncorrelated_reduces_var (le_add_of_nonneg_right), negative_corr (linarith) | correlation_symmetric (:= h) |
| pythia-fundamentals-dcf | pv_antitone_rate/time (exp_le_exp), pv_additive (ring) | irr_zero_npv (:= h) |
| pythia-credit-cva | cva_nonneg (mul_nonneg + sum_nonneg), cva_mono_lgd (mul_le_mul) | netting_reduces (:= h), wrong_way_risk (:= h) |
| pythia-fixedincome-swap | par_swap_zero_value (linarith), payer_antitone (linarith + mul_le_mul) | swap_dv01_nonneg (:= h) |
| pythia-credit-recovery | lgd_antitone (linarith), expected_loss_le_pd (mul_le_of_le_one_right) | seniority_improves (:= h) |
| pythia-risk-vol | ewma_nonneg (add_nonneg + mul_nonneg), garch_unconditional_pos (div_pos) | garch_stationarity_condition (:= h) |
| pythia-portfolio-factor | systematic_risk_nonneg (sum_nonneg + sq_nonneg), tracking_error (linarith) | return_attribution (:= h), risk_decomposition (:= h), market_neutral (:= h) |
| pythia-execution-twap | participation_rate_bounded (div_le_iff), schedule_completes (nsmul + mul_div_cancel) | — |

## Crates with SCAFFOLDING only (all tautological, proptest exercises impl but not backed by proofs)

| Crate | Notes |
|-------|-------|
| pythia-finance-risk | CoherentAxioms — all ADEH axioms are `:= h` (modeling assumptions, not provable properties) |
| pythia-finance-backtest | overfit_prob_mono (:= h), min_track_record (:= h) — deflation_adjustment_nonneg is real (sqrt_nonneg) |
| pythia-options-greeks | Most `:= h` except delta_parity (linarith) and greeks_pde_check (linarith) |
| pythia-options-volsurface | Most `:= h` except total_variance_nonneg (mul_nonneg + sq_nonneg) and var_swap_strike_nonneg (sum_nonneg) |
| pythia-options-exotic | All `:= h` except straddle_nonneg (add_nonneg) |
| pythia-options-american | All `:= h` except early_exercise_premium_nonneg (linarith) and put_early_exercise_value (linarith) |
| pythia-options-noarb | *(needs detailed check — has real Finset reasoning in some theorems)* |
| pythia-options-impliedvol | All `:= h` (existence/uniqueness stated as hypotheses) |
| pythia-hft-auction | Most `:= h` except buyer/seller_surplus_nonneg (linarith) |
| pythia-hft-fairvalue | microPrice_between (le_div_iff + nlinarith) — REAL; ewma_between (linarith) — REAL |
| pythia-hft-slippage | slippage_sum (sum_sub_distrib) — REAL; rest mostly `:= h` |
| pythia-portfolio-construction | *(needs detailed check)* |
| pythia-portfolio-attribution | *(needs detailed check)* |
| pythia-portfolio-sharpe | *(needs detailed check)* |
| pythia-portfolio-sortino | *(needs detailed check)* |
| pythia-portfolio-tca | *(needs detailed check)* |
| pythia-risk-drawdown | *(needs detailed check)* |
| pythia-risk-stress | worst_case_bounded logic REAL; rest `:= h` |
| pythia-risk-liquidity | lvar_ge_var (le_add_of_nonneg_right) REAL; liquidity_cost_mono (mul_le_mul) REAL |
| pythia-fundamentals-capital | tax_shield logic likely real; *(needs detailed check)* |
| pythia-portfolio-kelly | *(needs detailed check)* |
| pythia-options-parity-div | *(needs detailed check)* |
| pythia-execution-router | *(needs detailed check — routing_preserves is := h)* |

---

## Summary

- **24 crates** with genuine mathematical proof content (proptest truly backed by Lean)
- **18 crates** with mixed content (some real, some tautological)  
- **22 crates** need detailed review or are primarily scaffolding

The 24 real-proof crates are the demo-ready showcase. The mixed crates are partially verified. The scaffolding crates exercise the Rust implementation (useful as tests) but are not formally verified.
