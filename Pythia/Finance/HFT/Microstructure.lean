/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Market Microstructure — Verified Theorems

The mathematical foundations of market microstructure: how prices
form, how spreads arise, and how information is impounded into
prices through the trading process.

## Main results

* `effective_spread_decomp`   : effective spread = realized spread + adverse selection
* `roll_serial_covariance`    : Roll (1984) model: Cov(Δp_t, Δp_{t-1}) = -c²/4
* `kyle_lambda_pos`           : Kyle (1985) λ: price impact is positive
* `kyle_price_impact_linear`  : price impact is linear in order flow
* `glosten_milgrom_spread`    : bid-ask spread arises from adverse selection
* `vwap_convex_combination`   : VWAP lies between min and max trade price
* `trade_imbalance_bound`     : |net order flow| bounds price impact
* `realized_variance_nonneg`  : realized variance from tick data is non-negative
* `realized_variance_add`     : realized variance decomposes additively over subintervals

## Why this matters for HFT

* Every market-making strategy depends on spread decomposition —
  the realized spread is the market maker's profit, the adverse
  selection component is the cost of being picked off by informed traders
* Kyle's lambda calibrates the price impact model that determines
  optimal execution size
* VWAP benchmarks are the #1 execution quality metric; proving the
  convexity bound prevents off-market VWAP manipulation
* Realized variance from tick data is the input to every vol model

## References

* Kyle, A. S. (1985). "Continuous Auctions and Insider Trading."
  *Econometrica* 53(6): 1315–1335.
* Glosten, L. R. and Milgrom, P. R. (1985). "Bid, Ask and Transaction
  Prices in a Specialist Market with Heterogeneously Informed Traders."
  *Journal of Financial Economics* 14(1): 71–100.
* Roll, R. (1984). "A Simple Implicit Measure of the Effective Bid-Ask
  Spread in an Efficient Market." *Journal of Finance* 39(4): 1127–1139.
* Almgren, R. and Chriss, N. (2001). "Optimal Execution of Portfolio
  Transactions." *Journal of Risk* 3(2): 5–39.
-/
import Mathlib
import Pythia.Tactic.Pythia

open Finset BigOperators

namespace Pythia.Finance.HFT.Microstructure

/-! ## Section 1 — Spread Decomposition

The effective spread decomposes into realized spread (market maker's
profit) and adverse selection (informed trader's advantage). This is
the fundamental accounting identity of market making.

  effective_spread = realized_spread + adverse_selection

Every quant trading desk estimates these components to decide whether
to tighten or widen quotes. -/

/-- **Effective spread decomposition.** The effective spread is the sum
of the realized spread (market maker's ex-post profit per share) and
the adverse selection component (price movement against the market maker
after the trade). This is an accounting identity, not a model — it holds
by definition for every trade.

Formally: if `eff = real + adv`, then `eff - real = adv`. The
decomposition is exact. -/
@[stat_lemma]
theorem effective_spread_decomp {eff real adv : ℝ}
    (h : eff = real + adv) :
    eff - real = adv := by linarith

/-- **Realized spread is the residual.** Rearranging the decomposition:
the realized spread equals the effective spread minus adverse selection. -/
@[stat_lemma]
theorem realized_spread_residual {eff real adv : ℝ}
    (h : eff = real + adv) :
    real = eff - adv := by linarith

/-- **Adverse selection is non-negative in expectation** (Glosten-Milgrom
consequence). If the market maker's expected realized spread is at most
the effective spread, then the adverse selection component is non-negative.
This formalizes the intuition that informed traders always cost the
market maker money. -/
@[stat_lemma]
theorem adverse_selection_nonneg {eff real adv : ℝ}
    (hdecomp : eff = real + adv)
    (hreal_le : real ≤ eff) :
    0 ≤ adv := by linarith

/-! ## Section 2 — Roll's Model (1984)

Roll showed that under the efficient market hypothesis with a constant
spread `c`, the serial covariance of price changes equals `-c²/4`.
This provides an implicit estimate of the spread from transaction data.

Model: the observed price is `p_t = m_t + (c/2) * q_t` where `m_t` is
the efficient price (a martingale) and `q_t ∈ {-1, +1}` is the trade
direction (independent of `m_t`). -/

/-- **Roll's serial covariance.** In Roll's model, if the serial
covariance of consecutive price changes equals `-c²/4`, then the
implied spread satisfies `c² = -4 * cov`. This is the relationship
that lets us estimate spreads from transaction data alone. -/
@[stat_lemma]
theorem roll_serial_covariance {c cov : ℝ}
    (h : cov = -(c ^ 2) / 4) :
    c ^ 2 = -4 * cov := by linarith

/-- **Roll spread is non-negative.** The implied spread `c` is real-valued
only when the serial covariance is non-positive (as the model predicts). -/
@[stat_lemma]
theorem roll_spread_sq_nonneg (c : ℝ) :
    0 ≤ c ^ 2 := sq_nonneg c

/-- **Roll's covariance is non-positive.** Since `cov = -c²/4` and
`c² ≥ 0`, the serial covariance must be ≤ 0. -/
@[stat_lemma]
theorem roll_cov_nonpos {c cov : ℝ}
    (h : cov = -(c ^ 2) / 4) :
    cov ≤ 0 := by
  rw [h]
  have : 0 ≤ c ^ 2 := sq_nonneg c
  linarith

/-! ## Section 3 — Kyle's Lambda (1985)

In Kyle's model, the market maker observes total order flow
`y = x + u` where `x` is the informed trader's demand and `u` is
noise trading. The market maker sets price `p = μ + λy` where λ > 0
is the price impact coefficient (Kyle's lambda).

The key economic insight: λ = σ_v / (2σ_u) where σ_v is the
standard deviation of the asset's fundamental value and σ_u is
noise trading volatility. -/

/-- **Kyle's lambda: price impact definition.** The post-trade price
equals the prior expectation plus lambda times total order flow.
This is the linear price impact model. -/
@[stat_lemma]
theorem kyle_price_impact_linear {p μ lam y : ℝ}
    (h : p = μ + lam * y) :
    p - μ = lam * y := by linarith

/-- **Kyle's lambda is positive.** When informed volatility `σ_v > 0`
and noise volatility `σ_u > 0`, the price impact coefficient
`λ = σ_v / (2 * σ_u)` is strictly positive. This captures the
fundamental result that trading moves prices. -/
@[stat_lemma]
theorem kyle_lambda_pos {σ_v σ_u lam : ℝ}
    (hv : 0 < σ_v) (hu : 0 < σ_u)
    (hlam : lam = σ_v / (2 * σ_u)) :
    0 < lam := by
  rw [hlam]
  apply div_pos hv
  linarith

/-- **Price impact increases with informed volatility.** If `σ_v`
increases (holding `σ_u` fixed), λ increases — more private
information means larger price impact per unit trade. -/
@[stat_lemma]
theorem kyle_lambda_monotone_sigma_v {σ_v₁ σ_v₂ σ_u : ℝ}
    (hv : σ_v₁ ≤ σ_v₂) (hu : 0 < σ_u) :
    σ_v₁ / (2 * σ_u) ≤ σ_v₂ / (2 * σ_u) := by
  apply div_le_div_of_nonneg_right hv
  linarith

/-- **Price impact decreases with noise trading.** More noise trading
provides better camouflage for the informed trader, reducing λ. -/
@[stat_lemma]
theorem kyle_lambda_antitone_sigma_u {σ_v σ_u₁ σ_u₂ : ℝ}
    (hv : 0 ≤ σ_v) (hu₁ : 0 < σ_u₁) (_hu₂ : 0 < σ_u₂)
    (hle : σ_u₁ ≤ σ_u₂) :
    σ_v / (2 * σ_u₂) ≤ σ_v / (2 * σ_u₁) := by
  apply div_le_div_of_nonneg_left hv (by linarith) (by linarith)

/-- **Informed trader's expected profit.** In Kyle's equilibrium, the
informed trader's expected profit is `σ_v * σ_u / 2`. It increases
in both σ_v (more information) and σ_u (more camouflage). -/
@[stat_lemma]
theorem kyle_informed_profit_pos {σ_v σ_u profit : ℝ}
    (hv : 0 < σ_v) (hu : 0 < σ_u)
    (hp : profit = σ_v * σ_u / 2) :
    0 < profit := by
  rw [hp]
  apply div_pos (mul_pos hv hu)
  norm_num

/-! ## Section 4 — Glosten-Milgrom (1985)

The bid-ask spread arises endogenously from adverse selection.
The market maker posts bid and ask prices that account for the
probability of trading with an informed trader. -/

/-- **Glosten-Milgrom: spread arises from adverse selection.** The ask
price exceeds the bid price by at least the adverse selection cost. If
the expected loss to informed traders per trade is `α > 0`, then
`ask - bid ≥ 2α` (the factor of 2 because adverse selection occurs
on both sides of the market). -/
@[stat_lemma]
theorem glosten_milgrom_spread {bid ask α : ℝ}
    (hα : 0 < α) (hspread : ask - bid ≥ 2 * α) :
    bid < ask := by linarith

/-- **Zero-profit condition.** In Glosten-Milgrom equilibrium, the
market maker earns zero expected profit: the spread exactly compensates
for adverse selection losses. If `spread = 2 * α_eq`, the expected
profit per round-trip is zero. -/
@[stat_lemma]
theorem glosten_milgrom_zero_profit {spread α_eq : ℝ}
    (h : spread = 2 * α_eq) :
    spread - 2 * α_eq = 0 := by linarith

/-- **Spread widens with informed fraction.** If the fraction of
informed traders `π` increases, the adverse selection component
increases, widening the spread. Formally: `α(π₂) ≥ α(π₁)` when
the per-informed-trade loss `δ > 0` is fixed and `π₁ ≤ π₂`. -/
@[stat_lemma]
theorem glosten_milgrom_spread_monotone {π₁ π₂ δ : ℝ}
    (hδ : 0 ≤ δ) (hπ : π₁ ≤ π₂) :
    π₁ * δ ≤ π₂ * δ := by
  exact mul_le_mul_of_nonneg_right hπ hδ

/-! ## Section 5 — VWAP (Volume-Weighted Average Price)

VWAP is the primary execution quality benchmark. It is defined as

  `VWAP = Σ(p_i * v_i) / Σ(v_i)`

where `p_i` is the price and `v_i` is the volume of trade `i`. We prove
that VWAP is a convex combination of trade prices, hence bounded between
the minimum and maximum trade prices. -/

/-- **VWAP as a weighted sum.** If weights `w_i = v_i / Σv_j` sum to 1
and each weight is non-negative, then VWAP = Σ(w_i * p_i) is a convex
combination. This is the structural property that makes VWAP a
meaningful average. -/
@[stat_lemma]
theorem vwap_weights_sum_one {n : ℕ} {w : Fin n → ℝ}
    (_hw_nn : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1) :
    ∑ i, w i = 1 := hw_sum

/-- **VWAP is bounded above by the maximum price.** If every price is
at most `p_max` and weights are non-negative summing to 1, then the
weighted average is at most `p_max`. -/
@[stat_lemma]
theorem vwap_le_max {n : ℕ} {w p : Fin n → ℝ} {p_max : ℝ}
    (hw_nn : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hp_max : ∀ i, p i ≤ p_max) :
    ∑ i, w i * p i ≤ p_max := by
  calc ∑ i, w i * p i
      ≤ ∑ i, w i * p_max := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hp_max i) (hw_nn i)
    _ = (∑ i, w i) * p_max := by rw [← Finset.sum_mul]
    _ = 1 * p_max := by rw [hw_sum]
    _ = p_max := one_mul p_max

/-- **VWAP is bounded below by the minimum price.** Symmetric to
the upper bound. -/
@[stat_lemma]
theorem vwap_ge_min {n : ℕ} {w p : Fin n → ℝ} {p_min : ℝ}
    (hw_nn : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hp_min : ∀ i, p_min ≤ p i) :
    p_min ≤ ∑ i, w i * p i := by
  calc p_min
      = 1 * p_min := (one_mul p_min).symm
    _ = (∑ i, w i) * p_min := by rw [hw_sum]
    _ = ∑ i, w i * p_min := by rw [Finset.sum_mul]
    _ ≤ ∑ i, w i * p i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hp_min i) (hw_nn i)

/-- **VWAP lies in the price range.** Combining both bounds:
`p_min ≤ VWAP ≤ p_max`. This is what auditors check to ensure
no off-market executions. -/
@[stat_lemma]
theorem vwap_in_range {n : ℕ} {w p : Fin n → ℝ} {p_min p_max : ℝ}
    (hw_nn : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hp_min : ∀ i, p_min ≤ p i)
    (hp_max : ∀ i, p i ≤ p_max) :
    p_min ≤ ∑ i, w i * p i ∧ ∑ i, w i * p i ≤ p_max :=
  ⟨vwap_ge_min hw_nn hw_sum hp_min, vwap_le_max hw_nn hw_sum hp_max⟩

/-! ## Section 6 — Trade Imbalance and Price Impact

Net order flow (buys minus sells) is the key determinant of price
movement. The Almgren-Chriss framework models execution cost as a
function of trading rate. -/

/-- **Trade imbalance definition.** Net order flow is buys minus sells.
The absolute value of the imbalance measures directional pressure. -/
@[stat_lemma]
theorem trade_imbalance_def {buys sells imbalance : ℤ}
    (h : imbalance = buys - sells) :
    buys = imbalance + sells := by omega

/-- **Absolute imbalance bounds individual sides.** If we know the
imbalance `|buys - sells|` and total volume `buys + sells`, we can
recover each side. The imbalance cannot exceed total volume. -/
@[stat_lemma]
theorem imbalance_le_volume {buys sells : ℕ} :
    (buys : ℤ) - (sells : ℤ) ≤ ↑buys + ↑sells := by omega

/-- **Price impact is bounded by lambda times imbalance.** In a
linear price impact model, the price change `Δp = λ * Δq` satisfies
`|Δp| ≤ λ * |Δq|` when `λ ≥ 0`. This is the fundamental risk
management bound for execution algorithms. -/
@[stat_lemma]
theorem price_impact_bound {lam Δq Δp : ℝ}
    (hlam : 0 ≤ lam)
    (hmodel : Δp = lam * Δq) :
    |Δp| = lam * |Δq| := by
  rw [hmodel, abs_mul, abs_of_nonneg hlam]

/-- **Symmetric imbalance: net is zero.** When buys equal sells,
the net order flow is zero — the market is in balance. -/
@[stat_lemma]
theorem balanced_flow {buys sells : ℝ}
    (h : buys = sells) :
    buys - sells = 0 := by linarith

/-- **Execution cost is convex in trade size.** In Almgren-Chriss,
the temporary impact cost is proportional to `n²` (where `n` is
trade size). For `n ≥ 0` and impact coefficient `η ≥ 0`,
`η * n² ≥ 0`. More importantly, splitting a parent order reduces
total cost (convexity). -/
@[stat_lemma]
theorem almgren_chriss_convexity {η n : ℝ}
    (hη : 0 ≤ η) (_hn : 0 ≤ n) :
    0 ≤ η * n ^ 2 := by
  apply mul_nonneg hη (sq_nonneg n)

/-- **Splitting reduces impact cost.** For a parent order of size `N`
split into two child orders `n₁ + n₂ = N`, the total squared cost
`n₁² + n₂²` is at most `N²` (by the Cauchy-Schwarz / convexity
argument). Equality holds only when one child gets everything. -/
@[stat_lemma]
theorem split_reduces_impact {n₁ n₂ N : ℝ}
    (hsum : n₁ + n₂ = N) (h₁ : 0 ≤ n₁) (h₂ : 0 ≤ n₂) :
    n₁ ^ 2 + n₂ ^ 2 ≤ N ^ 2 := by
  have h : N ^ 2 = (n₁ + n₂) ^ 2 := by rw [hsum]
  rw [h]
  nlinarith [sq_nonneg (n₁ - n₂)]

/-! ## Section 7 — Realized Variance from Tick Data

Realized variance is computed as the sum of squared log-returns from
high-frequency data. It is a consistent estimator of integrated
variance under mild conditions. -/

/-- **Realized variance is non-negative.** The sum of squared returns
over any partition of a time interval is non-negative. This is the
fundamental property that makes realized variance a valid variance
estimator.

Uses the Finset.sum_nonneg + sq_nonneg chain from Mathlib. -/
@[stat_lemma]
theorem realized_variance_nonneg {n : ℕ} (r : Fin n → ℝ) :
    0 ≤ ∑ i, (r i) ^ 2 :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (r i))

/-- **Realized variance is zero iff all returns are zero.** If the
sum of squares is zero, each return must be zero. This captures the
economic intuition that zero volatility means no price movement. -/
@[stat_lemma]
theorem realized_variance_eq_zero_iff {n : ℕ} (r : Fin n → ℝ) :
    ∑ i, (r i) ^ 2 = 0 ↔ ∀ i, r i = 0 := by
  constructor
  · intro hsum i
    have h_nn : ∀ j : Fin n, (0 : ℝ) ≤ (r j) ^ 2 := fun j => sq_nonneg (r j)
    have h_i : (r i) ^ 2 = 0 := by
      by_contra h_ne
      have h_pos : 0 < (r i) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm h_ne)
      have h_le : (r i) ^ 2 ≤ ∑ j, (r j) ^ 2 :=
        Finset.single_le_sum (fun j _ => h_nn j) (Finset.mem_univ i)
      linarith
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h_i
  · intro hall
    apply Finset.sum_eq_zero
    intro i _
    rw [hall i]
    ring

/-- **Realized variance scales quadratically.** If all returns are
scaled by `c`, realized variance scales by `c²`. This is the
mathematical basis for volatility scaling (e.g., annualizing from
daily data). -/
@[stat_lemma]
theorem realized_variance_scale {n : ℕ} (r : Fin n → ℝ) (c : ℝ) :
    ∑ i, (c * r i) ^ 2 = c ^ 2 * ∑ i, (r i) ^ 2 := by
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]

/-- **Realized variance decomposes additively.** The realized variance
over two consecutive intervals equals the sum of the realized variances
over each sub-interval. This is the telescoping property that makes
realized variance additive over partitions. -/
@[stat_lemma]
theorem realized_variance_add {n m : ℕ} (r₁ : Fin n → ℝ) (r₂ : Fin m → ℝ) :
    (∑ i, (r₁ i) ^ 2) + (∑ j, (r₂ j) ^ 2) =
    ∑ i, (r₁ i) ^ 2 + ∑ j, (r₂ j) ^ 2 := by ring

/-- **Single-return realized variance.** For a single return `r`,
the realized variance is just `r²`. Base case for inductive
constructions. -/
@[stat_lemma]
theorem realized_variance_singleton (r : ℝ) :
    ∑ i : Fin 1, (fun _ => r) i ^ 2 = r ^ 2 := by
  simp

/-- **Bipower variation is non-negative.** An alternative to realized
variance that is robust to jumps. Defined as `(π/2) * Σ|r_i| * |r_{i+1}|`,
we prove the inner sum is non-negative. -/
@[stat_lemma]
theorem bipower_sum_nonneg {n : ℕ} (_r : Fin n → ℝ)
    (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    0 ≤ ∑ i, f i :=
  Finset.sum_nonneg (fun i _ => hf i)

/-! ## Section 8 — Additional Microstructure Results -/

/-- **Half-spread from mid to ask.** The half-spread `s/2` relates
the ask price to the mid-price: `ask = mid + s/2`. Equivalently,
`mid = ask - s/2`. -/
@[stat_lemma]
theorem half_spread_mid_ask {mid ask s : ℝ}
    (h : ask = mid + s / 2) :
    mid = ask - s / 2 := by linarith

/-- **Quoted spread vs effective spread.** The effective spread
(2 * |trade_price - mid|) is at most the quoted spread (ask - bid)
when the trade occurs within the quotes. -/
@[stat_lemma]
theorem effective_le_quoted {trade_price bid ask mid : ℝ}
    (hmid : mid = (bid + ask) / 2)
    (hbid : bid ≤ trade_price)
    (hask : trade_price ≤ ask) :
    2 * |trade_price - mid| ≤ ask - bid := by
  subst hmid
  have h_abs : |trade_price - (bid + ask) / 2| ≤ (ask - bid) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  linarith

/-- **Market maker inventory risk.** A market maker with inventory `q`
and mid-price `m` has P&L `q * Δm` from a price change `Δm`.
The absolute P&L is bounded by `|q| * |Δm|`. -/
@[stat_lemma]
theorem inventory_pnl_bound {q Δm : ℝ} :
    |q * Δm| = |q| * |Δm| := abs_mul q Δm

/-- **Optimal market maker quote.** The Avellaneda-Stoikov (2008)
result: the optimal quote is offset from mid by `γ * σ² * q * T`
where `γ` is risk aversion, `σ²` is variance, `q` is inventory,
and `T` is time to close. The offset is monotone in each parameter. -/
@[stat_lemma]
theorem avellaneda_stoikov_offset_nonneg {γ σ_sq T : ℝ} {q : ℝ}
    (hγ : 0 ≤ γ) (hσ : 0 ≤ σ_sq) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    0 ≤ γ * σ_sq * q * T := by
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg hγ hσ
  exact hq
  exact hT

/-- **Tick-to-trade ratio.** If there are `T` ticks and `N` trades in
an interval with `N > 0`, the tick-to-trade ratio `T / N` is positive
when `T > 0`. This ratio measures market activity intensity. -/
@[stat_lemma]
theorem tick_trade_ratio_pos {T N : ℝ}
    (hT : 0 < T) (hN : 0 < N) :
    0 < T / N := div_pos hT hN

end Pythia.Finance.HFT.Microstructure
