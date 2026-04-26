/-
Copyright (c) 2026 Pythia contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Little's Law  (L = λ · W)

## Statement

For any queueing system whose cumulative-arrival process `A`, time-average
number-in-system `L_bar`, and running mean sojourn time `W_bar` satisfy the
**sample-path integral identity**

    `L_bar t = (A t / t) * W_bar t`        for all `t > 0`

and whose three defining limits exist:

  * `λ  = lim_{t → ∞}  A(t) / t`        (arrival rate),
  * `W  = lim_{t → ∞}  W_bar(t)`        (mean sojourn time),
  * `L  = lim_{t → ∞}  L_bar(t)`        (time-average number in system),

we have **`L = λ · W`**.

## Proof sketch

The function `t ↦ (A t / t) * W_bar t` tends to `λ * W` by the product-of-
limits rule (`Filter.Tendsto.mul`).  But this function *equals* `L_bar` for
all positive `t`, so `L_bar` also tends to `λ * W`.  Since limits in a
Hausdorff space are unique (`tendsto_nhds_unique`), `L = λ * W`.

## Reference

J. D. C. Little, "A Proof for the Queuing Formula: L = λW",
*Operations Research* **9** (3), 383–387, 1961.

## Applications

Cloud SLA capacity planning, call-centre staffing, network engineering,
inventory management.
-/

import Mathlib

open Filter Topology

/-! ### Core sample-path formulation -/

/-
**Little's Law (sample-path form).**

Given real-valued functions modelling a queueing system:
  * `A`     — cumulative arrivals by time `t`,
  * `L_bar` — running time-average number in system,
  * `W_bar` — running mean sojourn time,

and three limit values `arr_rate` (λ), `mean_sojourn` (W), `avg_in_system` (L),
if the sample-path integral identity holds for all positive `t` and all three
limits exist, then `L = λ · W`.
-/
theorem littles_law
    (A L_bar W_bar : ℝ → ℝ)
    (arr_rate mean_sojourn avg_in_system : ℝ)
    (h_identity : ∀ t : ℝ, 0 < t → L_bar t = (A t / t) * W_bar t)
    (h_arr   : Tendsto (fun t => A t / t) atTop (𝓝 arr_rate))
    (h_soj   : Tendsto W_bar             atTop (𝓝 mean_sojourn))
    (h_L     : Tendsto L_bar             atTop (𝓝 avg_in_system)) :
    avg_in_system = arr_rate * mean_sojourn := by
  exact tendsto_nhds_unique h_L ( Filter.Tendsto.congr' ( Filter.eventuallyEq_of_mem ( Filter.Ioi_mem_atTop 0 ) fun x hx => by rw [ h_identity x hx ] ) ( h_arr.mul h_soj ) )

/-! ### Convenience corollaries -/

/-
**Little's Law — rate form.**  `λ = L / W` when `W ≠ 0`.
-/
theorem littles_law_rate
    (A L_bar W_bar : ℝ → ℝ)
    (arr_rate mean_sojourn avg_in_system : ℝ)
    (h_identity : ∀ t : ℝ, 0 < t → L_bar t = (A t / t) * W_bar t)
    (h_arr   : Tendsto (fun t => A t / t) atTop (𝓝 arr_rate))
    (h_soj   : Tendsto W_bar             atTop (𝓝 mean_sojourn))
    (h_L     : Tendsto L_bar             atTop (𝓝 avg_in_system))
    (hW : mean_sojourn ≠ 0) :
    arr_rate = avg_in_system / mean_sojourn := by
  exact eq_div_of_mul_eq hW ( by linarith [ tendsto_nhds_unique h_L ( h_arr.mul h_soj |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with t ht; aesop ) ) ] )

/-
**Little's Law — sojourn form.**  `W = L / λ` when `λ ≠ 0`.
-/
theorem littles_law_sojourn
    (A L_bar W_bar : ℝ → ℝ)
    (arr_rate mean_sojourn avg_in_system : ℝ)
    (h_identity : ∀ t : ℝ, 0 < t → L_bar t = (A t / t) * W_bar t)
    (h_arr   : Tendsto (fun t => A t / t) atTop (𝓝 arr_rate))
    (h_soj   : Tendsto W_bar             atTop (𝓝 mean_sojourn))
    (h_L     : Tendsto L_bar             atTop (𝓝 avg_in_system))
    (h_arr_ne : arr_rate ≠ 0) :
    mean_sojourn = avg_in_system / arr_rate := by
  exact eq_div_of_mul_eq h_arr_ne <| by linarith [ littles_law A L_bar W_bar arr_rate mean_sojourn avg_in_system h_identity h_arr h_soj h_L ] ;