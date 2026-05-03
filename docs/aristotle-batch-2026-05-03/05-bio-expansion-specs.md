# Pythia.Bio expansion  -  9 theorems (ATH-942)

Filed 2026-05-03 by Sonnet sub-agent at asabi's direction. Grows module from 11 → 20.

## Mathlib gap

Confirmed absent: no `one_compartment_auc`, `halfLife`, `batemanConc`, `kimuraNeutralFixationProb`, `seirR0`, `sir_final_size`, `hill_emax_saturation_limit`, `rct_mean_identifiability` declarations.

Mathlib HAS to build on: `integral_exp_mul_Ioi`, `Real.exp_log`, `IsProbabilityMeasure`, `ProbabilityTheory.IndepFun.integral_mul_eq_integral_mul_integral`, `Continuous.ivt`.

## Existing (NOT to duplicate)

Mainline Bio (11): massAction_existence/nonneg/conservation, detailed_balance_equilibrium, felsenstein_correct_spec, JukesCantor_pi_sum, hardy_weinberg_conservation, lotka_volterra_equilibrium_x/y_pos, sir_total_population_derivative_zero, michaelis_menten_saturation. Frontier Bio (WIP): hillSaturation_*, sir_subcritical/supercritical, wrightFisherFixation_*.



## PK/PD (3)

1. **one_compartment_auc** [easy] AUC = D/(V_d · k_e) for IV bolus. Citation: Rowland-Tozer Ch. 2.
2. **half_life_clearance_relation** [easy] t_{1/2} = ln(2)/k_e satisfies C_0 · exp(-k_e · t_{1/2}) = C_0/2. Citation: Wagner 1971.
3. **bateman_equation_positivity** [medium] Oral-dose Bateman concentration > 0 for t > 0, k_a > k_e > 0. Citation: Bateman 1910; Teorell 1937.

## Population Genetics (2)

4. **kimura_neutral_fixation** [easy] Neutral mutant fixation prob = 1/(2N). Citation: Kimura 1962.
5. **hwe_allele_frequency_invariance** [easy] HWE preserves allele frequency under random mating. Citation: Hardy 1908; Weinberg 1908.

## Compartmental Epidemiology (2)

6. **seir_r0_threshold** [easy] SEIR sub-threshold (β·S·I - γ·I ≤ 0) when β·S/γ ≤ 1. Citation: Anderson-May 1991 Ch. 2.
7. **sir_final_size_positive_solution** [medium] Kermack-McKendrick: r = 1 - exp(-R_0 · r) has positive r when R_0 > 1. Citation: Kermack-McKendrick 1927.

## Gene-Regulatory / PD (1)

8. **hill_emax_saturation_limit** [medium] E(c) = E_max · c^n/(EC50^n + c^n) → E_max as c → ∞. Citation: Hill 1910; Holford-Sheiner 1981.

## Clinical Trials (1)

9. **rct_mean_identifiability** [easy] RCT independence ⟹ E[T·Y] = E[T]·E[Y]. Citation: Rubin 1974; Imbens-Rubin 2015 Theorem 3.2.

## Difficulty mix

| | Easy | Medium | Hard |
| - | - :| - :| - :|
| Count | 6 | 3 | 0 |

## Starter theorem (fire to Aristotle today)

**hwe_allele_frequency_invariance**  -  easy, `ring` closes after `rw [hq]`. Concrete and headline-named.

## Build order

Easy starters (1, 2, 4, 5, 6, 9) → Medium (3, 7, 8). All tractable; no hard tail in this expansion.
