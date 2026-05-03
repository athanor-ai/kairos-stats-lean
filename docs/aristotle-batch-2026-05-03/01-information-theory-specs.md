# Pythia.InformationTheory  -  20 theorem specs (ATH-938)

Filed 2026-05-03 by Sonnet sub-agent at asabi's direction. Source enumeration covers all 5 sub-areas: discrete entropy foundations, AEP/typicality, channel capacity, Fano's inequality, large deviations, source-channel separation, rate-distortion + DPI.

## Mathlib gap (verified absent)

```
grep -rn "shannonEntropy|kraft|aep|AEP|channelCapacity|mutualInfo|fano|Fano|conditionalEntropy|sanov|Sanov|source_coding|rate_distortion|data_processing" \
  .lake/packages/mathlib/Mathlib/
```
→ no results across all 13 keywords.

What Mathlib HAS to build on: `Real.negMulLog`, `Real.binEntropy`, `Real.qaryEntropy`, `InformationTheory.klDiv`, `ProbabilityTheory.strong_law_ae`, `InformationTheory.hammingDist`.



## Discrete entropy foundations (5)

### 1. `shannonEntropy_nonneg` [easy]  -  STARTER
PMF-level Shannon entropy is nonneg.
<!-- doctest: skip-reason: spec target signature, not a complete proof -->
```lean
theorem shannonEntropy_nonneg
    {α : Type*} [Fintype α]
    (p : α → ℝ) (h_nonneg : ∀ a, 0 ≤ p a) (h_sum : ∑ a, p a = 1) :
    0 ≤ ∑ a, Real.negMulLog (p a)
```
Closes via `Real.negMulLog_nonneg` + `Finset.sum_nonneg` in ≤4 lines.
Citation: Cover-Thomas §2.1.

### 2. `shannonEntropy_le_log_card` [medium]
Entropy ≤ log(|α|), with uniform distribution as maximizer. Jensen on `negMulLog` concavity.
Citation: Cover-Thomas Theorem 2.6.4.

### 3. `kraft_inequality` [medium]
Binary prefix-free codes satisfy ∑ 2^{-l(a)} ≤ 1. Requires new `PrefixFreeCode` structure.
Citation: Kraft 1949; Cover-Thomas Theorem 5.2.1.

### 4. `kraft_converse` [hard]
For any lengths satisfying Kraft, a prefix-free code with those lengths exists. Constructive binary-tree.
Citation: Cover-Thomas Theorem 5.2.2.

### 5. `optimal_code_length_lower_bound` [medium]
Any uniquely decodable code has expected length ≥ Shannon entropy. Reduces to KL divergence nonneg via Gibbs.
Citation: Cover-Thomas Theorem 5.4.1.

## AEP / typicality (3)

### 6. `aep_bernoulli` [medium]
For iid Bernoulli(p) samples, `(1/n) log P(X_1,...,X_n) →ᵃˢ -H(p)`. Reduces to SLLN.
Citation: Cover-Thomas Theorem 3.1.2.

### 7. `typical_set_size_lower_bound` [hard]
For ε > 0 and n large, |T_ε^(n)| ≥ (1-ε) · 2^{n·H(p)}. Requires AEP + Chebyshev rate.
Citation: Cover-Thomas Theorem 3.2.2 part 2.

### 8. `typical_set_size_upper_bound` [medium]
For all n, |T_ε^(n)| ≤ 2^{n·(H(p)+ε)}. Direct counting from definition.
Citation: Cover-Thomas Theorem 3.2.2 part 1.

## Channel capacity (3)

### 9. `channel_capacity_eq_sup_mutual_info` [easy as def]
Capacity := sup over input distributions of I(X;Y). Mostly definition + rfl.
Citation: Shannon 1948; Cover-Thomas Definition 7.2.1.

### 10. `mutual_info_nonneg` [medium]
I(X;Y) ≥ 0 via Gibbs / KL nonneg on product measure.
Citation: Cover-Thomas Theorem 2.4.1.

### 11. `bsc_capacity` [medium]
Binary symmetric channel capacity = 1 - H(δ) for crossover prob δ ∈ (0, 1/2).
Citation: Cover-Thomas Example 7.2.1.

## Fano's inequality (2)

### 12. `fano_inequality` [hard]
H(X|Y) ≤ binEntropy(P_e) + P_e · log(|X|-1). Requires defining conditional entropy.
Citation: Fano 1961; Cover-Thomas Theorem 2.10.1.

### 13. `fano_converse_channel_coding` [hard]
For any code with rate R > C, error probability ≥ 1 - (C + 1/n) / R.
Citation: Cover-Thomas Theorem 7.12.1.

## Large deviations (3)

### 14. `sanov_theorem_discrete` [hard]
P(empirical distribution ∈ E) ~ exp(-n · inf_{p∈E} KL(p||q)). Method of types.
Citation: Sanov 1957; Cover-Thomas Theorem 11.4.1.

### 15. `kl_divergence_rate_bound` [medium]
P(p̂ = p) ≤ exp(-n · KL(p||q)) for iid samples from q. Algebra on `klDiv`.
Citation: Cover-Thomas Lemma 11.1.2.

### 16. `chernoff_bound_via_kl` [medium]
Bernoulli tail bound expressed as exp(-n · KL(p||q)). Mgf approach + Legendre.
Citation: Chernoff 1952; Cover-Thomas Theorem 11.8.2.

## Source coding (2)

### 17. `source_coding_achievability` [hard]
For Bernoulli(p) source and rate R > H(p), block codes exist with error → 0. Random-coding via typical set.
Citation: Shannon 1948 Theorem 9; Cover-Thomas Theorem 3.3.1.

### 18. `source_coding_converse` [hard]
For R < H(p), error probability bounded away from 0. Pigeonhole + AEP lower bound.
Citation: Cover-Thomas Theorem 3.3.2.

## Rate-distortion + DPI (2)

### 19. `rate_distortion_lower_bound` [hard]
For Bernoulli(1/2) + Hamming distortion, R(D) ≥ 1 - H(D) bits. Fano + I(X;Y).
Citation: Shannon 1948; Cover-Thomas Theorem 10.2.1.

### 20. `data_processing_inequality` [medium]
X → Y → Z Markov ⟹ I(X;Z) ≤ I(X;Y). Chain rule + Markov factorization.
Citation: Cover-Thomas Theorem 2.8.1.



## Build order

Easy starters (1, 9 def-only) → Medium core (2, 5, 8, 10, 11, 15, 16, 20) → Hard (3, 4, 6 if AEP infra ready, 7, 12, 13, 14, 17, 18, 19).

Headline arc: 1 → 5 (compression lower bound) → 6 (AEP) → 8 (typicality upper) → 17 (source coding direct) → 18 (converse). For channels: 9 → 10 → 11 (BSC) → 12 (Fano) → 13 (channel converse).
