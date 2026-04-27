---
name: Request a new theorem
about: Propose a closed-form fact for the pythia library
title: "[theorem] <one-line summary>"
labels: ["theorem-request"]
---

## Theorem statement

A single closed-form fact you'd like pythia to ship. State it in informal
math first, then in Lean if you can. Be precise about the hypotheses.

```
example: for `(K, L, λ : ℝ)` with `K, L > 0`, `λ > 0`, and `α ∈ (0, 1)`,
the Cobb-Douglas production function satisfies
`(λK)^α (λL)^(1-α) = λ K^α L^(1-α)` (constant returns to scale).
```

## Domain

One of: economics, chemistry, biology, engineering, mechanical, control,
operations research, information theory, signal processing, fluid mechanics,
game theory, probability, statistics, other.

## Mathlib status

- [ ] Not in mathlib (novel pythia contribution)
- [ ] In mathlib as a named result; pythia should add the `@[stat_lemma]`
      tag + the empirical sweep
- [ ] Not sure; help me check

## Suggested closing tactic

If you've thought about how it closes, share it. `positivity` /
`linarith` / `nlinarith` / `ring` / `field_simp` / `mul_pos` /
`div_nonneg` etc. Optional.

## References

Bibliographic citation(s) for the named result. At least one if the
theorem has a proper name.

## Why pythia should ship this

One sentence: who benefits, what does it unlock for the cascade.
