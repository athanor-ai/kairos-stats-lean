# Pythia.MechanismDesign — 20 theorem specs (ATH-939)

Filed 2026-05-03 by Sonnet sub-agent at asabi's direction.

## Mathlib gap (verified absent across all 6 keyword sweeps)

`auction|Vickrey|VCG|truthful|incentive_compatible|Gibbard|Satterthwaite|Arrow|dominant_strategy|Nash|revelation|monotone.*mechanism|payment_rule|optimal_reserve|virtual_value|hazard_rate|IIA|social_welfare_function|Bulow|Klemperer|Myerson` → 0 hits in any mechanism-design context.

Mathlib HAS to build on: `Fintype`, `Fin n`, `LinearOrder`, `Monotone`/`StrictMono`, `MeasureTheory.integral`, `Finset.sup'`, `IsGreatest`/`IsLeast`, Hall's marriage theorem, Farkas' lemma. None of these contain mechanism-design content.

---

## Single-Item Auctions (5)

1. **vickrey_second_price_dominant_strategy** [easy-medium] Vickrey SPA truthful bidding weakly dominates all others. Citation: Vickrey 1961; NRTV AGT Ch. 9 §9.2.
2. **second_price_allocation_efficient** [easy] SPA allocates to highest-value bidder. Citation: NRTV Theorem 9.12.
3. **revenue_equivalence_uniform_two_bidder** [easy] FPSB and SPSB yield equal revenue with 2 bidders, uniform [0,1]. Citation: Myerson 1981.
4. **first_price_symmetric_equilibrium_bid** [medium] FPSB symmetric BNE: b*(v) = (n-1)/n · v. Citation: Krishna Auction Theory Prop 2.2.
5. **vickrey_individual_rationality** [easy] SPA participation is weakly beneficial. Citation: Vickrey 1961.

## Multi-Item / VCG (4)

6. **vcg_truthfulness** [medium] VCG is dominant-strategy incentive compatible. Citation: Vickrey-Clarke-Groves; NRTV Theorem 9.16.
7. **vcg_efficiency** [easy] VCG maximizes social welfare. Citation: Groves 1973.
8. **groves_mechanism_characterization** [hard] DSIC + efficient ⟹ Groves payment form. Citation: Green-Laffont 1977; Holmstrom 1979.
9. **vcg_budget_balance_failure** [easy] VCG can run a deficit (witness counter-example). Citation: NRTV §9.4.

## Revenue Equivalence + Optimal Mechanism Design (4)

10. **revenue_equivalence_theorem** [hard] Symmetric efficient BNE mechanisms with same allocation + same lowest-type utility yield same revenue. Citation: Myerson 1981 Theorem 1.
11. **myerson_optimal_reserve_price** [medium] Optimal reserve r* solves φ(r*) = 0 (virtual value zero-crossing). Citation: Myerson 1981 Theorem 6.
12. **virtual_value_expected_revenue** [hard] Expected revenue = expected virtual surplus. Citation: Myerson 1981 §3 Lemma 2; NRTV Theorem 3.7.
13. **bulow_klemperer_augmented_auction** [easy framing] SPA with n+1 bidders ≥ optimal Myerson with n. Citation: Bulow-Klemperer 1996.

## Social Choice (4)

14. **condorcet_winner_majority_characterization** [medium] Condorcet winner is unique. Citation: Condorcet 1785; Black 1958.
15. **arrow_impossibility** [hard] SWF satisfying Pareto + IIA must be a dictatorship (≥3 alternatives, ≥2 voters). Citation: Arrow 1951; NRTV Theorem 10.2.
16. **gibbard_satterthwaite** [hard] Surjective + strategy-proof SCF ⟹ dictatorship (≥3 alternatives). Citation: Gibbard 1973; Satterthwaite 1975.
17. **gibbard_strategyproofness_randomized** [hard] Strategy-proof random mechanisms = mixtures of dictatorships + duples. Citation: Gibbard 1977.

## Mechanism Design Impossibilities (3)

18. **myerson_satterthwaite_impossibility** [hard] No BIC + IR + ex-post efficient bilateral trade mechanism. Citation: Myerson-Satterthwaite 1983.
19. **roberts_affine_maximizer** [hard] Unrestricted-domain DSIC ⟹ affine maximizer. Citation: Roberts 1979.
20. **spence_mirrlees_single_crossing** [medium] Single-crossing + IC ⟹ allocation monotone in type. Citation: Mirrlees 1971; Spence 1973.

## Difficulty mix

| | Easy | Medium | Hard |
|---|---:|---:|---:|
| Count | 7 | 6 | 7 |

## Starter theorem (fire to Aristotle today)

**vcg_efficiency** — easy, ~3 line proof unfolding `IsGreatest` + applying hypothesis. Concrete and headline-named.

## Build order

Easy starters (2, 5, 7, 9, 13) → Auction core (1, 3, 4, 6, 11, 14, 20) → Hard tail (8, 10, 12, 15, 16, 17, 18, 19).
