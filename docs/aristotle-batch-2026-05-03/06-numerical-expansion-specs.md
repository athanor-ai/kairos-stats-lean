# Pythia.Numerical expansion — 16 theorems (ATH-943)

Filed 2026-05-03 by Sonnet sub-agent at asabi's direction. Grows module from 14 → 30.

## Mathlib gap

Confirmed absent: `SVD`, `QR factorization` (named theorem), `Cholesky` (named decomposition; LDL exists), `polar decomposition`, `LU partial pivot`, `Weyl eigenvalue inequality`, `Bauer-Fike`, `Courant-Fischer min-max`, `Cauchy interlacing`, `gradient descent rate`, `Newton's method real-variable convergence`, `conjugate gradient`, `Forward Euler local truncation error`, `RK4 order 4`, `Lax equivalence`, `IEEE-754 ULP analysis`.

Mathlib HAS to build on: `Matrix`, `Matrix.IsHermitian`, `IsHermitian.eigenvalues` + `eigenvalues₀_antitone`, `Matrix.PosDef` + `Matrix.PosSemidef`, `Mathlib.Analysis.Matrix.LDL`, `gramSchmidtOrthonormalBasis` + `gramSchmidtOrthonormalBasis_inv_blockTriangular`, `HermitianFunctionalCalculus`, `StrongConvexOn`, `LipschitzWith`, `Taylor.taylor_mean_remainder_bound`.

## Existing (NOT to duplicate)

`kkt_necessary`, `kkt_sufficient_convex`, `picard_lindelof_local/global/global_existence/continuous_dependence`, `lyapunov_stable/asymptotic`, `lasalle_invariance`, `kahan_error_bound`, `naive_error_bound`, `newton_quadratic_iter_pos`.

---

## Matrix Decompositions (5)

1. **svd_existence** [hard] Real SVD: A = U Σ Vᵀ. Citation: Trefethen-Bau Lecture 4.
2. **qr_factorization_existence** [medium] m≥n ⟹ A = QR with Q orthonormal cols, R upper-tri non-neg diag. Citation: Golub-Van Loan Theorem 5.2.2.
3. **cholesky_existence_unique** [medium] SPD A = L Lᵀ uniquely with L lower-tri positive diag. Citation: Golub-Van Loan Theorem 4.2.5.
4. **polar_decomposition_existence** [hard] A = QS with Q orthogonal, S PSD. Citation: Golub-Van Loan §6.4.
5. **lu_partial_pivot_existence** [medium] PA = LU with L unit-lower, U upper. Citation: Golub-Van Loan Algorithm 3.4.1.

## Eigenvalue Inequalities (4)

6. **weyl_eigenvalue_inequality** [medium] λ_k(A+E) ≤ λ_k(A) + λ_max(E). Citation: Weyl 1912; Trefethen-Bau Theorem 24.3.
7. **bauer_fike_eigenvalue_bound** [medium] |μ - λ_i| ≤ κ(X) ‖E‖. Citation: Bauer-Fike 1960.
8. **courant_fischer_min_max** [hard] λ_k(A) = sup over (n-k+1)-dim subspaces of inf Rayleigh. Citation: Courant 1920; Fischer 1905.
9. **cauchy_interlacing** [hard] Eigenvalues of principal submatrix interlace. Citation: Horn-Johnson §4.3.

## Optimization Algorithm Correctness (3)

10. **gradient_descent_geometric_convergence** [medium] m-strongly-convex L-smooth: ‖x_k - x*‖² ≤ ((L-m)/(L+m))^{2k}‖x_0 - x*‖². Citation: Boyd-Vandenberghe §9.3.
11. **newton_method_quadratic_convergence** [hard] Local quadratic convergence with Lipschitz Hessian. Citation: Nocedal-Wright Theorem 3.5.
12. **conjugate_gradient_finite_termination** [hard] CG terminates in ≤n steps for n×n SPD. Citation: Hestenes-Stiefel 1952.

## ODE Numerical Methods (3)

13. **forward_euler_local_truncation_error** [easy] |y(t+h) - Euler(t,h)| ≤ (h²/2) sup|y''|. Citation: Hairer-Nørsett-Wanner Solving ODEs I §I.2.
14. **rk4_fourth_order_accuracy** [hard] Local error O(h^5). Citation: Butcher 1963.
15. **lax_equivalence** [hard] Consistency + Stability ⟺ Convergence. Citation: Lax-Richtmyer 1956.

## Floating-Point (1)

16. **ieee754_round_nearest_relative_error** [easy-medium] |fl(x) - x| ≤ (ε/2)|x|. Citation: Higham 2nd ed. Theorem 2.2.

## Difficulty mix

| | Easy | Medium | Hard |
|---|---:|---:|---:|
| Count | 1 | 7 | 8 |

## Starter theorem (fire to Aristotle today)

**forward_euler_local_truncation_error** — easy, follows from Taylor's theorem with remainder. ~25 lines. Note this isn't a NEW domain so no starter is being fired today; the new-domain starters (IT, MD, Distributed) take priority. Numerical starter will be in tomorrow's batch.

## Build order

Easy: 13. Medium core: 2, 3, 5, 6, 7, 10, 16. Hard tail: 1, 4, 8 (req for 9), 9, 11, 12, 14, 15.
