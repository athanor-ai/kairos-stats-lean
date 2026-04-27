"""tools.sim.theorem_manifest — central registry of pythia theorems.

Source of truth for ``(lean_path, lean_theorem, sim_path, harness_test,
domain, mathlib_status, mutations)``. Every cross-domain theorem
shipped in pythia (post-ATH-742) registers here. CI loops over the
manifest entries to:

* run ``pytest <sim_path>::<harness_test>`` per entry (regression
  sweep on every PR; mathlib bumps surface as harness drift)
* drive ``tools/check_lean_spec.py`` against ``lean_path`` for the
  ATH-743 spec-health gate
* answer ``pythia list-theorems --domain X`` from the customer side
  (future ``tools/cli.py``)

Adding a new theorem: append a :class:`TheoremEntry` to ``MANIFEST``
below. ``tools/add_theorem.py`` (CLI scaffold) does this
automatically.

Manifest is plain Python (not YAML) so it imports without parsing
overhead and uses dataclass type checks for the registry shape.
"""
from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


REPO_ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class TheoremEntry:
    """One row in the registry. All paths are relative to repo root."""

    domain: str
    """Top-level area: 'economics', 'chemistry', 'biology',
    'engineering', 'mechanical', 'control', 'or', 'mathlib_tags'."""

    name: str
    """Short identifier matching the Lean theorem name (e.g.
    'cobb_douglas_crts')."""

    lean_path: str
    """Path to the .lean file, e.g. 'Pythia/Economics/CobbDouglas.lean'."""

    lean_theorem: str
    """Fully-qualified Lean theorem identifier including namespace,
    e.g. 'Pythia.Economics.cobb_douglas_crts'."""

    sim_path: str
    """Path to the Python harness, e.g.
    'tools/sim/economics_cobb_douglas.py'."""

    sim_test: str
    """pytest test function name in sim_path, e.g.
    'test_cobb_douglas_crts'."""

    mathlib_status: str
    """One of: 'novel' (not in mathlib), 'retag' (named entry exists
    in mathlib, pythia adds @[stat_lemma]), 'extension' (extends a
    mathlib concept with new framing)."""

    summary: str = ""
    """One-sentence description of the theorem for `pythia list`
    output. Optional but recommended."""

    references: list[str] = field(default_factory=list)
    """Bibliographic citations for the named result, mirroring the
    Lean module docstring's References section. Optional."""

    drafter: str = "unknown"
    """Which AI drafter (or human) first produced the closed Lean proof.
    Allowed values: 'aristotle', 'dspv2', 'sonnet', 'opus', 'human',
    'unknown'. Backfilled from git history / PR bodies; see ATH-779."""


# ─────────────────────────────────────────────────────────────────────
# The registry
# ─────────────────────────────────────────────────────────────────────


MANIFEST: tuple[TheoremEntry, ...] = (
    # ── Economics ─────────────────────────────────────────────────
    TheoremEntry(
        domain="economics",
        name="cobb_douglas_crts",
        lean_path="Pythia/Economics/CobbDouglas.lean",
        lean_theorem="Pythia.Economics.cobb_douglas_crts",
        sim_path="tools/sim/economics_cobb_douglas.py",
        sim_test="test_cobb_douglas_crts",
        mathlib_status="novel",
        summary="Cobb-Douglas constant returns to scale: scaling all inputs by lambda scales output by lambda.",
        references=["Cobb, C.W. and Douglas, P.H. American Economic Review 18(Suppl): 139-165 (1928)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="economics",
        name="cobb_douglas_pos",
        lean_path="Pythia/Economics/CobbDouglas.lean",
        lean_theorem="Pythia.Economics.cobb_douglas_pos",
        sim_path="tools/sim/economics_cobb_douglas.py",
        sim_test="test_cobb_douglas_crts",  # bundled in the same harness
        mathlib_status="novel",
        summary="Cobb-Douglas output positivity for positive K, L.",
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="economics",
        name="crra_marginal_utility_pos",
        lean_path="Pythia/Economics/CRRA.lean",
        lean_theorem="Pythia.Economics.crra_marginal_utility_pos",
        sim_path="tools/sim/economics_crra.py",
        sim_test="test_crra_marginal_utility_pos",
        mathlib_status="novel",
        summary="CRRA marginal utility c^(-gamma) > 0 for c > 0.",
        references=["Pratt, J.W. Econometrica 32 (1964); Arrow, K.J. Yrjö Jahnsson Lectures (1965)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="economics",
        name="capm_beta_nonneg",
        lean_path="Pythia/Economics/CAPM.lean",
        lean_theorem="Pythia.Economics.capm_beta_nonneg",
        sim_path="tools/sim/economics_capm.py",
        sim_test="test_capm_beta_nonneg",
        mathlib_status="novel",
        summary="CAPM beta = Cov(R_i, R_m)/Var(R_m) >= 0 when assets positively correlated.",
        references=["Sharpe, W.F. J. Finance 19(3): 425-442 (1964); Lintner, J. Rev. Econ. Stat. 47(1): 13-37 (1965)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="economics",
        name="risk_neutral_call_nonneg",
        lean_path="Pythia/Economics/RiskNeutralCall.lean",
        lean_theorem="Pythia.Economics.risk_neutral_call_nonneg",
        sim_path="tools/sim/economics_risk_neutral_call.py",
        sim_test="test_risk_neutral_call_nonneg",
        mathlib_status="novel",
        summary="Risk-neutral call option price max(S-K,0)*exp(-r*T) >= 0.",
        references=["Cox, J.C., Ross, S.A., Rubinstein, M. J. Financial Economics 7(3): 229-263 (1979); Black, F. and Scholes, M. J. Political Economy 81(3): 637-654 (1973)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="economics",
        name="walras_clearing_implies_zero_sum",
        lean_path="Pythia/Economics/Walras.lean",
        lean_theorem="Pythia.Economics.walras_clearing_implies_zero_sum",
        sim_path="tools/sim/economics_walras.py",
        sim_test="test_walras_clearing",
        mathlib_status="novel",
        summary="Walras' Law: when all excess demands clear (z_i = 0), the price-weighted sum is zero.",
        references=["Walras, L. Eléments d'économie politique pure (1874)"],
        drafter="sonnet",
    ),

    # ── Chemistry ─────────────────────────────────────────────────
    TheoremEntry(
        domain="chemistry",
        name="arrhenius_pos",
        lean_path="Pythia/Chemistry/Arrhenius.lean",
        lean_theorem="Pythia.Chemistry.arrhenius_pos",
        sim_path="tools/sim/chemistry_arrhenius.py",
        sim_test="test_arrhenius_pos",
        mathlib_status="novel",
        summary="Arrhenius rate constant k = A*exp(-Ea/(RT)) > 0.",
        references=["Arrhenius, S. Z. Phys. Chem. 4: 226-248 (1889)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="chemistry",
        name="hh_monotone_in_ratio",
        lean_path="Pythia/Chemistry/HendersonHasselbalch.lean",
        lean_theorem="Pythia.Chemistry.hh_monotone_in_ratio",
        sim_path="tools/sim/chemistry_henderson_hasselbalch.py",
        sim_test="test_hh_monotone_in_ratio",
        mathlib_status="novel",
        summary="Henderson-Hasselbalch pH = pKa + log10([A-]/[HA]) is monotone increasing in the ratio.",
        references=["Henderson, L.J. American Journal of Physiology 21(2): 173-179 (1908); Hasselbalch, K.A. Biochem. Z. 78: 112-144 (1917)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="chemistry",
        name="mass_action_conservation_pair",
        lean_path="Pythia/Chemistry/MassActionConservation.lean",
        lean_theorem="Pythia.Chemistry.mass_action_conservation_pair",
        sim_path="tools/sim/chemistry_mass_action.py",
        sim_test="test_mass_action_conservation_pair",
        mathlib_status="novel",
        summary="Mass-action stoichiometric conservation for A <-> B: total moles constant under reaction extent.",
        references=["Guldberg, C.M. and Waage, P. Forhandlinger Videnskabs-Selskabet i Christiania (1864)"],
        drafter="sonnet",
    ),

    # ── Biology ───────────────────────────────────────────────────
    TheoremEntry(
        domain="biology",
        name="hardy_weinberg_conservation",
        lean_path="Pythia/Bio/Population.lean",
        lean_theorem="Pythia.Bio.Population.hardy_weinberg_conservation",
        sim_path="tools/sim/bio_hardy_weinberg.py",
        sim_test="test_hardy_weinberg",
        mathlib_status="novel",
        summary="Hardy-Weinberg allele-frequency conservation: p^2 + 2pq + q^2 = 1 when p+q=1.",
        references=["Hardy, G.H. Science 28(706): 49-50 (1908); Weinberg, W. Jahresh. Verein f. vaterländ. Naturkunde in Württemberg 64: 369-382 (1908)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="biology",
        name="lotka_volterra_equilibrium_x_pos",
        lean_path="Pythia/Bio/Population.lean",
        lean_theorem="Pythia.Bio.Population.lotka_volterra_equilibrium_x_pos",
        sim_path="tools/sim/bio_lotka_volterra.py",
        sim_test="test_lotka_volterra_equilibrium_pos",
        mathlib_status="novel",
        summary="Lotka-Volterra prey equilibrium x* = gamma/delta > 0.",
        references=["Lotka, A.J. Elements of Physical Biology (1925); Volterra, V. Mem. R. Accad. Naz. dei Lincei 2 (1926)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="biology",
        name="lotka_volterra_equilibrium_y_pos",
        lean_path="Pythia/Bio/Population.lean",
        lean_theorem="Pythia.Bio.Population.lotka_volterra_equilibrium_y_pos",
        sim_path="tools/sim/bio_lotka_volterra.py",
        sim_test="test_lotka_volterra_equilibrium_pos",
        mathlib_status="novel",
        summary="Lotka-Volterra predator equilibrium y* = alpha/beta > 0.",
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="biology",
        name="sir_total_population_derivative_zero",
        lean_path="Pythia/Bio/Population.lean",
        lean_theorem="Pythia.Bio.Population.sir_total_population_derivative_zero",
        sim_path="tools/sim/bio_sir_conservation.py",
        sim_test="test_sir_total_population_derivative_zero",
        mathlib_status="novel",
        summary="SIR epidemic model: total population derivative dS+dI+dR is zero.",
        references=["Kermack, W.O. and McKendrick, A.G. Proc. Roy. Soc. A 115(772): 700-721 (1927)"],
        drafter="sonnet",
    ),

    # ── Engineering (electrical) ───────────────────────────────────
    TheoremEntry(
        domain="engineering",
        name="rc_time_constant_pos",
        lean_path="Pythia/Engineering/RCTimeConstant.lean",
        lean_theorem="Pythia.Engineering.rc_time_constant_pos",
        sim_path="tools/sim/engineering_rc_time_constant.py",
        sim_test="test_rc_time_constant_pos",
        mathlib_status="novel",
        summary="RC circuit time constant tau = R*C > 0.",
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="engineering",
        name="signal_energy_nonneg",
        lean_path="Pythia/Engineering/SignalEnergy.lean",
        lean_theorem="Pythia.Engineering.signal_energy_nonneg",
        sim_path="tools/sim/engineering_signal_energy.py",
        sim_test="test_signal_energy_nonneg",
        mathlib_status="novel",
        summary="Discrete signal energy sum |x_n|^2 is non-negative.",
        references=["Oppenheim, A.V. and Schafer, R.W. Discrete-Time Signal Processing 3rd ed (2010)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="engineering",
        name="power_dissipation_nonneg",
        lean_path="Pythia/Engineering/PowerDissipation.lean",
        lean_theorem="Pythia.Engineering.power_dissipation_nonneg",
        sim_path="tools/sim/engineering_power_dissipation.py",
        sim_test="test_power_dissipation_nonneg",
        mathlib_status="novel",
        summary="Joule heating power P = I^2 * R is non-negative when R is non-negative.",
        references=["Ohm, G.S. Die galvanische Kette, mathematisch bearbeitet (1827); Joule, J.P. Philosophical Magazine 19: 260-277 (1841)"],
        drafter="sonnet",
    ),

    # ── Mechanical ────────────────────────────────────────────────
    TheoremEntry(
        domain="mechanical",
        name="hooke_pe_nonneg",
        lean_path="Pythia/Mechanical/HookeSpring.lean",
        lean_theorem="Pythia.Mechanical.hooke_pe_nonneg",
        sim_path="tools/sim/mechanical_hooke_spring.py",
        sim_test="test_hooke_pe_nonneg",
        mathlib_status="novel",
        summary="Hooke spring potential energy U = 0.5*k*x^2 is non-negative.",
        references=["Hooke, R. De Potentia Restitutiva (1678); Goldstein, Poole, Safko Classical Mechanics 3rd ed (2002)"],
        drafter="sonnet",
    ),

    # ── Control ───────────────────────────────────────────────────
    TheoremEntry(
        domain="control",
        name="scalar_lyapunov_nonneg",
        lean_path="Pythia/Control/Lyapunov.lean",
        lean_theorem="Pythia.Control.scalar_lyapunov_nonneg",
        sim_path="tools/sim/control_lyapunov.py",
        sim_test="test_scalar_lyapunov_nonneg",
        mathlib_status="novel",
        summary="Scalar Lyapunov function V(x) = x^2 is non-negative.",
        references=["Lyapunov, A.M. PhD thesis, Kharkov University (1892); translation: The General Problem of the Stability of Motion (1992)"],
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="control",
        name="scalar_lyapunov_stable_decreasing",
        lean_path="Pythia/Control/Lyapunov.lean",
        lean_theorem="Pythia.Control.scalar_lyapunov_stable_decreasing",
        sim_path="tools/sim/control_lyapunov.py",
        sim_test="test_scalar_lyapunov_stable_decreasing",
        mathlib_status="novel",
        summary="For dx/dt = -alpha*x with alpha > 0, the Lyapunov derivative dV/dt is non-positive.",
        drafter="sonnet",
    ),

    # ── Operations Research ──────────────────────────────────────
    TheoremEntry(
        domain="or",
        name="littles_law_nonneg",
        lean_path="Pythia/OR/LittlesLaw.lean",
        lean_theorem="Pythia.OR.littles_law_nonneg",
        sim_path="tools/sim/or_littles_law.py",
        sim_test="test_littles_law_nonneg",
        mathlib_status="novel",
        summary="Little's law: L = lambda*W is non-negative for non-negative arrival rate and wait time.",
        references=["Little, J.D.C. Operations Research 9(3): 383-387 (1961)"],
        drafter="sonnet",
    ),

    # ── Information Theory ────────────────────────────────────────
    TheoremEntry(
        domain="info_theory",
        name="binary_entropy_nonneg",
        lean_path="Pythia/InfoTheory/BinaryEntropy.lean",
        lean_theorem="Pythia.InfoTheory.binary_entropy_nonneg",
        sim_path="tools/sim/info_theory_binary_entropy.py",
        sim_test="test_binary_entropy_nonneg",
        mathlib_status="novel",
        summary="Shannon binary entropy H(p) = -p*log(p) - (1-p)*log(1-p) is non-negative on [0,1].",
        references=["Shannon, C.E. Bell System Technical Journal 27(3): 379-423 (1948)", "Cover, T.M. and Thomas, J.A. Elements of Information Theory 2nd ed (2006)"],
        drafter="sonnet",
    ),

    # ── Mathlib retags + extensions ──────────────────────────────
    TheoremEntry(
        domain="mathlib_tags",
        name="am_gm_two",
        lean_path="Pythia/MathlibTags.lean",
        lean_theorem="Pythia.MathlibTags.am_gm_two",
        sim_path="tools/sim/mathlib_tags_am_gm.py",
        sim_test="test_am_gm_two",
        mathlib_status="extension",
        summary="AM-GM (2 reals): sqrt(a*b) <= (a+b)/2 for a, b >= 0. Direct via discriminant identity.",
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="mathlib_tags",
        name="markov_inequality_retag",
        lean_path="Pythia/MathlibTags.lean",
        lean_theorem="MeasureTheory.meas_ge_le_lintegral_div",
        sim_path="tools/sim/mathlib_tags_markov.py",
        sim_test="test_markov_inequality",
        mathlib_status="retag",
        summary="Markov / Chebyshev inequality: mu{f >= eps} <= integral(f) / eps. Mathlib has the proof; pythia retags + adds empirical sweep.",
        drafter="sonnet",
    ),
    TheoremEntry(
        domain="mathlib_tags",
        name="cauchy_schwarz_two",
        lean_path="Pythia/MathlibTags.lean",
        lean_theorem="Pythia.MathlibTags.cauchy_schwarz_two",
        sim_path="tools/sim/mathlib_tags_cauchy_schwarz.py",
        sim_test="test_cauchy_schwarz_two",
        mathlib_status="extension",
        summary="Cauchy-Schwarz (2 reals): (a*c+b*d)^2 <= (a^2+b^2)*(c^2+d^2). Direct via discriminant trick.",
        drafter="sonnet",
    ),
    # ── Thermodynamics ────────────────────────────────────────────
    TheoremEntry(
        domain="thermodynamics",
        name="carnot_efficiency_upper_bound",
        lean_path="Pythia/Thermodynamics/CarnotEfficiencyUpperBound.lean",
        lean_theorem="Pythia.Thermodynamics.carnot_efficiency_upper_bound",
        sim_path="tools/sim/thermodynamics_carnot_efficiency_upper_bound.py",
        sim_test="test_carnot_efficiency_upper_bound",
        mathlib_status="novel",
        summary="Carnot heat-engine efficiency 1 - T_c/T_h is bounded above by 1.",
        references=["Carnot, S. Réflexions sur la puissance motrice du feu (1824)"],
        drafter="opus",
    ),

    # ── Biology (batch 8) ────────────────────────────────────────
    TheoremEntry(
        domain="biology",
        name="michaelis_menten_saturation",
        lean_path="Pythia/Bio/MichaelisMentenSaturation.lean",
        lean_theorem="Pythia.Bio.michaelis_menten_saturation",
        sim_path="tools/sim/bio_michaelis_menten_saturation.py",
        sim_test="test_michaelis_menten_saturation",
        mathlib_status="novel",
        summary="Michaelis-Menten reaction velocity v = Vmax*S/(Km+S) is bounded above by Vmax.",
        references=["Michaelis, L. and Menten, M.L. Biochem. Z. 49: 333-369 (1913)"],
        drafter="opus",
    ),

    # ── Numerical methods ────────────────────────────────────────
    TheoremEntry(
        domain="numerical",
        name="newton_quadratic_iter_pos",
        lean_path="Pythia/Numerical/NewtonQuadraticIterPos.lean",
        lean_theorem="Pythia.Numerical.newton_quadratic_iter_pos",
        sim_path="tools/sim/numerical_newton_quadratic_iter_pos.py",
        sim_test="test_newton_quadratic_iter_pos",
        mathlib_status="novel",
        summary="Newton iteration on f(x)=x^2-c keeps positive iterates: (x + c/x)/2 > 0 when x > 0 and c > 0.",
        references=["Newton, I. De analysi per aequationes numero terminorum infinitas (1669)"],
        drafter="opus",
    ),

    # ── Information theory (batch 8) ─────────────────────────────
    TheoremEntry(
        domain="info_theory",
        name="hamming_distance_triangle",
        lean_path="Pythia/InfoTheory/HammingDistanceTriangle.lean",
        lean_theorem="Pythia.InfoTheory.hamming_distance_triangle",
        sim_path="tools/sim/infotheory_hamming_distance_triangle.py",
        sim_test="test_hamming_distance_triangle",
        mathlib_status="novel",
        summary="Hamming distance on 3-bit binary tuples satisfies the triangle inequality.",
        references=["Hamming, R.W. Bell System Technical Journal 29(2): 147-160 (1950)"],
        drafter="opus",
    ),

    # ── Cross-field batch 9 (ATH-753) ────────────────────────────
    TheoremEntry(
        domain="optimal_transport",
        name="wasserstein_distance_nonneg",
        lean_path="Pythia/OptimalTransport/WassersteinDistanceNonneg.lean",
        lean_theorem="Pythia.OptimalTransport.wasserstein_distance_nonneg",
        sim_path="tools/sim/optimaltransport_wasserstein_distance_nonneg.py",
        sim_test="test_wasserstein_distance_nonneg",
        mathlib_status="novel",
        summary="Discrete L1 Wasserstein-style cost sum_i |p_i - q_i| is non-negative.",
        references=[
            "Vaserstein, L.N. Problemy Peredachi Informatsii 5(3): 64-72 (1969)",
            "Kantorovich, L.V. Doklady Akademii Nauk SSSR 37: 199-201 (1942)",
        ],
        drafter="opus",
    ),
    TheoremEntry(
        domain="stochastic",
        name="ito_isometry_finite_dim",
        lean_path="Pythia/Stochastic/ItoIsometryFiniteDim.lean",
        lean_theorem="Pythia.Stochastic.ito_isometry_finite_dim",
        sim_path="tools/sim/stochastic_ito_isometry_finite_dim.py",
        sim_test="test_ito_isometry_finite_dim",
        mathlib_status="novel",
        summary="Discrete Ito isometry / Cauchy-Schwarz: (sum f)^2 <= n * sum f^2.",
        references=["Ito, K. Memoirs of the American Mathematical Society 4: 1-51 (1951)"],
        drafter="opus",
    ),
    TheoremEntry(
        domain="quantum",
        name="von_neumann_entropy_nonneg_two_state",
        lean_path="Pythia/Quantum/VonNeumannEntropyNonnegTwoState.lean",
        lean_theorem="Pythia.Quantum.von_neumann_entropy_nonneg_two_state",
        sim_path="tools/sim/quantum_von_neumann_entropy_nonneg_two_state.py",
        sim_test="test_von_neumann_entropy_nonneg_two_state",
        mathlib_status="novel",
        summary="Two-state von Neumann (binary Shannon) entropy is non-negative on [0,1].",
        references=[
            "von Neumann, J. Mathematische Grundlagen der Quantenmechanik, Springer (1932)",
            "Shannon, C.E. Bell System Technical Journal 27(3): 379-423 (1948)",
        ],
        drafter="opus",
    ),
    TheoremEntry(
        domain="game_theory",
        name="minimax_two_strategy_bound",
        lean_path="Pythia/GameTheory/MinimaxTwoStrategyBound.lean",
        lean_theorem="Pythia.GameTheory.minimax_two_strategy_bound",
        sim_path="tools/sim/gametheory_minimax_two_strategy_bound.py",
        sim_test="test_minimax_two_strategy_bound",
        mathlib_status="novel",
        summary="Weak minimax inequality for 2x2 payoff: max_i min_j A i j <= min_j max_i A i j.",
        references=["von Neumann, J. Mathematische Annalen 100: 295-320 (1928)"],
        drafter="opus",
    ),
)


# ─────────────────────────────────────────────────────────────────────
# Public helpers
# ─────────────────────────────────────────────────────────────────────


def by_domain(domain: str) -> tuple[TheoremEntry, ...]:
    """All entries in a given domain."""
    return tuple(e for e in MANIFEST if e.domain == domain)


def by_name(name: str) -> Optional[TheoremEntry]:
    """Single entry by name (None if not found)."""
    for e in MANIFEST:
        if e.name == name:
            return e
    return None


def domains() -> tuple[str, ...]:
    """Distinct domain names, in order of first appearance."""
    seen: list[str] = []
    for e in MANIFEST:
        if e.domain not in seen:
            seen.append(e.domain)
    return tuple(seen)


def assert_files_exist() -> list[str]:
    """Return a list of missing file paths. Empty list = clean."""
    missing: list[str] = []
    for e in MANIFEST:
        if not (REPO_ROOT / e.lean_path).is_file():
            missing.append(e.lean_path)
        if not (REPO_ROOT / e.sim_path).is_file():
            missing.append(e.sim_path)
    return missing


def pytest_args() -> list[str]:
    """Build the `pytest` CLI args that run every harness test
    listed in the manifest. Used by ``pytest --pythia-sim`` (CI hook)
    + ``tools/run_pythia_sim.py``.
    """
    return [f"{e.sim_path}::{e.sim_test}" for e in MANIFEST]


__all__ = [
    "MANIFEST",
    "TheoremEntry",
    "assert_files_exist",
    "by_domain",
    "by_name",
    "domains",
    "pytest_args",
]
