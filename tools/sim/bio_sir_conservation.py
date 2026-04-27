"""SIR epidemiological conservation -- empirical companion.

Lean side (`Pythia/Bio/Population.lean::sir_total_population_derivative_zero`)
proves: given dS = -beta*S*I, dI = beta*S*I - gamma*I, dR = gamma*I,
then dS + dI + dR = 0 (total population N = S + I + R is conserved).

Classical Kermack-McKendrick (1927) SIR model: the infection flux beta*S*I
enters dI with a plus sign and dS with a minus sign; the recovery flux
gamma*I enters dR with a plus sign and dI with a minus sign.  All fluxes
cancel, leaving dN/dt = 0.

Run:
    python -m tools.sim.bio_sir_conservation

Or via pytest:
    pytest tools/sim/bio_sir_conservation.py
"""
from __future__ import annotations

from tools.sim.harness import (
    Mutation,
    Strategy,
    floats,
    isclose,
    run_harness,
)


def sir_conservation_spec(
    beta: float,
    gamma: float,
    S: float,
    I: float,
    R: float,
) -> bool:
    """The theorem itself, evaluated numerically.

    Computes each ODE right-hand side and checks dS + dI + dR == 0.
    The tolerance is scaled to the magnitude of the largest individual
    flux so that cancellation errors at large S, I values are handled
    correctly.
    """
    dS = -beta * S * I
    dI = beta * S * I - gamma * I
    dR = gamma * I
    # Scale atol to the dominant flux to handle floating-point cancellation.
    flux_scale = max(abs(dS), abs(dI), abs(dR), 1.0)
    return isclose(dS + dI + dR, 0.0, atol=flux_scale * 1e-9)


# Mutations: deliberate bugs that should cause the conservation to fail.

def _drop_minus_on_dS(
    beta: float,
    gamma: float,
    S: float,
    I: float,
    R: float,
) -> bool:
    """Sign error: dS = +beta*S*I instead of -beta*S*I."""
    dS = beta * S * I          # wrong sign
    dI = beta * S * I - gamma * I
    dR = gamma * I
    flux_scale = max(abs(dS), abs(dI), abs(dR), 1.0)
    return isclose(dS + dI + dR, 0.0, atol=flux_scale * 1e-9)


def _drop_gamma_in_dI(
    beta: float,
    gamma: float,
    S: float,
    I: float,
    R: float,
) -> bool:
    """Forgot the recovery term: dI = beta*S*I instead of beta*S*I - gamma*I."""
    dS = -beta * S * I
    dI = beta * S * I          # missing - gamma*I
    dR = gamma * I
    flux_scale = max(abs(dS), abs(dI), abs(dR), 1.0)
    return isclose(dS + dI + dR, 0.0, atol=flux_scale * 1e-9)


def _double_dR(
    beta: float,
    gamma: float,
    S: float,
    I: float,
    R: float,
) -> bool:
    """Double-counted recovery: dR = 2*gamma*I instead of gamma*I."""
    dS = -beta * S * I
    dI = beta * S * I - gamma * I
    dR = 2 * gamma * I         # factor-of-2 error
    flux_scale = max(abs(dS), abs(dI), abs(dR), 1.0)
    return isclose(dS + dI + dR, 0.0, atol=flux_scale * 1e-9)


# Realistic epidemiological parameter ranges:
#   beta  in [1e-4, 1.0]   per-contact transmission rate
#   gamma in [1e-2, 1.0]   recovery rate (1/infectious period)
#   S, R  in [0, 1e5]      susceptible / recovered counts
#   I     in [0, 1e3]      infectious count (typically smaller)
STRATEGY = Strategy(
    beta=floats(1e-4, 1.0),
    gamma=floats(1e-2, 1.0),
    S=floats(0.0, 1e5),
    I=floats(0.0, 1e3),
    R=floats(0.0, 1e5),
)

MUTATIONS = (
    Mutation(name="drop_minus_on_dS", spec=_drop_minus_on_dS),
    Mutation(name="drop_gamma_in_dI", spec=_drop_gamma_in_dI),
    Mutation(name="double_dR", spec=_double_dR),
)


def main() -> int:
    result = run_harness(
        name="bio.sir_total_population_derivative_zero",
        spec=sir_conservation_spec,
        strategy=STRATEGY,
        n_pbt=10_000,
        sweep_points=4,
        mutations=MUTATIONS,
    )
    print(result.summarize())
    return 0 if result.all_passed else 1


def test_sir_total_population_derivative_zero() -> None:
    result = run_harness(
        name="bio.sir_total_population_derivative_zero",
        spec=sir_conservation_spec,
        strategy=STRATEGY,
        n_pbt=2_000,
        sweep_points=4,
        mutations=MUTATIONS,
    )
    assert result.pbt_passed, (
        f"PBT failed at {result.first_pbt_failure}"
    )
    assert result.sweep_passed, (
        f"sweep failed at {result.first_sweep_failure}"
    )
    assert not result.mutations_missed, (
        f"vacuous-test risk: mutations missed = {result.mutations_missed}"
    )


if __name__ == "__main__":
    import sys
    sys.exit(main())
