# Security Policy

## Supported versions

The pythia library is shipped from `main`. We do not maintain
back-versions; security fixes ship as new commits on `main` and the
patched commit becomes the supported version. Pin to a tagged release
or a specific commit if your build requires reproducibility.

| Version       | Supported          |
|---------------|--------------------|
| `main` (HEAD) | ✅                 |
| Tagged releases (latest 1) | ✅    |
| Older tagged releases       | ❌  |
| Forks                       | ❌ (we cannot speak to forks) |

## Reporting a vulnerability

**Do not open a public GitHub issue for a security report.** Public
issues are visible to everyone, including potential attackers, before
a fix can land.

Report security issues privately via GitHub's "Report a vulnerability"
button on the [Security Advisories
tab](https://github.com/athanor-ai/pythia/security/advisories/new).
You will receive an acknowledgement within 5 business days.

If GitHub Security Advisories are unavailable for any reason, email
`security@athanorl.com` with the subject `[pythia] security report`.

## What counts as a security issue here

Pythia is a Lean 4 + Python library, not a network service, so the
attack surface is narrow. We treat the following as security-relevant:

- A way to make the Lean kernel accept a false statement as a theorem
  (kernel soundness bug surfaced via pythia tactics or attributes).
- A path by which an out-of-band axiom can land in a `@[stat_lemma]`
  / `@[stats_ineq]` / `@[prob_simp]` member without being flagged by
  `Pythia/AxiomAudit.lean`.
- Code execution via `tools/` that goes beyond the documented
  scope (e.g. a CLI flag that reads or writes arbitrary paths
  outside the repo working tree).
- A supply-chain hazard introduced via a Lake dependency or a GitHub
  Actions step.

What we do NOT consider security issues:

- A theorem that proves an unintended statement because of a stated
  mistake in the hypotheses. That is a math bug. Open a normal
  issue.
- A tactic that fails to close a goal it should close. That is a
  performance / completeness bug. Open a normal issue.

## Disclosure

We follow [coordinated disclosure](https://en.wikipedia.org/wiki/Coordinated_vulnerability_disclosure):
the reporter and the maintainers agree on a fix and a publication date,
and credit is given in the published advisory unless the reporter
prefers anonymity.

## Out of scope

Pythia is offline-first by design (see `CONTRIBUTING.md` rule 4). We
do not accept reports about the absence of features that would only
matter for an LLM-coupled or cloud-coupled use case.
