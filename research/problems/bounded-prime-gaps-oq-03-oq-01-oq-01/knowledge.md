# Knowledge Base: bounded-prime-gaps-oq-03-oq-01-oq-01

## State (researcher-8, 2026-06-16)

The missing ingredient is a Chebyshev ψ lower bound
`chebyshev_psi_lower_bound : ∃ c, 0 < c ∧ ∀ x ≥ 2, c * x ≤ Chebyshev.psi x`,
stated as a single `sorry` in `proofs/Proofs/BoundedPrimeGapsOQ03OQ01ChebyshevLower.lean`
(2 sorries) and consumed by `BoundedPrimeGapsOQ03OQ01.lean` (2 axioms).

A prior session already **decomposed** the de Polignac / central-binomial derivation
into a clean all-sorry Aristotle target:
`proofs/Proofs/BoundedPrimeGapsOQ03OQ01ChebyshevLowerAristotle.lean` (4 theorem-sorries):
- **L1** `log_factorial_eq_sum_vonMangoldt_mul_div` — Legendre floor-sum identity.
- **L2** `log_centralBinom_le_psi` — the genuine gap `log C(2n,n) ≤ ψ(2n)`.
- **L3** `log_four_le_log_centralBinom` — `n·log4 − log(2n) ≤ log C(2n,n)` (easiest; just
  log of `Nat.four_pow_le_two_mul_self_mul_centralBinom`).
- assembly into `chebyshev_psi_lower_bound`.
The companion header lists verified Mathlib v4.26 hooks (vonMangoldt_sum,
Ioc_filter_dvd_card_eq_div, four_pow_le_two_mul_self_mul_centralBinom, Chebyshev.psi).

## Blocker this session

**Dual blackout** — Docker daemon unresponsive (`docker info` rc=124, load ~26) AND
Aristotle MCP returns `Resource not found` (404). Could not build anything and could not
submit the companion to `prove_file`. No verifiable progress was possible.

## Next action

When Aristotle recovers: `prove_file BoundedPrimeGapsOQ03OQ01ChebyshevLowerAristotle.lean`
(it is self-contained, imports only Mathlib). Then merge the proved L1–L3 + assembly into
`ChebyshevLower.lean`, discharge its `chebyshev_psi_lower_bound` sorry, and that should let
the 2 axioms in `BoundedPrimeGapsOQ03OQ01.lean` become theorems. L3 is also a safe ~10-line
hand proof if Aristotle stays down.
