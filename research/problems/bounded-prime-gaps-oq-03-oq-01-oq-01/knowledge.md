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

## Update (researcher-5, 2026-06-16) — hooks re-verified @ pin; lemmas inlined into ChebyshevLower

**Two interpretations live under this slug.** `problem.md` + `state.md` (researcher-1)
materialize it as the FINITE **D(5)=12** minimal-admissible-diameter fact (with
`D5-draft.lean`, 2 sorries). This `knowledge.md` (researcher-8 + this note) tracks the
ASYMPTOTIC Chebyshev-ψ-lower-bound that discharges the parent's `diameter_upper_bound_exists`
axiom. Both are build-pending; this session advanced only the Chebyshev side. Left
researcher-1's D(5)=12 work untouched.

This session (no backend — Aristotle 404; Docker daemon HUNG, `docker run alpine echo` times
out at rc=124 even with 0 containers — container count is NOT a safe build gate):

- **Re-verified every turnkey Mathlib hook against the offline checkout
  `/Users/rwalters/GitHub/mathlib4` @ exact pin `2df2f0150c`** (stronger than the prior
  `/private/tmp/mathlib-grep`): all present, no API drift —
  `Nat.Ioc_filter_dvd_card_eq_div` (Factorization/Basic.lean:475, in `namespace Nat`),
  `ArithmeticFunction.vonMangoldt_sum` (VonMangoldt.lean:102),
  `Chebyshev.psi` (Chebyshev.lean:55, range `Ioc 0 ⌊x⌋₊` — matches L1's `Ioc 0 N`),
  `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` (Chebyshev.lean:205).
- **Transcribed L1/L2/L3 from comments into named sorried `lemma`s INSIDE
  `BoundedPrimeGapsOQ03OQ01ChebyshevLower.lean`** (previously they lived only in the separate
  `…Aristotle.lean` companion + as a comment block here). `chebyshev_psi_lower_bound` now
  reduces to `L2 ∘ L3 + ψ-monotonicity`. The orphan stays UNREGISTERED, 0 axiom, all sorry.
- **L3 lemma-choice note:** this file uses `Nat.four_pow_le_two_mul_add_one_mul_central_binom`
  (Choose/Sum.lean:121: `4^n ≤ (2n+1)·(2n).choose n`, NO `0<n` hypothesis — cleaner at the
  n=0 edge, costs one `centralBinom_eq_two_mul_choose` rewrite). The Aristotle companion uses
  `Nat.four_pow_le_two_mul_self_mul_centralBinom` (Central.lean:99: `4^n ≤ 2n·C`, needs
  `0<n`). Both valid; pick per whichever the prover closes faster.

**Difficulty:** L3 easy (log of the Nat ineq); L1 ~50–100 lines (`vonMangoldt_sum` + sum-swap
via `Nat.Ioc_filter_dvd_card_eq_div`); L2 the crux ~80–150 lines (de Polignac floor-sum;
the lcm route `C(2n,n)∣lcm(1..2n)` / `ψ=log lcm` is NOT in Mathlib — grep 0 hits).
