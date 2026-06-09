# Knowledge Base: infinitude-primes-4k1-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-01 asks for the full biconditional Fermat two-squares characterization
for odd primes, framed as a strengthening of the gallery's
`infinitude-primes-4k1` proof. The S1 author surveyed
`Mathlib.NumberTheory.SumTwoSquares`, identified `Nat.Prime.sq_add_sq` as
the right bearer, and S2 shipped an 84-LOC wrapper file
`InfinitudePrimes4k1OQ01.lean` proving:

  `p odd prime → p ≠ 2 → (p % 4 = 1 ↔ ∃ a b : ℕ, p = a² + b²)`

with 0 axioms and 0 sorries.

---

## Insights

- **The gallery already had a strictly stronger proof of the same theorem.**
  `proofs/Proofs/FermatTwoSquares.lean` (gallery slug `fermat-two-squares`,
  Wiedijk #20) proves `(∃ a b, a² + b² = p) ↔ p % 4 ≠ 3` for any prime
  `p`, plus 5 supporting theorems (`one_mod_four_is_sum_of_squares`,
  `two_is_sum_of_squares`, `three_mod_four_not_sum_of_squares`,
  `prime_classification`, `sum_of_squares_classification`) and named
  examples for `p ∈ {5, 13, 17, 29, 37, 41}`. Same Mathlib bearer
  (`Nat.Prime.sq_add_sq`), same `interval_cases (n % 4) <;>` proof
  technique. So OQ-01's S2 file is a small odd-prime-only restriction of
  an existing gallery proof — pedagogically valid but mathematically
  redundant.

- **The `infinitude-primes-4k1/meta.json` open question §0 is the same
  question OQ-01 asks.** That openQuestion is already answered by
  `fermat-two-squares`. The OQ-01 slug was spun off without checking
  whether the gallery already covered it.

- **Lesson for future open-question generation**: before claiming/spinning
  a new "open question" slug from a gallery proof, search both
  `proofs/Proofs/<Topic>*.lean` AND `src/data/proofs/<topic>-*` for an
  existing proof of the precise statement under any related slug. A one-shot
  `glob src/data/proofs/fermat-*` would have caught this duplication at
  problem-creation time (2026-04-12).

- **Mathlib bearer reuse pattern**: both files use `Nat.Prime.sq_add_sq`
  at `Mathlib/NumberTheory/SumTwoSquares.lean:35` (pinned at lake SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). The `interval_cases (n % 4)`
  + `Nat.pow_mod` case-analysis for the easy direction (squares mod 4 are
  0 or 1) is the canonical Mathlib-style proof — both files independently
  reach the same pattern.

---

## Dead Ends

- **Creating a separate `src/data/proofs/infinitude-primes-4k1-oq-01/`
  gallery entry**: would duplicate the existing `fermat-two-squares`
  entry. The canonical gallery home for this theorem is
  `src/data/proofs/fermat-two-squares/`. The OQ-01 slug should be closed
  as `completed`, not via a separate enricher artifact.

- **Re-opening the slug as a new open question**: the biconditional is
  proved both in OQ-01's S2 wrapper and (more comprehensively) in
  `FermatTwoSquares.lean`. No mathematical content remains to extract.
  Adjacent open questions (Gaussian integer splitting, explicit witness
  extraction algorithms, density 1/2 statement, Dirichlet density) would
  warrant their own slugs, not a respin of OQ-01.

---

## Bearer pin

| Symbol | Location | Lake SHA |
|---|---|---|
| `Nat.Prime.sq_add_sq` | `Mathlib/NumberTheory/SumTwoSquares.lean:35` | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |

Drift from S1 (2026-05-30) through S4 (2026-06-09) = 0 commits (lake-pinned
manifest unchanged across 10 days).
