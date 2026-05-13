/-
Erdős Problem #455 (OQ-04): Arithmetic-Progression Gap Generalization

Parent: `proofs/Proofs/Erdos455Problem.lean` (Erdős #455 — Monotone
Prime Gap Sequences).

Parent's `conclusion.openQuestions[3]`:

> Can the problem be generalized to other arithmetic conditions on
> gaps (e.g., gaps forming an arithmetic progression)?

**Yes**, and we exhibit a concrete length-40 witness: Euler's prime-
generating polynomial `n² + n + 41` produces 40 consecutive primes
with AP-gap common second-difference `d = 2`.

The general structure: for even `d > 0` and `g_0, q_0 ∈ ℕ_{>0}`, the
AP-gap prime sequence is exactly the prime values of the quadratic
polynomial `(d/2) n² + (g_0 - d/2) n + q_0`. The maximum length is
open (Bunyakovsky 1857) — the current record for `d = 2` is **40**.

For `d = 0` (constant gaps), the question reduces to **Green-Tao 2008**
(primes contain arbitrarily long arithmetic progressions). Mathlib has
no Green-Tao at v4.26.0; this scaffold defers the `d = 0` axiomatisation
to a later session and focuses on the `d = 2` Euler witness, which is
sorry-free at the value-level.

References:
* Euler, L. (1772). De numeris primis valde magnis [On very large
  primes]. (`n² + n + 41` first observed.)
* Green, B.; Tao, T. (2008). The primes contain arbitrarily long
  arithmetic progressions. Ann. of Math. 167(2), 481-547.
* Bunyakovsky, V. (1857). Sur les nouveaux théorèmes relatifs à la
  distinction des nombres premiers et à la décomposition des entiers
  en facteurs.
* Hardy, G. H.; Littlewood, J. E. (1923). Some problems of "Partitio
  Numerorum"; III: On the expression of a number as a sum of primes.
  Acta Math. 44, 1-70. (Conjecture F.)

Session: S2 ACT — verbatim transfer from S2 PREP (PR #18540).
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Proofs.Erdos455Problem

namespace Erdos455OQ04

open Erdos455

/-- A sequence has AP-gaps with common second-difference `d : ℤ`. The
signed second difference `q (n+2) - 2·q (n+1) + q n` (coerced to ℤ)
equals `d` for every `n`. -/
def HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop :=
  ∀ n, (q (n + 2) : ℤ) - 2 * (q (n + 1) : ℤ) + (q n : ℤ) = d

/-- An AP-gap prime sequence with common second-difference `d : ℤ`. -/
structure APGapPrimeSeq (d : ℤ) where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  allPrime : ∀ n, (seq n).Prime
  apGaps : HasAPGaps seq d

/-- **Euler's prime-generating polynomial** `n² + n + 41`. Produces
primes for `n = 0, 1, …, 39` (40 values: 41, 43, 47, …, 1601). -/
def eulerPoly : ℕ → ℕ := fun n => n^2 + n + 41

/-- Euler's polynomial has AP-gaps with `d = 2` (its second difference
is the constant `2`). -/
theorem eulerPoly_hasAPGaps : HasAPGaps eulerPoly 2 := by
  intro n
  unfold eulerPoly
  push_cast
  ring

/-- Witness for the parent's `openQuestions[3]`: there exists an
AP-gap prime sequence of length ≥ 40 with `d = 2`. -/
theorem exists_length40_apGapPrimeSeq :
    ∃ q : ℕ → ℕ, HasAPGaps q 2 ∧ ∀ n, n < 40 → (q n).Prime := by
  refine ⟨eulerPoly, eulerPoly_hasAPGaps, ?_⟩
  intro n hn
  interval_cases n <;> (unfold eulerPoly; native_decide)

/-- **Green-Tao 2008** (finitary statement): for every length `k`, there
exists an arithmetic progression `a, a + g, a + 2g, …, a + (k-1) g` of
`k` primes with positive common difference `g`. (B. Green & T. Tao,
*The primes contain arbitrarily long arithmetic progressions*, Annals
of Mathematics 167(2), 481-547, 2008.)

This is taken as an axiom; the original proof is ~30 pages of additive
combinatorics (Szemerédi-regularity + transference principle +
Goldston-Yıldırım sieve), none of which are sufficiently developed in
Mathlib v4.26.0 for a derivation. Mathlib does provide Dirichlet's
theorem (`Mathlib/NumberTheory/LSeries/PrimesInAP.lean`), but that
gives infinitely many primes in a residue class — not `k` consecutive
prime terms in an AP, which is qualitatively much harder.

Small-case sanity: at `k = 5` the witness `(a, g) = (5, 6)` gives the
prime AP `5, 11, 17, 23, 29` (independently certified by
`exists_apGap_zero_length_5_witness` below, sorry-free and axiom-free). -/
axiom greenTao_finitary :
    ∀ k : ℕ, ∃ a g : ℕ, 0 < g ∧ ∀ n, n < k → Nat.Prime (a + n * g)

/-- Bridge: Green-Tao produces a `HasAPGaps`-shaped finitary witness
for `d = 0`. Note that `APGapPrimeSeq 0` is **not** instantiable (any
`ℕ → ℕ` with second-difference 0 is linear, and no infinite AP of
primes exists), so this is the finitary analogue of
`exists_length40_apGapPrimeSeq` rather than a full `APGapPrimeSeq 0`. -/
theorem exists_apGap_zero_of_length (k : ℕ) :
    ∃ q : ℕ → ℕ, HasAPGaps q 0 ∧ ∀ n, n < k → (q n).Prime := by
  obtain ⟨a, g, _hg, hp⟩ := greenTao_finitary k
  refine ⟨fun n => a + n * g, ?_, hp⟩
  intro n
  push_cast
  ring

/-- Concrete `k = 5` witness for the Green-Tao finitary statement:
`5, 11, 17, 23, 29` is an arithmetic progression of 5 primes with
common difference 6. Sorry-free **and** axiom-free; independent of
`greenTao_finitary`. -/
theorem exists_apGap_zero_length_5_witness :
    ∃ a g : ℕ, 0 < g ∧ ∀ n, n < 5 → Nat.Prime (a + n * g) := by
  refine ⟨5, 6, by decide, ?_⟩
  intro n hn
  interval_cases n <;> decide

end Erdos455OQ04
