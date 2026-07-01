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

/-- **Bunyakovsky 1857** (finitary AP-gap quadratic specialization). For
every length `k` and every common second-difference `d : ℤ` with `0 < d`,
there exists a strictly-monotone sequence `q : ℕ → ℕ` whose first `k`
entries are prime and whose AP-gaps equal `d`.

This is conjectural; the full Bunyakovsky conjecture is open since 1857
(unproved even for the simplest non-linear case `f(n) = n² + 1`). It is
epistemically distinct from `greenTao_finitary` — Green-Tao (d = 0) was
proved in 2008, whereas Bunyakovsky (d > 0) remains an open conjecture.
Kept as a separate axiom to preserve provenance per
`feedback_researcher_axiom_integrity_policy`.

References:
- Bunyakovsky, V. (1857). Sur les nouveaux théorèmes relatifs à la
  distinction des nombres premiers et à la décomposition des entiers
  en facteurs.
- Hardy, G. H.; Littlewood, J. E. (1923). Some problems of "Partitio
  Numerorum"; III: On the expression of a number as a sum of primes.
  Acta Math. 44, 1-70. (Conjecture F.)
- Bateman, P. T.; Horn, R. A. (1962). A heuristic asymptotic formula
  concerning the distribution of prime numbers. Math. Comp. 16, 363-367. -/
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d

/-- Bridge: Bunyakovsky produces an AP-gap prime prefix for any `d > 0`.

This is a direct restatement of `bunyakovsky_finitary` (no `obtain`
unpacking needed because the F5 axiom signature directly produces the
desired tuple). The asymmetry with `exists_apGap_zero_of_length`
(d = 0 bridge, which DOES use `obtain` + `push_cast; ring`) reflects the
deliberate choice to axiomatize d > 0 in predicate (F5) form rather than
raw-triple (F1) form: the F5 form sidesteps the `ℤ`-cast bookkeeping
that an F1 form would require for the quadratic
`q n = q₀ + n * g₀ + (n * (n - 1) / 2) * d.toNat`. -/
theorem exists_apGapPrimeSeq_of_length_d_pos
    (k : ℕ) (d : ℤ) (hd : 0 < d) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n, n < k → (q n).Prime) ∧ HasAPGaps q d :=
  bunyakovsky_finitary k d hd

/-! ## Structural theory of AP-gap sequences (verified, axiom-free)

The witnesses above are conditional on Green-Tao / Bunyakovsky, but the *shape*
of any `HasAPGaps q d` sequence is unconditional: the second-difference condition
is a linear recurrence, so the first gaps form an arithmetic progression and `q`
itself is a quadratic. This section proves that closed structure — no primality,
no axioms — pinning down the inclusion chain from `problem.md`:

  `ConstantGap (d = 0) ⊊ APGap_{d>0} ⊊ MonotoneGap`.

The `d ≥ 0 ⟹ non-decreasing gaps` step (`apGap_gaps_monotone`) is exactly the
inclusion `APGap_{d ≥ 0} ⊆ MonotoneGap` into the parent `erdos-455` condition. -/

/-- **Gaps of an AP-gap sequence form an arithmetic progression.** The consecutive
gap `q (n+1) - q n` is the linear function `(q 1 - q 0) + n · d` of `n`. This is the
first integral of the second-difference recurrence `HasAPGaps`. -/
theorem apGap_gap_linear {q : ℕ → ℕ} {d : ℤ} (h : HasAPGaps q d) :
    ∀ n : ℕ, (q (n + 1) : ℤ) - (q n : ℤ) = ((q 1 : ℤ) - (q 0 : ℤ)) + (n : ℤ) * d := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have hh := h m
    rw [show m + 1 + 1 = m + 2 from rfl]
    push_cast
    push_cast at ih
    linear_combination ih + hh

/-- **`d = 0` ⟺ constant gaps (primes in arithmetic progression).** When the common
second-difference is `0`, every gap equals the first gap `q 1 - q 0`, i.e. the terms
themselves are in arithmetic progression — the Green-Tao specialization. -/
theorem apGap_zero_gaps_constant {q : ℕ → ℕ} (h : HasAPGaps q 0) (n : ℕ) :
    (q (n + 1) : ℤ) - (q n : ℤ) = (q 1 : ℤ) - (q 0 : ℤ) := by
  rw [apGap_gap_linear h n]; ring

/-- **`d ≥ 0` ⟹ non-decreasing gaps.** For a non-negative common difference the gap
sequence is monotone, so an `APGap_{d ≥ 0}` sequence satisfies the parent `erdos-455`
monotone-gap condition. This is the inclusion `APGap_{d ≥ 0} ⊆ MonotoneGap`. -/
theorem apGap_gaps_monotone {q : ℕ → ℕ} {d : ℤ} (h : HasAPGaps q d) (hd : 0 ≤ d)
    {m n : ℕ} (hmn : m ≤ n) :
    (q (m + 1) : ℤ) - (q m : ℤ) ≤ (q (n + 1) : ℤ) - (q n : ℤ) := by
  rw [apGap_gap_linear h m, apGap_gap_linear h n]
  have hmn' : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ (n : ℤ) - (m : ℤ)) hd]

/-- **Closed form: an AP-gap sequence is quadratic.** Summing the linear gap
(`apGap_gap_linear`) telescopes to `q n = q 0 + n·(q 1 - q 0) + \binom{n}{2}·d`.
Stated doubled to keep everything over `ℤ` without division:
`2·q n = 2·q 0 + 2n·(q 1 - q 0) + n(n-1)·d`. With `d = 2` and `q 0 = 41, q 1 = 43`
this is exactly Euler's `n² + n + 41`. -/
theorem apGap_closed_form {q : ℕ → ℕ} {d : ℤ} (h : HasAPGaps q d) :
    ∀ n : ℕ, 2 * (q n : ℤ) =
      2 * (q 0 : ℤ) + 2 * (n : ℤ) * ((q 1 : ℤ) - (q 0 : ℤ)) + (n : ℤ) * ((n : ℤ) - 1) * d := by
  intro n
  induction n with
  | zero => simp
  | succ m ih =>
    have hgap := apGap_gap_linear h m
    push_cast
    push_cast at ih
    linear_combination ih + 2 * hgap

/-- Sanity check that the closed form reproduces Euler's polynomial: for the AP-gap
sequence `eulerPoly` (`d = 2`, `q 0 = 41`, `q 1 = 43`), the closed form gives
`2·(n² + n + 41)`. -/
theorem eulerPoly_closed_form (n : ℕ) :
    2 * (eulerPoly n : ℤ) =
      2 * (eulerPoly 0 : ℤ) + 2 * (n : ℤ) * ((eulerPoly 1 : ℤ) - (eulerPoly 0 : ℤ))
        + (n : ℤ) * ((n : ℤ) - 1) * 2 :=
  apGap_closed_form eulerPoly_hasAPGaps n

end Erdos455OQ04
