import Mathlib
import Proofs.CatalanNumbersOQ01OQ04

/-
# Strict log-concavity of the reciprocal Catalan sequence `1/Cₙ`

This is the leaf `oq-01-oq-04-oq-02` of `catalan-numbers-oq-01`, a companion to the
parent `oq-01-oq-04`, which proves the **strict log-convexity** (Turán inequality)
of the Catalan numbers:

  `catalan_turan : catalan (n+1) ^ 2 < catalan n * catalan (n+2)`.

## The mathematical content, and an honest correction

The open question asks for a **derived** Catalan sequence `aₙ` that is strictly
*log-concave*, `aₙ² > aₙ₋₁·aₙ₊₁`, and suggests `aₙ = Cₙ/(n+1)` as a candidate.
That candidate is **false**: `n ↦ Cₙ/(n+1)` is *not* log-concave. Already at
`n = 1`,

  `a₁² = (C₁/2)² = 1/4`,   `a₀·a₂ = (C₀/1)(C₂/3) = 2/3`,   and `1/4 < 2/3`,

so `a₁² > a₀·a₂` **fails** (`catalanOverSucc_not_logConcave_at_one`). The reason is
structural: the Catalan numbers themselves are strictly log-*convex*, and dividing by
the mildly-growing `n+1` does not reverse that.

The correct, canonical derived sequence that *is* strictly log-concave is the
**reciprocal** `aₙ = 1/Cₙ`. Indeed, for any strictly positive strictly log-convex
sequence the pointwise reciprocal is strictly log-concave — reciprocation is an
order-reversing multiplicative involution on the positive reals — and this instance
is *exactly* the parent's Turán inequality read through `x ↦ 1/x`:

  `(1/Cₙ)² > (1/Cₙ₋₁)(1/Cₙ₊₁)  ⟺  Cₙ² < Cₙ₋₁·Cₙ₊₁`.

## What is proved

* `recip_sq_gt_of_sq_lt` — the general pointwise principle: in a `LinearOrderedField`,
  if `0 < x, y, z` and `y² < x·z` then `(1/y)² > (1/x)·(1/z)`.
* `catalan_recip_logConcave` — its Catalan instance for every `n`:
  `(1/catalan (n+1))² > (1/catalan n)·(1/catalan (n+2))` over `ℚ`.
* `catalan_recip_logConcave_shift` — the same stated in the standard log-concavity
  indexing `aₙ² > aₙ₋₁·aₙ₊₁` for `n ≥ 1`.
* `catalanOverSucc_not_logConcave_at_one` — the counterexample refuting the suggested
  candidate `Cₙ/(n+1)`.

Mathlib has the Catalan API but neither the Turán inequality (supplied by the parent)
nor this reciprocal log-concavity.
-/

namespace CatalanNumbersOQ01OQ04OQ02

open Nat CatalanNumbersOQ01OQ04

/-- **Reciprocation turns a strict Turán (log-convexity) step into a strict
log-concavity step.** In any linearly ordered field, if `x, y, z` are positive and
`y² < x · z`, then the reciprocals satisfy `(1/x)·(1/z) < (1/y)²`. Purely the fact
that `t ↦ 1/t` is strictly antitone and multiplicative on the positive cone. -/
theorem recip_sq_gt_of_sq_lt {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x y z : K} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : y ^ 2 < x * z) :
    (1 / x) * (1 / z) < (1 / y) ^ 2 := by
  have hy2 : (0 : K) < y ^ 2 := by positivity
  have hxz : (0 : K) < x * z := by positivity
  -- `(1/y)^2 = 1/y^2` and `(1/x)*(1/z) = 1/(x*z)`; reciprocal reverses `y^2 < x*z`.
  rw [div_pow, one_pow, div_mul_div_comm, one_mul]
  exact one_div_lt_one_div_of_lt hy2 h

/-- **Strict log-concavity of the reciprocal Catalan sequence.** For every `n`,

  `(1 / catalan (n+1))² > (1 / catalan n) · (1 / catalan (n+2))`   over `ℚ`,

obtained by reciprocating the parent's strict Turán inequality
`catalan (n+1)² < catalan n · catalan (n+2)`. -/
theorem catalan_recip_logConcave (n : ℕ) :
    (1 / (catalan n : ℚ)) * (1 / (catalan (n + 2) : ℚ))
      < (1 / (catalan (n + 1) : ℚ)) ^ 2 := by
  have hA : (0 : ℚ) < catalan n := by exact_mod_cast catalan_pos n
  have hB : (0 : ℚ) < catalan (n + 1) := by exact_mod_cast catalan_pos (n + 1)
  have hC : (0 : ℚ) < catalan (n + 2) := by exact_mod_cast catalan_pos (n + 2)
  have hT : (catalan (n + 1) : ℚ) ^ 2 < (catalan n : ℚ) * (catalan (n + 2) : ℚ) := by
    exact_mod_cast catalan_turan n
  exact recip_sq_gt_of_sq_lt hA hB hC hT

/-- **Reciprocal Catalan log-concavity in standard indexing.** Writing
`a n = 1 / catalan n`, for every `n ≥ 1`

  `a n ^ 2 > a (n-1) * a (n+1)`,

the defining strict log-concavity inequality. (This is `catalan_recip_logConcave`
reindexed at `n = m + 1`.) -/
theorem catalan_recip_logConcave_shift (n : ℕ) (hn : 1 ≤ n) :
    (1 / (catalan (n - 1) : ℚ)) * (1 / (catalan (n + 1) : ℚ))
      < (1 / (catalan n : ℚ)) ^ 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [Nat.zero_add, Nat.add_sub_cancel]
  have h := catalan_recip_logConcave m
  -- `m + 1 + 1 = m + 2`
  simpa [Nat.add_assoc] using h

/-- **The suggested candidate `Cₙ/(n+1)` is NOT log-concave.** With
`a n = catalan n / (n + 1)`, the log-concavity inequality `a 1 ^ 2 > a 0 * a 2`
already **fails** at `n = 1`: `a 1 ^ 2 = 1/4` while `a 0 * a 2 = 2/3`, and
`1/4 < 2/3`. This refutes the open question's proposed example and is the reason the
reciprocal sequence, not `Cₙ/(n+1)`, is the correct log-concave derived sequence. -/
theorem catalanOverSucc_not_logConcave_at_one :
    ¬ (((catalan 1 : ℚ) / (1 + 1)) ^ 2
        > ((catalan 0 : ℚ) / (0 + 1)) * ((catalan 2 : ℚ) / (2 + 1))) := by
  rw [catalan_zero, catalan_one, catalan_two]
  norm_num

end CatalanNumbersOQ01OQ04OQ02
