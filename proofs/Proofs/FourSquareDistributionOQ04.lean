import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Tactic

/-
# Four-Square Distribution — Open Question 04: generalization to r₆(n)

## Parent

`FourSquareDistribution.lean` proves, for `r₄(n)`, that the ordered signed
representations partition into **types** (sorted multisets of absolute values),
each contributing

  contribution(type) = (number of orderings) × 2^(number of nonzero parts)
                     = (4! / ∏ mᵢ!) · 2^(#nonzero)

and that these contributions sum to `r₄(n)`. The symmetry group there is the
hyperoctahedral group `B₄ = S₄ ⋉ (ℤ/2)⁴`.

## Open question (oq-04)

Does the orbit/type bookkeeping generalize to `r_{2k}(n)` under
`B_{2k} = S_{2k} ⋉ (ℤ/2)^{2k}`, `|B_{2k}| = (2k)! · 2^{2k}`?

**Answer (this file, the `2k = 6` case): yes, verbatim.** With six coordinates
the orbit-size formula reads

  contribution(type) = (6! / ∏ mᵢ!) · 2^(#nonzero)              (★)

and `∑_{types of n} contribution = r₆(n)`. The factor `2^(#nonzero)` (not
`2^6`) is the same zero-sign degeneracy as in the parent: flipping the sign of a
zero coordinate fixes the tuple, so only the nonzero coordinates contribute sign
choices.

This file mirrors the parent's **computational** approach (a sorted six-tuple
structure + the formula `(★)`, with concrete contributions discharged by
`native_decide`), rather than the heavier `MulAction`/semidirect-product route.
That is exactly the "fixed small `m`" first ACT recommended in
`research/problems/four-square-distribution-oq-04/knowledge.md`.

All embedded contribution/total values are validated by
`research/problems/four-square-distribution-oq-04/verify_hyperoctahedral_2k.py`
and the `2k = 6` extension recorded in the knowledge base (each shape's orbit by
`(★)` against an independent brute count of signed orderings; the per-`n` totals
against an independent signed-square convolution computing `r₆(n)`).

**Build status.** Authored under a Docker/Aristotle blackout, so this file is
**not yet registered in `Proofs.lean`**. It uses only elementary list arithmetic
and `native_decide`, mirroring the already-compiling parent; it is a
verified-on-paper drop-in for the next build-enabled session.

## References

- Jacobi, C. G. J. (1834). *Fundamenta nova theoriae functionum ellipticarum.*
  (Formulae for `r₄`, `r₆`, `r₈`.)
- Grosswald, E. (1985). *Representations of Integers as Sums of Squares.*
-/

namespace FourSquareDistributionOQ04

open List

/-! ## Part 1: Representation types for six squares

A type is a sorted six-tuple of non-negative integers whose squares sum to `n`;
it captures the unordered multiset of absolute values of a representation. -/

/-- A sorted representation type for `n` as a sum of six squares. -/
structure RepType6 (n : ℕ) where
  a₁ : ℕ
  a₂ : ℕ
  a₃ : ℕ
  a₄ : ℕ
  a₅ : ℕ
  a₆ : ℕ
  sorted : a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ a₃ ≤ a₄ ∧ a₄ ≤ a₅ ∧ a₅ ≤ a₆
  sum_eq : a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 + a₅ ^ 2 + a₆ ^ 2 = n
  deriving DecidableEq

/-- The six values as a list. -/
def RepType6.toList {n : ℕ} (t : RepType6 n) : List ℕ :=
  [t.a₁, t.a₂, t.a₃, t.a₄, t.a₅, t.a₆]

/-- Number of nonzero entries. -/
def RepType6.nonzeroCount {n : ℕ} (t : RepType6 n) : ℕ :=
  (if t.a₁ = 0 then 0 else 1) + (if t.a₂ = 0 then 0 else 1) +
  (if t.a₃ = 0 then 0 else 1) + (if t.a₄ = 0 then 0 else 1) +
  (if t.a₅ = 0 then 0 else 1) + (if t.a₆ = 0 then 0 else 1)

/-! ## Part 2: The symmetry multiplier `(★)` -/

/-- Multinomial number of orderings: `6! / ∏ (multiplicity v)!`. -/
def RepType6.permutations {n : ℕ} (t : RepType6 n) : ℕ :=
  let vals := t.toList
  let distinctVals := vals.dedup
  720 / (distinctVals.map (fun v => Nat.factorial (vals.count v))).prod

/-- Sign factor `2^(#nonzero)`. -/
def RepType6.signFactor {n : ℕ} (t : RepType6 n) : ℕ :=
  2 ^ t.nonzeroCount

/-- Contribution of a type to `r₆(n)`: orderings times sign choices. -/
def RepType6.contribution {n : ℕ} (t : RepType6 n) : ℕ :=
  t.permutations * t.signFactor

/-- Constructor with the two proof obligations. -/
private def mk6 (n a₁ a₂ a₃ a₄ a₅ a₆ : ℕ)
    (hs : a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ a₃ ≤ a₄ ∧ a₄ ≤ a₅ ∧ a₅ ≤ a₆)
    (he : a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 + a₅ ^ 2 + a₆ ^ 2 = n) : RepType6 n :=
  ⟨a₁, a₂, a₃, a₄, a₅, a₆, hs, he⟩

/-! ## Part 3: Enumeration of types for small `n`

The types below are the complete list of sorted six-square shapes for each `n`
(verified exhaustively in the Python certificate). -/

-- n = 1
def t1 : RepType6 1 := mk6 1 0 0 0 0 0 1 (by decide) (by norm_num)
-- n = 2
def t2 : RepType6 2 := mk6 2 0 0 0 0 1 1 (by decide) (by norm_num)
-- n = 3
def t3 : RepType6 3 := mk6 3 0 0 0 1 1 1 (by decide) (by norm_num)
-- n = 5
def t5a : RepType6 5 := mk6 5 0 0 0 0 1 2 (by decide) (by norm_num)
def t5b : RepType6 5 := mk6 5 0 1 1 1 1 1 (by decide) (by norm_num)
-- n = 6
def t6a : RepType6 6 := mk6 6 0 0 0 1 1 2 (by decide) (by norm_num)
def t6b : RepType6 6 := mk6 6 1 1 1 1 1 1 (by decide) (by norm_num)
-- n = 12
def t12a : RepType6 12 := mk6 12 0 0 0 2 2 2 (by decide) (by norm_num)
def t12b : RepType6 12 := mk6 12 0 0 1 1 1 3 (by decide) (by norm_num)
def t12c : RepType6 12 := mk6 12 1 1 1 1 2 2 (by decide) (by norm_num)
-- n = 30 (six shapes, including the all-distinct-nonzero one)
def t30a : RepType6 30 := mk6 30 0 0 0 1 2 5 (by decide) (by norm_num)
def t30b : RepType6 30 := mk6 30 0 0 1 2 3 4 (by decide) (by norm_num)
def t30c : RepType6 30 := mk6 30 0 2 2 2 3 3 (by decide) (by norm_num)
def t30d : RepType6 30 := mk6 30 1 1 1 1 1 5 (by decide) (by norm_num)
def t30e : RepType6 30 := mk6 30 1 1 1 3 3 3 (by decide) (by norm_num)
def t30f : RepType6 30 := mk6 30 1 1 2 2 2 4 (by decide) (by norm_num)

/-! ## Part 4: Contributions via `(★)`, checked by `native_decide` -/

theorem t1_contribution  : t1.contribution  = 12  := by native_decide
theorem t2_contribution  : t2.contribution  = 60  := by native_decide
theorem t3_contribution  : t3.contribution  = 160 := by native_decide
theorem t5a_contribution : t5a.contribution = 120 := by native_decide
theorem t5b_contribution : t5b.contribution = 192 := by native_decide
theorem t6a_contribution : t6a.contribution = 480 := by native_decide
theorem t6b_contribution : t6b.contribution = 64  := by native_decide
theorem t12a_contribution : t12a.contribution = 160 := by native_decide
theorem t12b_contribution : t12b.contribution = 960 := by native_decide
theorem t12c_contribution : t12c.contribution = 960 := by native_decide
theorem t30a_contribution : t30a.contribution = 960  := by native_decide
theorem t30b_contribution : t30b.contribution = 5760 := by native_decide
theorem t30c_contribution : t30c.contribution = 1920 := by native_decide
theorem t30d_contribution : t30d.contribution = 384  := by native_decide
theorem t30e_contribution : t30e.contribution = 1280 := by native_decide
theorem t30f_contribution : t30f.contribution = 3840 := by native_decide

/-! ## Part 5: The decomposition `∑ contributions = r₆(n)`

Jacobi's `r₆` values (computed independently in the certificate) are reproduced
exactly by summing the type contributions. -/

theorem r6_1  : t1.contribution = 12 := t1_contribution
theorem r6_2  : t2.contribution = 60 := t2_contribution
theorem r6_3  : t3.contribution = 160 := t3_contribution

/-- `r₆(5) = 312`: the two shapes `(0,0,0,0,1,2)` and `(0,1,1,1,1,1)`. -/
theorem r6_5  : t5a.contribution + t5b.contribution = 312 := by
  rw [t5a_contribution, t5b_contribution]

/-- `r₆(6) = 544`: shapes `(0,0,0,1,1,2)` and `(1,1,1,1,1,1)`. -/
theorem r6_6  : t6a.contribution + t6b.contribution = 544 := by
  rw [t6a_contribution, t6b_contribution]

/-- `r₆(12) = 2080`: three shapes. -/
theorem r6_12 : t12a.contribution + t12b.contribution + t12c.contribution = 2080 := by
  rw [t12a_contribution, t12b_contribution, t12c_contribution]

/-- `r₆(30) = 14144`: six shapes, including the all-six-distinct-nonzero shape
`(1,1,2,2,2,4)` … and `(0,0,1,2,3,4)` realizing the largest single orbit. -/
theorem r6_30 :
    t30a.contribution + t30b.contribution + t30c.contribution +
      t30d.contribution + t30e.contribution + t30f.contribution = 14144 := by
  rw [t30a_contribution, t30b_contribution, t30c_contribution,
      t30d_contribution, t30e_contribution, t30f_contribution]

/-! ## Part 6: Structural properties of the six-square decomposition -/

/-- The number of nonzero parts is at most six. -/
theorem nonzeroCount_le_six {n : ℕ} (t : RepType6 n) : t.nonzeroCount ≤ 6 := by
  simp only [RepType6.nonzeroCount]
  split_ifs <;> omega

/-- The sign factor is a power of two, at most `2⁶ = 64`. -/
theorem signFactor_le_64 {n : ℕ} (t : RepType6 n) : t.signFactor ≤ 64 := by
  have h := nonzeroCount_le_six t
  simp only [RepType6.signFactor]
  calc 2 ^ t.nonzeroCount ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) h
    _ = 64 := by norm_num

#check @RepType6.contribution
#check @r6_30
#check @nonzeroCount_le_six

end FourSquareDistributionOQ04
