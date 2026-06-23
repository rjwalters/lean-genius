import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Tactic

/-
# Four-Square Distribution — Open Question 04: generalization to r₈(n)

## Parent and sibling

`FourSquareDistribution.lean` proves, for `r₄(n)`, that the ordered signed
representations partition into **types** (sorted multisets of absolute values),
each contributing

  contribution(type) = (number of orderings) × 2^(number of nonzero parts)
                     = (4! / ∏ mᵢ!) · 2^(#nonzero).

`FourSquareDistributionOQ04.lean` carries this out for `r₆(n)` (the `2k = 6`
case). This file does the **`2k = 8` case**, the example singled out in the open
question: `|B₈| = 8! · 2⁸ = 10 321 920`.

## Open question (oq-04)

Does the orbit/type bookkeeping generalize to `r_{2k}(n)` under
`B_{2k} = S_{2k} ⋉ (ℤ/2)^{2k}`, `|B_{2k}| = (2k)! · 2^{2k}`?

**Answer (this file, the `2k = 8` case): yes, verbatim.** With eight coordinates
the orbit-size formula reads

  contribution(type) = (8! / ∏ mᵢ!) · 2^(#nonzero)              (★)

and `∑_{types of n} contribution = r₈(n)`. As in the parent, the factor
`2^(#nonzero)` (not `2⁸`) is the zero-sign degeneracy: flipping the sign of a
zero coordinate fixes the tuple, so only the nonzero coordinates contribute sign
choices. The all-equal-nonzero shape `(1,1,1,1,1,1,1,1)` at `n = 8` contributes
exactly `8!/8! · 2⁸ = 2⁸ = 256`; the all-distinct-nonzero shape would contribute
the full `8! · 2⁸ = |B₈|` (its smallest realization is `n = 1²+⋯+8² = 204`, not
tabulated here).

This file mirrors the parent's **computational** approach (a sorted eight-tuple
structure + the formula `(★)`, with concrete contributions discharged by
`native_decide`), rather than the heavier `MulAction`/semidirect-product route.
That is exactly the "fixed small `m`" ACT recommended in
`research/problems/four-square-distribution-oq-04/knowledge.md`; with the `2k = 6`
case already formalized, this completes `{4, 6, 8}`.

All embedded contribution/total values are validated by
`research/problems/four-square-distribution-oq-04/verify_r8_decomposition.py`
(each shape's orbit by `(★)` against an independent brute count of signed
orderings; the per-`n` totals against an independent signed-square convolution
computing `r₈(n)`) and by `verify_hyperoctahedral_2k.py` (which covers
`2k ∈ {2,4,6,8}`).

**Build status.** Authored under a Docker/Aristotle blackout, so this file is
**not yet registered in `Proofs.lean`**. It uses only elementary list arithmetic
and `native_decide`, mirroring the already-compiling parent and the `2k = 6`
sibling; it is a verified-on-paper drop-in for the next build-enabled session.

## References

- Jacobi, C. G. J. (1834). *Fundamenta nova theoriae functionum ellipticarum.*
  (Formula `r₈(n) = 16 σ₃*(n)`.)
- Grosswald, E. (1985). *Representations of Integers as Sums of Squares.*
-/

namespace FourSquareDistributionOQ04M8

open List

/-! ## Part 1: Representation types for eight squares

A type is a sorted eight-tuple of non-negative integers whose squares sum to
`n`; it captures the unordered multiset of absolute values of a representation. -/

/-- A sorted representation type for `n` as a sum of eight squares. -/
structure RepType8 (n : ℕ) where
  a₁ : ℕ
  a₂ : ℕ
  a₃ : ℕ
  a₄ : ℕ
  a₅ : ℕ
  a₆ : ℕ
  a₇ : ℕ
  a₈ : ℕ
  sorted : a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ a₃ ≤ a₄ ∧ a₄ ≤ a₅ ∧ a₅ ≤ a₆ ∧ a₆ ≤ a₇ ∧ a₇ ≤ a₈
  sum_eq : a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 + a₅ ^ 2 + a₆ ^ 2 + a₇ ^ 2 + a₈ ^ 2 = n
  deriving DecidableEq

/-- The eight values as a list. -/
def RepType8.toList {n : ℕ} (t : RepType8 n) : List ℕ :=
  [t.a₁, t.a₂, t.a₃, t.a₄, t.a₅, t.a₆, t.a₇, t.a₈]

/-- Number of nonzero entries. -/
def RepType8.nonzeroCount {n : ℕ} (t : RepType8 n) : ℕ :=
  (if t.a₁ = 0 then 0 else 1) + (if t.a₂ = 0 then 0 else 1) +
  (if t.a₃ = 0 then 0 else 1) + (if t.a₄ = 0 then 0 else 1) +
  (if t.a₅ = 0 then 0 else 1) + (if t.a₆ = 0 then 0 else 1) +
  (if t.a₇ = 0 then 0 else 1) + (if t.a₈ = 0 then 0 else 1)

/-! ## Part 2: The symmetry multiplier `(★)` -/

/-- Multinomial number of orderings: `8! / ∏ (multiplicity v)!`. -/
def RepType8.permutations {n : ℕ} (t : RepType8 n) : ℕ :=
  let vals := t.toList
  let distinctVals := vals.dedup
  40320 / (distinctVals.map (fun v => Nat.factorial (vals.count v))).prod

/-- Sign factor `2^(#nonzero)`. -/
def RepType8.signFactor {n : ℕ} (t : RepType8 n) : ℕ :=
  2 ^ t.nonzeroCount

/-- Contribution of a type to `r₈(n)`: orderings times sign choices. -/
def RepType8.contribution {n : ℕ} (t : RepType8 n) : ℕ :=
  t.permutations * t.signFactor

/-- Constructor with the two proof obligations. -/
private def mk8 (n a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : ℕ)
    (hs : a₁ ≤ a₂ ∧ a₂ ≤ a₃ ∧ a₃ ≤ a₄ ∧ a₄ ≤ a₅ ∧ a₅ ≤ a₆ ∧ a₆ ≤ a₇ ∧ a₇ ≤ a₈)
    (he : a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2 + a₅ ^ 2 + a₆ ^ 2 + a₇ ^ 2 + a₈ ^ 2 = n) :
    RepType8 n :=
  ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈, hs, he⟩

/-! ## Part 3: Enumeration of types for small `n`

The types below are the complete list of sorted eight-square shapes for each `n`
(verified exhaustively in the Python certificate). -/

-- n = 1
def t1 : RepType8 1 := mk8 1 0 0 0 0 0 0 0 1 (by decide) (by norm_num)
-- n = 2
def t2 : RepType8 2 := mk8 2 0 0 0 0 0 0 1 1 (by decide) (by norm_num)
-- n = 3
def t3 : RepType8 3 := mk8 3 0 0 0 0 0 1 1 1 (by decide) (by norm_num)
-- n = 4 (two shapes)
def t4a : RepType8 4 := mk8 4 0 0 0 0 0 0 0 2 (by decide) (by norm_num)
def t4b : RepType8 4 := mk8 4 0 0 0 0 1 1 1 1 (by decide) (by norm_num)
-- n = 5 (two shapes)
def t5a : RepType8 5 := mk8 5 0 0 0 0 0 0 1 2 (by decide) (by norm_num)
def t5b : RepType8 5 := mk8 5 0 0 0 1 1 1 1 1 (by decide) (by norm_num)
-- n = 6 (two shapes)
def t6a : RepType8 6 := mk8 6 0 0 0 0 0 1 1 2 (by decide) (by norm_num)
def t6b : RepType8 6 := mk8 6 0 0 1 1 1 1 1 1 (by decide) (by norm_num)
-- n = 7 (two shapes)
def t7a : RepType8 7 := mk8 7 0 0 0 0 1 1 1 2 (by decide) (by norm_num)
def t7b : RepType8 7 := mk8 7 0 1 1 1 1 1 1 1 (by decide) (by norm_num)
-- n = 8 (three shapes, including the all-ones shape)
def t8a : RepType8 8 := mk8 8 0 0 0 0 0 0 2 2 (by decide) (by norm_num)
def t8b : RepType8 8 := mk8 8 0 0 0 1 1 1 1 2 (by decide) (by norm_num)
def t8c : RepType8 8 := mk8 8 1 1 1 1 1 1 1 1 (by decide) (by norm_num)
-- n = 12 (three shapes)
def t12a : RepType8 12 := mk8 12 0 0 0 0 0 2 2 2 (by decide) (by norm_num)
def t12b : RepType8 12 := mk8 12 0 0 0 0 1 1 1 3 (by decide) (by norm_num)
def t12c : RepType8 12 := mk8 12 0 0 1 1 1 1 2 2 (by decide) (by norm_num)

/-! ## Part 4: Contributions via `(★)`, checked by `native_decide` -/

theorem t1_contribution  : t1.contribution  = 16   := by native_decide
theorem t2_contribution  : t2.contribution  = 112  := by native_decide
theorem t3_contribution  : t3.contribution  = 448  := by native_decide
theorem t4a_contribution : t4a.contribution = 16   := by native_decide
theorem t4b_contribution : t4b.contribution = 1120 := by native_decide
theorem t5a_contribution : t5a.contribution = 224  := by native_decide
theorem t5b_contribution : t5b.contribution = 1792 := by native_decide
theorem t6a_contribution : t6a.contribution = 1344 := by native_decide
theorem t6b_contribution : t6b.contribution = 1792 := by native_decide
theorem t7a_contribution : t7a.contribution = 4480 := by native_decide
theorem t7b_contribution : t7b.contribution = 1024 := by native_decide
theorem t8a_contribution : t8a.contribution = 112  := by native_decide
theorem t8b_contribution : t8b.contribution = 8960 := by native_decide
theorem t8c_contribution : t8c.contribution = 256  := by native_decide
theorem t12a_contribution : t12a.contribution = 448   := by native_decide
theorem t12b_contribution : t12b.contribution = 4480  := by native_decide
theorem t12c_contribution : t12c.contribution = 26880 := by native_decide

/-! ## Part 5: The decomposition `∑ contributions = r₈(n)`

Jacobi's `r₈` values (computed independently in the certificate, and matching
`r₈(n) = 16 σ₃*(n)`) are reproduced exactly by summing the type contributions. -/

theorem r8_1 : t1.contribution = 16 := t1_contribution
theorem r8_2 : t2.contribution = 112 := t2_contribution
theorem r8_3 : t3.contribution = 448 := t3_contribution

/-- `r₈(4) = 1136`: shapes `(0,…,0,2)` and `(0,0,0,0,1,1,1,1)`. -/
theorem r8_4 : t4a.contribution + t4b.contribution = 1136 := by
  rw [t4a_contribution, t4b_contribution]

/-- `r₈(5) = 2016`: shapes `(0,…,0,1,2)` and `(0,0,0,1,1,1,1,1)`. -/
theorem r8_5 : t5a.contribution + t5b.contribution = 2016 := by
  rw [t5a_contribution, t5b_contribution]

/-- `r₈(6) = 3136`: shapes `(0,0,0,0,0,1,1,2)` and `(0,0,1,1,1,1,1,1)`. -/
theorem r8_6 : t6a.contribution + t6b.contribution = 3136 := by
  rw [t6a_contribution, t6b_contribution]

/-- `r₈(7) = 5504`: shapes `(0,0,0,0,1,1,1,2)` and `(0,1,1,1,1,1,1,1)`. -/
theorem r8_7 : t7a.contribution + t7b.contribution = 5504 := by
  rw [t7a_contribution, t7b_contribution]

/-- `r₈(8) = 9328`: three shapes, including the all-equal-nonzero shape
`(1,1,1,1,1,1,1,1)` contributing `8!/8! · 2⁸ = 256`. -/
theorem r8_8 : t8a.contribution + t8b.contribution + t8c.contribution = 9328 := by
  rw [t8a_contribution, t8b_contribution, t8c_contribution]

/-- `r₈(12) = 31808`: three shapes. -/
theorem r8_12 : t12a.contribution + t12b.contribution + t12c.contribution = 31808 := by
  rw [t12a_contribution, t12b_contribution, t12c_contribution]

/-! ## Part 6: Structural properties of the eight-square decomposition -/

/-- The number of nonzero parts is at most eight. -/
theorem nonzeroCount_le_eight {n : ℕ} (t : RepType8 n) : t.nonzeroCount ≤ 8 := by
  simp only [RepType8.nonzeroCount]
  split_ifs <;> omega

/-- The sign factor is a power of two, at most `2⁸ = 256`. -/
theorem signFactor_le_256 {n : ℕ} (t : RepType8 n) : t.signFactor ≤ 256 := by
  have h := nonzeroCount_le_eight t
  simp only [RepType8.signFactor]
  calc 2 ^ t.nonzeroCount ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) h
    _ = 256 := by norm_num

#check @RepType8.contribution
#check @r8_8
#check @nonzeroCount_le_eight

end FourSquareDistributionOQ04M8
