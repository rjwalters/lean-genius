/-
Erdős Problem #100, Open Question 3:
The Optimal Linear Constant in the 1-Dimensional Analogue

**Parent problem (Erdős #100, OPEN).** Let `A` be a set of `n` points in `ℝ²`
all of whose pairwise distances are positive integers. Must the diameter of `A`
be `≫ n`? The best known lower bounds are `diam ≥ n^(3/4)` (Kanold) and
`diam ≥ c·n/log n` (Guth–Katz, via distinct distances); whether a *linear* bound
`diam ≥ c·n` holds, and what the optimal constant `c` would be, is open.

**This entry answers the question completely in dimension 1.**
On a line the points are totally ordered, and the `n-1` distances from the
leftmost point to the others are distinct positive integers, hence one of them
is `≥ n-1`. This gives `diam(A) ≥ n - 1`, and the arithmetic progression
`{0,1,…,n-1}` attains it. Therefore the optimal linear constant in dimension 1
is exactly `c = 1`:

    diam(A) ≥ |A| - 1,   with equality for {0,1,…,n-1}.

The contrast with the plane is the whole content of the open problem: in `ℝ²`
the `n-1` distances from one point need *not* be distinct (points can be
equidistant), which is exactly why the linear lower bound is hard there.

We also record the dimension-free packing inequality underlying every known
lower bound: the distinct pairwise distances are distinct positive integers in
`{1,…,⌊diam⌋}`, so the number of distinct distances is `≤ diam`. In dimension 1
the number of distinct distances is `≥ n-1`, recovering the sharp bound.

All results are fully verified, 0 axioms, no `native_decide`.

Reference: https://erdosproblems.com/100
-/

import Mathlib

open Finset

namespace Erdos100OQ03

/--
A finite set of real numbers (collinear points on the line) has the
**integer-distance property** when every pairwise difference is an integer.
On the line `dist a b = |a - b|`, so this is exactly the condition that all
pairwise distances are integers (and hence positive integers for distinct
points, since distinct reals at integer distance differ by at least `1`).
-/
def IntegerDistances (A : Finset ℝ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∃ k : ℤ, a - b = (k : ℝ)

/--
The diameter of a nonempty finite set on the line: largest minus smallest.
-/
noncomputable def diam (A : Finset ℝ) (hA : A.Nonempty) : ℝ :=
  A.max' hA - A.min' hA

/-! ### Key arithmetic fact: shifted points are nonnegative integers -/

/--
If `A` has the integer-distance property and `m` is its minimum, then for every
`a ∈ A` the shift `a - m` equals its own floor (i.e. it is an integer real),
and that floor is nonnegative.
-/
theorem shift_eq_floor (A : Finset ℝ) (hA : A.Nonempty) (hd : IntegerDistances A)
    {a : ℝ} (ha : a ∈ A) :
    ((⌊a - A.min' hA⌋ : ℤ) : ℝ) = a - A.min' hA ∧ 0 ≤ ⌊a - A.min' hA⌋ := by
  obtain ⟨k, hk⟩ := hd a ha (A.min' hA) (A.min'_mem hA)
  constructor
  · rw [hk, Int.floor_intCast]
  · have hge : (0 : ℝ) ≤ a - A.min' hA := by
      have := A.min'_le a ha
      linarith
    have : (0 : ℝ) ≤ ((⌊a - A.min' hA⌋ : ℤ) : ℝ) := by
      rw [hk, Int.floor_intCast]; rw [← hk]; exact hge
    exact_mod_cast this

/-! ### Main lower bound: diam ≥ |A| - 1 -/

/--
**Sharp 1-dimensional lower bound.**
For a nonempty collinear point set with integer pairwise distances,
`diam(A) ≥ |A| - 1`.

Proof: shift so the minimum is `0`; the map `a ↦ ⌊a - min⌋` is injective on `A`
(the shifts are genuine integers), so it sends `A` to `|A|` distinct integers in
`[0, ⌊diam⌋]`. An interval of integers of that length holds at most
`⌊diam⌋ + 1` of them, whence `|A| ≤ ⌊diam⌋ + 1 ≤ diam + 1`.
-/
theorem diam_ge_card_sub_one (A : Finset ℝ) (hA : A.Nonempty)
    (hd : IntegerDistances A) :
    (A.card : ℝ) - 1 ≤ diam A hA := by
  set m := A.min' hA with hm
  set M := A.max' hA with hMdef
  -- the shifting map into ℤ
  set f : ℝ → ℤ := fun a => ⌊a - m⌋ with hf
  -- `f` is injective on `A`
  have hinj : Set.InjOn f A := by
    intro a ha b hb hab
    have ea := (shift_eq_floor A hA hd ha).1
    have eb := (shift_eq_floor A hA hd hb).1
    have : a - m = b - m := by
      rw [← ea, ← eb]; exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hab
    linarith
  -- the image set
  set T : Finset ℤ := A.image f with hT
  have hcardT : T.card = A.card := by
    rw [hT]; exact Finset.card_image_of_injOn hinj
  -- every image lands in Icc 0 ⌊M - m⌋
  have hsub : T ⊆ Finset.Icc 0 ⌊M - m⌋ := by
    intro t ht
    rw [hT, Finset.mem_image] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    rw [Finset.mem_Icc]
    refine ⟨(shift_eq_floor A hA hd ha).2, ?_⟩
    apply Int.floor_le_floor
    have : a ≤ M := A.le_max' a ha
    linarith
  -- cardinality of the integer interval
  have hMm : (0 : ℝ) ≤ M - m := by
    have := A.min'_le (A.max' hA) (A.max'_mem hA)
    linarith
  have hfloor_nonneg : 0 ≤ ⌊M - m⌋ := Int.floor_nonneg.mpr hMm
  have hcardIcc : ((Finset.Icc (0 : ℤ) ⌊M - m⌋).card : ℤ) = ⌊M - m⌋ + 1 := by
    rw [Int.card_Icc]; omega
  -- combine: |A| = |T| ≤ ⌊M-m⌋ + 1
  have hcard_le : (A.card : ℤ) ≤ ⌊M - m⌋ + 1 := by
    have h1 : T.card ≤ (Finset.Icc (0 : ℤ) ⌊M - m⌋).card := Finset.card_le_card hsub
    rw [hcardT] at h1
    have h2 : (A.card : ℤ) ≤ ((Finset.Icc (0 : ℤ) ⌊M - m⌋).card : ℤ) := by exact_mod_cast h1
    rw [hcardIcc] at h2
    exact h2
  -- push to ℝ and use ⌊M-m⌋ ≤ M - m
  have hcast : (A.card : ℝ) ≤ (⌊M - m⌋ : ℝ) + 1 := by exact_mod_cast hcard_le
  have hfl : (⌊M - m⌋ : ℝ) ≤ M - m := Int.floor_le _
  rw [diam, ← hMdef, ← hm]
  linarith

/-! ### Sharpness: the arithmetic progression {0,1,…,n-1} attains equality -/

/-- The witness configuration `{0, 1, …, n-1}` as a finite set of reals. -/
noncomputable def apSet (n : ℕ) : Finset ℝ := (Finset.range n).image (fun i : ℕ => (i : ℝ))

theorem apSet_card (n : ℕ) : (apSet n).card = n := by
  rw [apSet, Finset.card_image_of_injOn, Finset.card_range]
  intro a _ b _ h
  exact Nat.cast_injective h

theorem apSet_nonempty {n : ℕ} (hn : 0 < n) : (apSet n).Nonempty := by
  rw [apSet]
  exact (Finset.nonempty_range_iff.mpr hn.ne').image _

theorem apSet_integerDistances (n : ℕ) : IntegerDistances (apSet n) := by
  intro a ha b hb
  rw [apSet, Finset.mem_image] at ha hb
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, rfl⟩ := hb
  exact ⟨(i : ℤ) - (j : ℤ), by push_cast; ring⟩

/-- Membership characterization: `x ∈ apSet n` iff `x = i` for some `i < n`. -/
theorem mem_apSet {n : ℕ} {x : ℝ} : x ∈ apSet n ↔ ∃ i : ℕ, i < n ∧ x = (i : ℝ) := by
  rw [apSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, Finset.mem_range.mp hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, Finset.mem_range.mpr hi, rfl⟩

theorem apSet_min {n : ℕ} (hn : 0 < n) : (apSet n).min' (apSet_nonempty hn) = 0 := by
  apply le_antisymm
  · apply Finset.min'_le
    rw [mem_apSet]; exact ⟨0, hn, by norm_num⟩
  · apply Finset.le_min'
    intro y hy
    rw [mem_apSet] at hy
    obtain ⟨i, _, rfl⟩ := hy
    positivity

theorem apSet_max {n : ℕ} (hn : 0 < n) :
    (apSet n).max' (apSet_nonempty hn) = (n : ℝ) - 1 := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    rw [mem_apSet] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    have : (i : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_pred_of_lt hi
    rw [Nat.cast_pred hn] at this; linarith
  · apply Finset.le_max'
    rw [mem_apSet]
    refine ⟨n - 1, Nat.sub_lt hn one_pos, ?_⟩
    rw [Nat.cast_pred hn]

/--
**Sharpness.** For every `n ≥ 1` the configuration `{0,1,…,n-1}` has integer
pairwise distances, `n` points, and diameter exactly `n - 1`. Hence the lower
bound `diam ≥ |A| - 1` cannot be improved: the optimal linear constant is `1`.
-/
theorem apSet_diam {n : ℕ} (hn : 0 < n) :
    diam (apSet n) (apSet_nonempty hn) = (n : ℝ) - 1 := by
  rw [diam, apSet_max hn, apSet_min hn]; ring

/--
**Optimal constant statement.** For dimension 1, `c = 1` is the optimal linear
constant: the bound `diam ≥ |A| - 1` always holds (with equality attained), and
the witness has `|A| = n` and `diam = n - 1`.
-/
theorem optimal_constant_one {n : ℕ} (hn : 0 < n) :
    ∃ A : Finset ℝ, ∃ hA : A.Nonempty,
      A.card = n ∧ IntegerDistances A ∧ diam A hA = (n : ℝ) - 1 ∧
      ∀ B : Finset ℝ, ∀ hB : B.Nonempty, IntegerDistances B →
        (B.card : ℝ) - 1 ≤ diam B hB := by
  refine ⟨apSet n, apSet_nonempty hn, apSet_card n, apSet_integerDistances n,
    apSet_diam hn, ?_⟩
  intro B hB hd
  exact diam_ge_card_sub_one B hB hd

/-! ### Dimension-free packing inequality (the connection noted in #100) -/

/--
**Distinct-distance packing bound.** The distinct positive pairwise distances of
an integer-distance set are distinct positive integers, all `≤ diam`. Hence the
number of distinct distances is at most `diam`.

We formalize the integer-content of this statement: the set of distinct distance
*values*, viewed in `ℤ` via the floor, is a set of positive integers contained in
`Icc 1 ⌊diam⌋`, so its cardinality is `≤ ⌊diam⌋ ≤ diam`.
-/
theorem distinct_distances_le_diam (A : Finset ℝ) (hA : A.Nonempty)
    (hd : IntegerDistances A) :
    let D : Finset ℤ :=
      (A ×ˢ A).filter (fun p => p.1 ≠ p.2) |>.image (fun p => ⌊|p.1 - p.2|⌋)
    (D.card : ℝ) ≤ diam A hA := by
  intro D
  -- every element of D is a positive integer ≤ ⌊diam⌋
  have hsub : D ⊆ Finset.Icc 1 ⌊diam A hA⌋ := by
    intro t ht
    simp only [D, Finset.mem_image, Finset.mem_filter] at ht
    obtain ⟨⟨a, b⟩, ⟨hmem, hne⟩, rfl⟩ := ht
    rw [Finset.mem_product] at hmem
    obtain ⟨ha, hb⟩ := hmem
    simp only at hne ⊢
    obtain ⟨k, hk⟩ := hd a ha b hb
    -- |a - b| is a positive integer
    have hposR : (0 : ℝ) < |a - b| := by
      rw [abs_pos]; exact sub_ne_zero.mpr hne
    have hval : (⌊|a - b|⌋ : ℝ) = |a - b| := by
      have h0 : |a - b| = |(k : ℝ)| := by rw [hk]
      rw [h0, ← Int.cast_abs, Int.floor_intCast]
    rw [Finset.mem_Icc]
    constructor
    · -- ≥ 1 since positive integer
      have : (0 : ℝ) < (⌊|a - b|⌋ : ℝ) := by rw [hval]; exact hposR
      have : 0 < ⌊|a - b|⌋ := by exact_mod_cast this
      omega
    · -- ≤ ⌊diam⌋ since |a-b| ≤ diam
      apply Int.le_floor.mpr
      rw [hval, diam]
      have h1 : A.min' hA ≤ a := A.min'_le a ha
      have h2 : a ≤ A.max' hA := A.le_max' a ha
      have h3 : A.min' hA ≤ b := A.min'_le b hb
      have h4 : b ≤ A.max' hA := A.le_max' b hb
      rw [abs_le]; constructor <;> linarith
  have hcard : D.card ≤ (Finset.Icc 1 ⌊diam A hA⌋).card := Finset.card_le_card hsub
  have hdiam_nonneg : (0 : ℝ) ≤ diam A hA := by
    rw [diam]; have := A.min'_le (A.max' hA) (A.max'_mem hA); linarith
  have hfloor_nonneg : 0 ≤ ⌊diam A hA⌋ := Int.floor_nonneg.mpr hdiam_nonneg
  rw [Int.card_Icc] at hcard
  -- (⌊diam⌋ + 1 - 1).toNat = ⌊diam⌋.toNat
  have hcard' : (D.card : ℤ) ≤ ⌊diam A hA⌋ := by
    have : ((Finset.Icc 1 ⌊diam A hA⌋).card : ℤ) = ⌊diam A hA⌋ := by
      rw [Int.card_Icc]; omega
    omega
  calc (D.card : ℝ) ≤ (⌊diam A hA⌋ : ℝ) := by exact_mod_cast hcard'
    _ ≤ diam A hA := Int.floor_le _

end Erdos100OQ03
