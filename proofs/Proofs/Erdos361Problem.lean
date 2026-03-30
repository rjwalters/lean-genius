/- Erdős Problem 361: Largest Non-Representing Subsets

Let `c > 0` and `n` be a large integer. What is the size of the largest set
`A ⊆ {1, ..., ⌊cn⌋}` such that `n` is not a sum of a subset of `A`?

Does this maximum size depend on `n` in an irregular way?

Source: Erdős–Graham [ErGr80, p. 59]

Reference: erdosproblems.com/361
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic

open Finset Filter Asymptotics Classical

/- ## Definitions -/

/-- `IsSubsetSum A n` holds when `n` can be expressed as a sum of elements from a
subset of `A`. -/
def IsSubsetSum (A : Finset ℕ) (n : ℕ) : Prop :=
    ∃ B : Finset ℕ, B ⊆ A ∧ B.sum id = n

/-- `NonRepresenting A n` means `n` is NOT a sum of any subset of `A`. -/
def NonRepresenting (A : Finset ℕ) (n : ℕ) : Prop :=
    ¬IsSubsetSum A n

/-- `maxNonReprSize c n` is the maximum cardinality of `A ⊆ {1,...,⌊cn⌋}` such
that `n` is not a sum of a subset of `A`. -/
noncomputable def maxNonReprSize (c : ℝ) (n : ℕ) : ℕ :=
    ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B => NonRepresenting B n)).sup Finset.card

/- ## Main conjecture -/

/-- Erdős Problem 361: What is the asymptotic growth of `maxNonReprSize c n`?
Does it depend on `n` irregularly? The question asks for the growth rate
and whether the function oscillates. -/
def ErdosProblem361 : Prop :=
    ∀ c : ℝ, 0 < c →
      ¬Monotone (fun n => maxNonReprSize c n)

/-- A weaker form: `maxNonReprSize c n` is unbounded as `n → ∞`. -/
def MaxNonReprUnbounded : Prop :=
    ∀ c : ℝ, 0 < c → Tendsto (fun n => (maxNonReprSize c n : ℝ)) atTop atTop

/- ## Asymptotic questions (OPEN - kept as axioms) -/

/-- Is there an asymptotic upper bound `maxNonReprSize c n = O(f(n))` for some `f`? -/
/-- The growth rate might be `Θ(√n)` — this is a plausible conjecture. -/
/- ## Proved basic properties -/

/-- The empty set is always non-representing (for `n > 0`).
The only subset of `∅` is `∅` itself, which sums to `0 ≠ n`. -/
theorem nonRepresenting_empty (n : ℕ) (hn : 0 < n) : NonRepresenting ∅ n := by
  intro ⟨B, hB, hsum⟩
  have hBeq : B = ∅ := Finset.eq_empty_of_forall_notMem (fun x hx =>
    absurd (hB hx) (Finset.notMem_empty x))
  subst hBeq
  simp [id] at hsum
  omega

/-- Any subset of a non-representing set is also non-representing.
If no subset of `B` sums to `n`, and `A ⊆ B`, then no subset of `A` sums to `n`
either, since every subset of `A` is also a subset of `B`. -/
theorem nonRepresenting_subset {A B : Finset ℕ} {n : ℕ}
    (h : A ⊆ B) (hB : NonRepresenting B n) : NonRepresenting A n := by
  intro ⟨C, hCA, hsum⟩
  exact hB ⟨C, Finset.Subset.trans hCA h, hsum⟩

/-- For the singleton `{1}`, it's non-representing for `n ≥ 2`.
The subsets of `{1}` are `∅` (sum 0) and `{1}` (sum 1), neither equals `n ≥ 2`. -/
theorem singleton_one_nonRepr (n : ℕ) (hn : 2 ≤ n) : NonRepresenting {1} n := by
  intro ⟨B, hB, hsum⟩
  rw [Finset.subset_singleton_iff] at hB
  rcases hB with rfl | rfl
  · simp [id] at hsum; omega
  · simp [id] at hsum; omega

/- ## Structural lemmas -/

/-- If the sum of all elements in `A` is less than `n`, then `A` is non-representing.
Any subset `B ⊆ A` has `sum B ≤ sum A < n`, so `sum B ≠ n`. -/
theorem nonRepresenting_of_sum_lt {A : Finset ℕ} {n : ℕ}
    (hsum : A.sum id < n) : NonRepresenting A n := by
  intro ⟨B, hBA, hBsum⟩
  have hle : B.sum id ≤ A.sum id :=
    Finset.sum_le_sum_of_subset_of_nonneg hBA (fun _ _ _ => Nat.zero_le _)
  omega

/- ## Proved properties -/

/-- When the total sum of `{1,...,⌊cn⌋}` is less than `n`, every subset is
non-representing, so `maxNonReprSize c n` equals the full range cardinality.
This replaces the former `maxNonRepr_large_n` which incorrectly claimed an
asymptotic result — the condition `sum < n` only holds for finitely many `n`
when `c > 0` is fixed, since the sum grows as `Θ(c²n²)`. -/
theorem maxNonRepr_full_of_sum_lt (c : ℝ) (n : ℕ)
    (hsum : (Finset.Icc 1 ⌊c * ↑n⌋₊).sum id < n) :
    maxNonReprSize c n = (Finset.Icc 1 ⌊c * ↑n⌋₊).card := by
  unfold maxNonReprSize
  apply le_antisymm
  · -- Every element of the filtered powerset has card ≤ card(Icc 1 m)
    apply Finset.sup_le
    intro B hB
    rw [Finset.mem_filter] at hB
    rw [Finset.mem_powerset] at hB
    exact Finset.card_le_card hB.1
  · -- The full range Icc 1 m is itself in the filtered powerset
    apply Finset.le_sup (f := Finset.card)
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, nonRepresenting_of_sum_lt hsum⟩

/-- `maxNonReprSize c n ≥ 1` for `n ≥ 2` and `c ≥ 1`, since `{1}` is a
non-representing subset of `{1,...,⌊cn⌋}` with cardinality 1. -/
theorem maxNonRepr_ge_one (c : ℝ) (hc : 1 ≤ c) (n : ℕ) (hn : 2 ≤ n) :
    1 ≤ maxNonReprSize c n := by
  unfold maxNonReprSize
  -- Show 1 ∈ Icc 1 ⌊c * n⌋₊
  have hm : 1 ≤ ⌊c * (↑n : ℝ)⌋₊ := by
    have hcn : (1 : ℝ) ≤ c * ↑n := by
      have : (2 : ℝ) ≤ (↑n : ℝ) := Nat.ofNat_le_cast.mpr hn
      nlinarith
    have : 0 < ⌊c * (↑n : ℝ)⌋₊ := Nat.floor_pos.mpr hcn
    omega
  -- Show {1} is in the filtered powerset
  have hmem : ({1} : Finset ℕ) ∈ (Finset.Icc 1 ⌊c * (↑n : ℝ)⌋₊).powerset.filter
      (fun B => NonRepresenting B n) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.singleton_subset_iff.mpr (Finset.mem_Icc.mpr ⟨le_refl 1, hm⟩),
           singleton_one_nonRepr n hn⟩
  -- card {1} = 1, and le_sup gives 1 ≤ sup card
  calc (1 : ℕ) = ({1} : Finset ℕ).card := by simp
    _ ≤ _ := Finset.le_sup hmem
