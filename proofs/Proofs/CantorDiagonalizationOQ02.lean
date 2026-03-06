import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic

/-
# Cardinality of the Set of All Countable Ordinals (OQ-02)

## Research Question

What is the cardinality of the set of all countable ordinals?
Can the Cantor diagonal argument be applied to the collection of countable ordinals
to show that this collection is itself uncountable?

## Answer

The set of all countable ordinals — formally {α : Ordinal | α.card ≤ ℵ₀} —
equals the initial segment Iio(ω₁), where ω₁ = (ℵ₁).ord is the first uncountable ordinal.

**Its cardinality is exactly ℵ₁.**

Key facts proved:
1. ω₁ = (Cardinal.aleph 1).ord is the smallest ordinal of cardinality ℵ₁
2. ω₁.card = ℵ₁ (proved: Cardinal.card_ord)
3. ℵ₁ = Order.succ ℵ₀ (proved: Cardinal.aleph_succ)
4. ℵ₀ < ℵ₁ (proved: Cardinal.aleph_lt_aleph)
5. κ < ℵ₁ ↔ κ ≤ ℵ₀ (proved: Order.lt_succ_iff)

## Cantor's Diagonal Argument for Ordinals

The connection to Cantor diagonalization: suppose we try to enumerate all countable
ordinals as a sequence α₀, α₁, α₂, ... (a countable list). We can construct a
countable ordinal NOT captured by any finite initial segment:

Given any countable set {αₙ} of countable ordinals, form β = sup_{n∈ℕ} αₙ.
- Each αₙ < ω₁ (countable)
- A countable union of countable ordinals is countable
- So β < ω₁ (still countable)
- But β ≥ αₙ for all n, so β + 1 > all αₙ

This is the "diagonal step": the set of countable ordinals is too large to be
enumerated by any countable list — it requires ℵ₁ many elements.

## Connection to OQ-01 (Continuum Hypothesis)

From OQ-01, we know ℵ₁ ≤ 2^ℵ₀. The cardinality of countable ordinals (ℵ₁) is
the minimum uncountable cardinality. CH asks: is ℵ₁ = 2^ℵ₀? Independent of ZFC.

## Proof Technique (Updated: Zero Axioms)

The three facts previously axiomatized are now fully proved using Mathlib:
1. α < ω₁ ↔ α.card ≤ ℵ₀ — via Cardinal.lt_ord (ordinal/cardinal initial segment correspondence)
2. ω₁ is a limit ordinal — via Cardinal.ord_isLimit (infinite cardinals have limit initial ordinal)
3. Countable sup is bounded — via Ordinal.sup_lt_ord + Cardinal.isRegular_aleph_one.cof_eq
-/

set_option linter.unusedVariables false

namespace CantorDiagonalizationOQ02

open Cardinal Ordinal

/- ## Part 1: The First Uncountable Ordinal ω₁ -/

/-- The first uncountable ordinal ω₁, defined as the initial ordinal of ℵ₁.
    This is the smallest ordinal whose cardinality equals ℵ₁. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1 : Cardinal.{0}).ord

/-- The cardinality of ω₁ equals ℵ₁.
    This follows directly from `Cardinal.card_ord`:
    the initial ordinal of any cardinal c has cardinality c. -/
theorem omega1_card : omega1.card = Cardinal.aleph 1 :=
  Cardinal.card_ord _

/- ## Part 2: ℵ₁ is the Successor of ℵ₀ -/

/-- ℵ₁ is the successor cardinal of ℵ₀.
    Uses `Cardinal.aleph_succ`: aleph(α+1) = Order.succ(aleph α). -/
theorem aleph1_eq_succ_aleph0 :
    (Cardinal.aleph 1 : Cardinal.{0}) = Order.succ (ℵ₀ : Cardinal.{0}) := by
  have : (Cardinal.aleph 1 : Cardinal.{0}) = Order.succ (Cardinal.aleph 0) := by
    have h1 : (1 : Ordinal) = Order.succ 0 := by simp
    rw [h1, Cardinal.aleph_succ]
  rwa [Cardinal.aleph_zero] at this

/-- The key fact: κ < ℵ₁ if and only if κ ≤ ℵ₀.
    This characterizes ℵ₁ as the MINIMUM uncountable cardinal. -/
theorem lt_aleph1_iff_le_aleph0 (κ : Cardinal.{0}) :
    κ < Cardinal.aleph 1 ↔ κ ≤ ℵ₀ := by
  rw [aleph1_eq_succ_aleph0]
  exact Order.lt_succ_iff

/- ## Part 3: Uncountability of ℵ₁ and ω₁ -/

/-- ℵ₀ < ℵ₁: the first uncountable cardinal is strictly larger than the countable infinity. -/
theorem aleph0_lt_aleph1 : (ℵ₀ : Cardinal.{0}) < Cardinal.aleph 1 := by
  have : Cardinal.aleph 0 < Cardinal.aleph 1 :=
    Cardinal.aleph_lt_aleph.mpr (by norm_num)
  rwa [Cardinal.aleph_zero] at this

/-- ω₁ is uncountable: its cardinality strictly exceeds ℵ₀. -/
theorem omega1_uncountable : (ℵ₀ : Cardinal.{0}) < omega1.card := by
  rw [omega1_card]
  exact aleph0_lt_aleph1

/-- Equivalently, ω₁ cannot be put in bijection with ℕ. -/
theorem omega1_not_countable : ¬ (omega1.card ≤ ℵ₀) :=
  not_le.mpr omega1_uncountable

/- ## Part 4: The Minimum Uncountable Cardinal -/

/-- ℵ₁ is the minimum uncountable cardinal:
    any uncountable cardinal is ≥ ℵ₁. -/
theorem aleph1_minimum_uncountable (κ : Cardinal.{0}) (hκ : ℵ₀ < κ) :
    Cardinal.aleph 1 ≤ κ := by
  rw [aleph1_eq_succ_aleph0]
  exact Order.succ_le_of_lt hκ

/-- The cardinal ℵ₁ is a gap:
    there is no cardinal strictly between ℵ₀ and ℵ₁. -/
theorem no_cardinal_between_aleph0_aleph1 (κ : Cardinal.{0})
    (h1 : ℵ₀ < κ) (h2 : κ < Cardinal.aleph 1) : False := by
  have : κ ≤ ℵ₀ := (lt_aleph1_iff_le_aleph0 κ).mp h2
  exact absurd h1 (not_lt.mpr this)

/- ## Part 5: Countable Ordinals as Iio(ω₁) -/

/-- An ordinal is "countable" in the set-theoretic sense if α.card ≤ ℵ₀. -/
def IsCountableOrdinal (α : Ordinal.{0}) : Prop := α.card ≤ ℵ₀

/-- The characterization of ω₁ as threshold between countable and uncountable ordinals.

    Proof: α < (aleph 1).ord ↔ α.card < aleph 1 (by Cardinal.lt_ord)
                               ↔ α.card ≤ ℵ₀ (by lt_aleph1_iff_le_aleph0)
                               ↔ IsCountableOrdinal α (by definition). -/
theorem lt_omega1_iff_countable (α : Ordinal.{0}) :
    α < omega1 ↔ IsCountableOrdinal α := by
  unfold omega1 IsCountableOrdinal
  rw [Cardinal.lt_ord]
  exact lt_aleph1_iff_le_aleph0 α.card

/-- The set of countable ordinals equals the initial segment below ω₁. -/
theorem countable_ordinals_eq_Iio :
    {α : Ordinal.{0} | IsCountableOrdinal α} = Set.Iio omega1 := by
  ext α; exact (lt_omega1_iff_countable α).symm

/- ## Part 6: Zero is a Countable Ordinal -/

/-- The ordinal 0 is countable: its cardinality is 0 ≤ ℵ₀. -/
theorem zero_lt_omega1 : (0 : Ordinal.{0}) < omega1 := by
  rw [lt_omega1_iff_countable]
  unfold IsCountableOrdinal
  simp

/- ## Part 7: The Cantor Diagonal Argument for Countable Ordinals -/

/-- ω₁ is a limit ordinal: there is no immediate predecessor.
    Every ordinal below ω₁ has a strict successor that is still below ω₁.

    Proof: Given α < ω₁, we have card α ≤ ℵ₀ (by lt_omega1_iff_countable).
    Then card (α + 1) = card (succ α) = card α + 1 ≤ ℵ₀ + 1 = ℵ₀ ≤ ℵ₀,
    so α + 1 < ω₁. -/
theorem omega1_isLimit : ∀ α : Ordinal.{0}, α < omega1 → α + 1 < omega1 := by
  intro α hα
  rw [lt_omega1_iff_countable] at hα ⊢
  unfold IsCountableOrdinal at *
  rw [Ordinal.add_one_eq_succ, Ordinal.card_succ]
  calc card α + 1 ≤ ℵ₀ + 1 := add_le_add hα le_rfl
    _ = ℵ₀ := Cardinal.add_one_of_aleph0_le le_rfl

/-- The supremum of any countable sequence of countable ordinals is countable.
    This is the crucial closure property that drives the diagonal argument.

    Proof: ℵ₁ is a regular cardinal (isRegular_aleph_one), so cof(ω₁) = ℵ₁.
    By Ordinal.sup_lt_ord, any sup over a family of size #ℕ = ℵ₀ < ℵ₁ = cof(ω₁)
    with all values < ω₁ is itself < ω₁.
    Note: sSup (Set.range f) = Ordinal.sup f (definitionally, both equal iSup f). -/
theorem countable_sup_lt_omega1 (f : ℕ → Ordinal.{0})
    (hf : ∀ n, f n < omega1) : sSup (Set.range f) < omega1 := by
  -- sSup (Set.range f) = iSup f (definitionally equal via definition of iSup)
  show iSup f < omega1
  -- Need: #ℕ < omega1.cof
  -- omega1.cof = (aleph 1).ord.cof = aleph 1 (by regularity of ℵ₁)
  -- #ℕ = ℵ₀ < aleph 1
  have hcof : omega1.cof = Cardinal.aleph 1 := by
    unfold omega1
    exact Cardinal.isRegular_aleph_one.cof_eq
  have hlt : #(ℕ) < omega1.cof := by
    rw [hcof, Cardinal.mk_nat]
    exact aleph0_lt_aleph1
  exact Ordinal.iSup_lt_ord hlt hf

/-- **The Cantor Diagonal Argument for Countable Ordinals**:

    For any countable sequence of countable ordinals f : ℕ → Ordinal,
    there exists a countable ordinal β that is STRICTLY GREATER than all f(n).

    This is the ordinal version of the diagonal argument: the set of countable
    ordinals cannot be "approached" from below by any countable sequence —
    there is always a countable ordinal "above" any countable collection.

    This formally shows the set of countable ordinals has uncountable size. -/
theorem cantor_diagonal_countable_ordinals
    (f : ℕ → Ordinal.{0}) (hf : ∀ n, f n < omega1) :
    ∃ β : Ordinal.{0}, β < omega1 ∧ ∀ n, f n < β := by
  -- sSup (range f) is bounded above by omega1, so csSup is well-defined
  have hbdd : BddAbove (Set.range f) :=
    ⟨omega1, fun x ⟨n, hn⟩ => hn ▸ le_of_lt (hf n)⟩
  -- The supremum of the sequence f is still a countable ordinal
  have hsup : sSup (Set.range f) < omega1 := countable_sup_lt_omega1 f hf
  -- β = (sSup f) + 1 is countable (ω₁ is a limit ordinal)
  have hsucc : sSup (Set.range f) + 1 < omega1 := omega1_isLimit _ hsup
  use sSup (Set.range f) + 1
  refine ⟨hsucc, fun n => ?_⟩
  -- f n ≤ sSup (range f) < sSup (range f) + 1
  have hle : f n ≤ sSup (Set.range f) :=
    le_csSup hbdd (Set.mem_range_self n)
  exact lt_of_le_of_lt hle (lt_add_of_pos_right _ zero_lt_one)

/-- Corollary: no surjection from ℕ maps onto all countable ordinals.
    The set of countable ordinals is "diagonalizable" — for any countable enumeration,
    we can always find a countable ordinal that exceeds all listed ordinals. -/
theorem no_surjection_onto_countable_ordinals :
    ∀ f : ℕ → Ordinal.{0},
    ¬ (∀ α : Ordinal.{0}, α < omega1 → ∃ n, f n = α) := by
  intro f hf_surj
  -- Clip f to countable values: g n = f n if f n < omega1, else 0
  -- This ensures all g n are countable
  let g : ℕ → Ordinal.{0} := fun n => if f n < omega1 then f n else 0
  have hg : ∀ n, g n < omega1 := by
    intro n
    simp only [g]
    split_ifs with h
    · exact h
    · exact zero_lt_omega1
  -- g still surjects onto all countable ordinals
  -- (if f n = α < omega1, then f n < omega1, so g n = f n = α)
  have hg_surj : ∀ α : Ordinal.{0}, α < omega1 → ∃ n, g n = α := by
    intro α hα
    obtain ⟨n, hn⟩ := hf_surj α hα
    exact ⟨n, by simp only [g, hn, hα, ↓reduceIte]⟩
  -- Apply diagonal argument to g
  obtain ⟨β, hβlt, hβgt⟩ := cantor_diagonal_countable_ordinals g hg
  -- β < ω₁ but β > all g(n), contradicts surjectivity
  obtain ⟨n, hn⟩ := hg_surj β hβlt
  exact absurd (hn ▸ hβgt n) (lt_irrefl _)

/- ## Part 8: Summary -/

/-- **Main theorem**: The Cantor diagonal argument shows why the set of
    countable ordinals has uncountable size (cardinality ≥ ℵ₁):
    - ℵ₁ > ℵ₀ (strictly uncountable)
    - No countable enumeration can cover all countable ordinals (diagonal argument)
    - ℵ₁ is the MINIMUM uncountable cardinal (no cardinal between ℵ₀ and ℵ₁) -/
theorem cantor_diagonalization_summary :
    -- (1) ℵ₁ > ℵ₀ (ω₁ is uncountable)
    (ℵ₀ : Cardinal.{0}) < Cardinal.aleph 1 ∧
    -- (2) ℵ₁ is the minimum uncountable cardinal
    (∀ κ : Cardinal.{0}, ℵ₀ < κ → Cardinal.aleph 1 ≤ κ) ∧
    -- (3) No surjection ℕ → (countable ordinals): diagonal argument
    (∀ f : ℕ → Ordinal.{0},
       ¬ (∀ α : Ordinal.{0}, α < omega1 → ∃ n, f n = α)) ∧
    -- (4) ω₁.card = ℵ₁ (the ordinal that bounds all countable ordinals has card ℵ₁)
    omega1.card = Cardinal.aleph 1 := by
  exact ⟨aleph0_lt_aleph1,
         aleph1_minimum_uncountable,
         no_surjection_onto_countable_ordinals,
         omega1_card⟩

end CantorDiagonalizationOQ02
