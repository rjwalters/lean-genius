/-
Cantor Diagonal Argument Generalized to Regular Cardinals (OQ-02-OQ-03)

The parent formalization (OQ-02) proves the diagonal argument for countable ordinals
using ω₁ and the regularity of ℵ₁. Here we generalize: for ANY regular uncountable
cardinal κ, the ordinals below κ.ord cannot be enumerated by a set of size < κ.

The key insight: regularity of κ means cof(κ.ord) = κ, so any family of ordinals
below κ.ord indexed by a set of size < κ has supremum still below κ.ord.
This is the abstract form of the Cantor diagonal argument.

Main results:
1. `regular_sup_bounded`: for regular κ, sup of < κ-many ordinals below κ.ord is bounded
2. `card_succ_lt_of_lt_infinite`: μ < κ implies μ + 1 < κ for infinite κ
3. `regular_diagonal`: for any < κ-sized family below κ.ord, there's an ordinal above all
4. `regular_no_surjection`: no < κ-sized family below κ.ord can surject onto ordinals below κ.ord

All results proved from Mathlib with 0 axioms and 0 sorries.

References:
- Hausdorff (1908): Regular and singular cardinals
- Mathlib: SetTheory.Cardinal.Cofinality
-/

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic

namespace CantorDiagonalizationOQ02OQ03

open Cardinal Ordinal

-- ══════════════════════════════════════════════════════════════════
-- § Part I: Regular Cardinals — Bounded Suprema
-- ══════════════════════════════════════════════════════════════════

/-- For a regular cardinal κ, any family of ordinals below κ.ord
    indexed by a type of size < κ has supremum still below κ.ord.

    This is the abstract engine behind all Cantor-type diagonal arguments:
    regular cardinals cannot be "reached from below" by fewer elements. -/
theorem regular_sup_bounded {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    {ι : Type u} (hι : #ι < κ) (f : ι → Ordinal.{u})
    (hf : ∀ i, f i < κ.ord) : iSup f < κ.ord :=
  Ordinal.iSup_lt_ord (hκ.cof_eq ▸ hι) hf

-- ══════════════════════════════════════════════════════════════════
-- § Part II: Successor Cardinals Below Infinite Cardinals
-- ══════════════════════════════════════════════════════════════════

/-- For infinite κ, μ < κ implies μ + 1 < κ.
    Either μ is infinite (so μ + 1 = μ < κ) or finite (so μ + 1 < ℵ₀ ≤ κ). -/
theorem card_succ_lt_of_lt_infinite {κ : Cardinal.{u}} (hκ_inf : ℵ₀ ≤ κ)
    {μ : Cardinal.{u}} (hμ : μ < κ) : μ + 1 < κ := by
  by_cases h : ℵ₀ ≤ μ
  · rwa [Cardinal.add_one_of_aleph0_le h]
  · push_neg at h
    exact lt_of_lt_of_le (Cardinal.add_lt_aleph0 h Cardinal.one_lt_aleph0) hκ_inf

/-- For infinite κ, κ.ord is a limit ordinal: α < κ.ord implies α + 1 < κ.ord. -/
theorem ord_succ_lt {κ : Cardinal.{u}} (hκ_inf : ℵ₀ ≤ κ)
    {α : Ordinal.{u}} (hα : α < κ.ord) : α + 1 < κ.ord := by
  rw [Cardinal.lt_ord] at hα ⊢
  rw [Ordinal.add_one_eq_succ, Ordinal.card_succ]
  exact card_succ_lt_of_lt_infinite hκ_inf hα

-- ══════════════════════════════════════════════════════════════════
-- § Part III: The Generalized Diagonal Argument
-- ══════════════════════════════════════════════════════════════════

/-- **Generalized Cantor Diagonal Argument**: For any regular uncountable cardinal κ,
    any family of ordinals below κ.ord indexed by a type of size < κ
    has an ordinal below κ.ord that strictly exceeds all members.

    This unifies the classical diagonal argument (κ = ℵ₁, index = ℕ)
    with arguments for higher regular cardinals (κ = ℵ_{α+1}). -/
theorem regular_diagonal {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hκ_inf : ℵ₀ ≤ κ) {ι : Type u} (hι : #ι < κ)
    (f : ι → Ordinal.{u}) (hf : ∀ i, f i < κ.ord) :
    ∃ β : Ordinal.{u}, β < κ.ord ∧ ∀ i, f i < β := by
  have hsup : iSup f < κ.ord := regular_sup_bounded hκ hι f hf
  have hsucc : iSup f + 1 < κ.ord := ord_succ_lt hκ_inf hsup
  have hbdd : BddAbove (Set.range f) :=
    ⟨κ.ord, fun x ⟨i, hi⟩ => hi ▸ le_of_lt (hf i)⟩
  exact ⟨iSup f + 1, hsucc, fun i =>
    lt_of_le_of_lt (le_ciSup hbdd i) (lt_add_of_pos_right _ zero_lt_one)⟩

/-- **No surjection from small families**: For regular uncountable κ,
    no family of ordinals below κ.ord indexed by a type of size < κ
    can surject onto all ordinals below κ.ord. -/
theorem regular_no_surjection {κ : Cardinal.{u}} (hκ : κ.IsRegular)
    (hκ_inf : ℵ₀ ≤ κ) {ι : Type u} (hι : #ι < κ)
    (f : ι → Ordinal.{u}) (hf : ∀ i, f i < κ.ord) :
    ¬ (∀ α, α < κ.ord → ∃ i, f i = α) := by
  intro hf_surj
  obtain ⟨β, hβlt, hβgt⟩ := regular_diagonal hκ hκ_inf hι f hf
  obtain ⟨i, hi⟩ := hf_surj β hβlt
  exact absurd (hi ▸ hβgt i) (lt_irrefl _)

-- ══════════════════════════════════════════════════════════════════
-- § Part IV: Recovering the ℵ₁ Case
-- ══════════════════════════════════════════════════════════════════

/-- ℵ₀ < ℵ₁ (used to instantiate the general theorem). -/
private theorem aleph0_lt_aleph1 : (ℵ₀ : Cardinal.{0}) < Cardinal.aleph 1 := by
  rw [show ℵ₀ = Cardinal.aleph 0 from Cardinal.aleph_zero.symm]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- The ℵ₁ case: the classical diagonal argument for countable ordinals.
    For any countable sequence of countable ordinals, there exists a countable
    ordinal strictly above all of them. -/
theorem aleph1_diagonal (f : ℕ → Ordinal.{0})
    (hf : ∀ n, f n < (Cardinal.aleph 1).ord) :
    ∃ β, β < (Cardinal.aleph 1).ord ∧ ∀ n, f n < β := by
  exact regular_diagonal Cardinal.isRegular_aleph_one
    (le_of_lt aleph0_lt_aleph1)
    (Cardinal.mk_nat ▸ aleph0_lt_aleph1) f hf

-- ══════════════════════════════════════════════════════════════════
-- § Summary
-- ══════════════════════════════════════════════════════════════════

/-
**The Generalized Cantor Diagonal Argument**:

For any regular uncountable cardinal κ:
- The initial ordinal κ.ord is a limit ordinal (ord_succ_lt)
- Any < κ-sized family of ordinals below κ.ord has bounded sup (regularity)
- Therefore there exists an ordinal below κ.ord above the entire family
- No < κ-sized set can surject onto ordinals below κ.ord

The key property is REGULARITY, not mere uncountability. Singular cardinals
(like ℵ_ω) do NOT satisfy this — there IS a countable cofinal sequence.

Applications:
- κ = ℵ₁: "countable ordinals are uncountable" (parent OQ-02)
- κ = ℵ_{α+1}: successor alephs are always regular (Hausdorff)
- Captures the common structure of all diagonal-type arguments
-/

end CantorDiagonalizationOQ02OQ03
