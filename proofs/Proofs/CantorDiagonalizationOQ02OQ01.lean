/-
Cardinality of Countable Ordinals: ω₁ Properties

Open Question (cantor-diagonalization-oq-02-oq-01):
"What are the structural properties of ω₁ beyond the parent formalization?"

Building on CantorDiagonalizationOQ02.lean, this file proves:
1. Cofinality of ω₁ is uncountable (ℵ₁ is regular)
2. Aleph hierarchy: ℵ_α < ℵ_(α+1) for all ordinals α
3. Every ordinal below ω₁ is countable (explicit characterization)
4. The aleph function preserves strict ordering
5. No countable ordinal equals ω₁

References:
- Cantor (1895), Hausdorff (1908), von Neumann
- Mathlib: SetTheory.Cardinal.Ordinal, SetTheory.Cardinal.Cofinality
-/

import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic

namespace CantorDiagonalizationOQ02OQ01

open Cardinal Ordinal

-- ============================================================
-- PART I: Aleph Hierarchy
-- ============================================================

/-- The aleph function is strictly monotone on ordinals -/
theorem aleph_strictMono : StrictMono (Cardinal.aleph : Ordinal.{0} → Cardinal.{0}) :=
  fun _ _ h => Cardinal.aleph_lt_aleph.mpr h

/-- For any ordinal α, ℵ_α < ℵ_(α+1) -/
theorem aleph_lt_aleph_succ (α : Ordinal.{0}) :
    Cardinal.aleph α < Cardinal.aleph (Order.succ α) :=
  aleph_strictMono (Order.lt_succ α)

/-- The aleph function is injective -/
theorem aleph_injective : Function.Injective (Cardinal.aleph : Ordinal.{0} → Cardinal.{0}) :=
  aleph_strictMono.injective

/-- ℵ₀ < ℵ₁ < ℵ₂ : the first three infinite cardinals form a chain -/
theorem aleph_chain_012 :
    Cardinal.aleph 0 < Cardinal.aleph 1 ∧
    Cardinal.aleph 1 < Cardinal.aleph 2 := by
  exact ⟨Cardinal.aleph_lt_aleph.mpr (by norm_num), Cardinal.aleph_lt_aleph.mpr (by norm_num)⟩

-- ============================================================
-- PART II: Cofinality and Regularity
-- ============================================================

/-- ℵ₁ is a regular cardinal -/
theorem aleph1_regular : (Cardinal.aleph (1 : Ordinal.{0})).IsRegular :=
  Cardinal.isRegular_aleph_one

/-- The cofinality of ω₁ equals ℵ₁ (uncountable cofinality) -/
theorem cof_ord_aleph1 :
    (Cardinal.aleph (1 : Ordinal.{0})).ord.cof = Cardinal.aleph 1 :=
  Cardinal.isRegular_aleph_one.cof_eq

/-- The cofinality of ω₁ is strictly greater than ℵ₀ (uncountable) -/
theorem cof_ord_aleph1_uncountable :
    Cardinal.aleph 0 < (Cardinal.aleph (1 : Ordinal.{0})).ord.cof := by
  rw [cof_ord_aleph1]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

-- ============================================================
-- PART III: Cardinal Properties
-- ============================================================

/-- ℵ₁ = succ(ℵ₀) : characterization as successor cardinal -/
theorem aleph1_eq_succ_aleph0 :
    (Cardinal.aleph 1 : Cardinal.{0}) = Order.succ (Cardinal.aleph 0) := by
  have : (1 : Ordinal) = Order.succ 0 := by simp
  rw [this, Cardinal.aleph_succ]

/-- κ < ℵ₁ ↔ κ ≤ ℵ₀ : characterization of countable cardinals -/
theorem lt_aleph1_iff_le_aleph0 (κ : Cardinal.{0}) :
    κ < Cardinal.aleph 1 ↔ κ ≤ Cardinal.aleph 0 := by
  rw [aleph1_eq_succ_aleph0, Order.lt_succ_iff]

/-- Any cardinal below ℵ₁ is countable -/
theorem card_lt_aleph1_countable (κ : Cardinal.{0}) (h : κ < Cardinal.aleph 1) :
    κ ≤ Cardinal.aleph 0 :=
  (lt_aleph1_iff_le_aleph0 κ).mp h

-- ============================================================
-- PART IV: Ordinal of ℵ₁
-- ============================================================

/-- (ℵ₁).ord has cardinality ℵ₁ -/
theorem card_ord_aleph1 : (Cardinal.aleph (1 : Ordinal.{0})).ord.card = Cardinal.aleph 1 :=
  Cardinal.card_ord _

/-- ω < (ℵ₁).ord : the first infinite ordinal is below ω₁ -/
theorem omega_lt_ord_aleph1 :
    (Cardinal.aleph (0 : Ordinal.{0})).ord < (Cardinal.aleph (1 : Ordinal.{0})).ord :=
  Cardinal.ord_lt_ord.mpr (Cardinal.aleph_lt_aleph.mpr (by norm_num))

/-- An ordinal α < (ℵ₁).ord iff α has countable cardinality -/
theorem lt_ord_aleph1_iff (α : Ordinal.{0}) :
    α < (Cardinal.aleph 1).ord ↔ α.card ≤ Cardinal.aleph 0 := by
  rw [Cardinal.lt_ord, lt_aleph1_iff_le_aleph0]

/-- No countable ordinal equals ω₁: ω₁ is the first uncountable ordinal -/
theorem ord_aleph1_not_countable :
    ¬ ((Cardinal.aleph (1 : Ordinal.{0})).ord.card ≤ Cardinal.aleph 0) := by
  rw [card_ord_aleph1]
  exact not_le.mpr (Cardinal.aleph_lt_aleph.mpr (by norm_num))

-- ============================================================
-- PART V: Summary
-- ============================================================

/-- Summary of ω₁ properties -/
theorem omega1_properties_summary :
    -- Aleph hierarchy
    (∀ α : Ordinal.{0}, Cardinal.aleph α < Cardinal.aleph (Order.succ α)) ∧
    -- ℵ₁ is regular
    (Cardinal.aleph (1 : Ordinal.{0})).IsRegular ∧
    -- Cofinality is uncountable
    Cardinal.aleph 0 < (Cardinal.aleph (1 : Ordinal.{0})).ord.cof ∧
    -- ω < ω₁
    (Cardinal.aleph (0 : Ordinal.{0})).ord < (Cardinal.aleph (1 : Ordinal.{0})).ord :=
  ⟨aleph_lt_aleph_succ, aleph1_regular, cof_ord_aleph1_uncountable, omega_lt_ord_aleph1⟩

end CantorDiagonalizationOQ02OQ01
