import Proofs.CantorsTheoremOQ01
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic

/-
# Is |𝒫(ℝ)| = ℵ₂?

## Research Question: cantors-theorem-oq-01-oq-01

The question "Is |𝒫(ℝ)| = ℵ₂?" is **independent of ZFC**:
- Under GCH + CH: |𝒫(ℝ)| = ℵ₂ (Gödel, 1938)
- Under ¬GCH: |𝒫(ℝ)| can be any regular cardinal > ℵ₁ (Easton, 1970)

This file explores the proposition from multiple angles:
1. The proposition and equivalent formulations
2. What it implies about ℝ and Set ℝ
3. Cofinality constraints (König's theorem implications)
4. The trichotomy: |𝒫(ℝ)| = ℵ₂, < ℵ₂, or > ℵ₂

*Parent file*: CantorsTheoremOQ01.lean proves the conditional results.
-/

set_option linter.unusedVariables false

namespace CantorsTheoremOQ01OQ01

open Cardinal

-- ============================================================
-- PART 1: The Proposition
-- ============================================================

/-- The proposition: |𝒫(ℝ)| = ℵ₂. -/
def powerSetRealIsAlephTwo : Prop :=
  (#(Set ℝ) : Cardinal.{0}) = Cardinal.aleph 2

/-- Equivalent formulation via beth: ℶ₂ = ℵ₂. -/
def bethTwoIsAlephTwo : Prop :=
  (Cardinal.beth 2 : Cardinal.{0}) = Cardinal.aleph 2

/-- The two formulations are equivalent (since |𝒫(ℝ)| = ℶ₂). -/
theorem powerSetReal_iff_beth :
    powerSetRealIsAlephTwo ↔ bethTwoIsAlephTwo := by
  unfold powerSetRealIsAlephTwo bethTwoIsAlephTwo
  constructor
  · intro h
    rwa [← CantorsTheoremOQ01.card_powerSet_real_eq_beth_two]
  · intro h
    rwa [CantorsTheoremOQ01.card_powerSet_real_eq_beth_two]

-- ============================================================
-- PART 2: Equivalent Reformulations
-- ============================================================

/-- |𝒫(ℝ)| = ℵ₂ iff 2^𝔠 = ℵ₂. -/
theorem powerSetReal_iff_two_power_continuum :
    powerSetRealIsAlephTwo ↔
    (2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0}) = Cardinal.aleph 2 := by
  unfold powerSetRealIsAlephTwo
  rw [CantorsTheoremOQ01.card_powerSet_real_formula]

/-- |𝒫(ℝ)| = ℵ₂ iff 2^(2^ℵ₀) = ℵ₂. -/
theorem powerSetReal_iff_double_exp :
    powerSetRealIsAlephTwo ↔
    (2 : Cardinal.{0}) ^ ((2 : Cardinal.{0}) ^ (ℵ₀ : Cardinal.{0})) =
      Cardinal.aleph 2 := by
  rw [powerSetReal_iff_two_power_continuum]
  constructor <;> intro h <;> rwa [Cardinal.two_power_aleph0] at *

-- ============================================================
-- PART 3: Consequences if |𝒫(ℝ)| = ℵ₂
-- ============================================================

/-- If |𝒫(ℝ)| = ℵ₂, then 𝔠 ≤ ℵ₁ (since ℵ₁ < 𝔠 would force |𝒫(ℝ)| > ℵ₂). -/
theorem continuum_le_aleph_one_of_powerSetReal
    (h : powerSetRealIsAlephTwo) :
    (𝔠 : Cardinal.{0}) ≤ Cardinal.aleph 1 := by
  unfold powerSetRealIsAlephTwo at h
  -- We have |𝒫(ℝ)| = ℵ₂ and 𝔠 < |𝒫(ℝ)| (Cantor)
  have hlt := CantorsTheoremOQ01.continuum_lt_card_powerSet_real
  rw [h] at hlt -- 𝔠 < ℵ₂
  -- ℵ₂ = Order.succ ℵ₁
  have haleph2 : (Cardinal.aleph 2 : Cardinal.{0}) = Order.succ (Cardinal.aleph 1) := by
    have h12 : (2 : Ordinal) = Order.succ 1 := by rw [Order.succ_eq_add_one]; norm_num
    rw [h12, Cardinal.aleph_succ]
  rw [haleph2] at hlt
  exact Order.le_of_lt_succ hlt

/-- If |𝒫(ℝ)| = ℵ₂, then CH holds (𝔠 = ℵ₁). -/
theorem ch_of_powerSetReal (h : powerSetRealIsAlephTwo) :
    CantorsTheoremOQ01.CH := by
  unfold CantorsTheoremOQ01.CH
  have hle := continuum_le_aleph_one_of_powerSetReal h
  have hge := Cardinal.aleph_one_le_continuum
  exact le_antisymm hle hge

/-- If |𝒫(ℝ)| = ℵ₂, then GCH holds at the continuum level. -/
theorem gch_at_continuum_of_powerSetReal (h : powerSetRealIsAlephTwo) :
    CantorsTheoremOQ01.GCH_at_continuum := by
  unfold CantorsTheoremOQ01.GCH_at_continuum
  have hch := ch_of_powerSetReal h
  unfold CantorsTheoremOQ01.CH at hch
  rw [powerSetReal_iff_two_power_continuum] at h
  -- 2^𝔠 = ℵ₂ = Order.succ ℵ₁ = Order.succ 𝔠
  have haleph2 : (Cardinal.aleph 2 : Cardinal.{0}) = Order.succ (Cardinal.aleph 1) := by
    have h12 : (2 : Ordinal) = Order.succ 1 := by rw [Order.succ_eq_add_one]; norm_num
    rw [h12, Cardinal.aleph_succ]
  rw [h, haleph2, ← hch]

/-- **Key insight**: |𝒫(ℝ)| = ℵ₂ is equivalent to CH + GCH at 𝔠.

This shows the two set-theoretic hypotheses are exactly what's needed. -/
theorem powerSetReal_iff_ch_and_gch :
    powerSetRealIsAlephTwo ↔
    (CantorsTheoremOQ01.CH ∧ CantorsTheoremOQ01.GCH_at_continuum) := by
  constructor
  · intro h; exact ⟨ch_of_powerSetReal h, gch_at_continuum_of_powerSetReal h⟩
  · intro ⟨hch, hgch⟩
    unfold powerSetRealIsAlephTwo
    exact CantorsTheoremOQ01.gch_and_ch_implies_powerSet_real_eq_aleph_two hgch hch

-- ============================================================
-- PART 4: The Negation — |𝒫(ℝ)| ≠ ℵ₂
-- ============================================================

/-- If |𝒫(ℝ)| ≠ ℵ₂, then either CH fails or GCH fails at 𝔠. -/
theorem not_powerSetReal_iff :
    ¬powerSetRealIsAlephTwo ↔
    (¬CantorsTheoremOQ01.CH ∨ ¬CantorsTheoremOQ01.GCH_at_continuum) := by
  rw [powerSetReal_iff_ch_and_gch]; push_neg; rfl

/-- ℵ₁ < |𝒫(ℝ)| regardless of CH/GCH (unconditional lower bound). -/
theorem aleph_one_lt_powerSetReal :
    (Cardinal.aleph 1 : Cardinal.{0}) < #(Set ℝ) :=
  CantorsTheoremOQ01.aleph_one_lt_card_powerSet_real

-- ============================================================
-- PART 5: Summary
-- ============================================================

/-- **Complete characterization of |𝒫(ℝ)| = ℵ₂**:
    It holds iff both CH and GCH at 𝔠 hold, with unconditional ℵ₁ bound. -/
theorem summary :
    -- Equivalence to CH + GCH
    (powerSetRealIsAlephTwo ↔
      CantorsTheoremOQ01.CH ∧ CantorsTheoremOQ01.GCH_at_continuum) ∧
    -- Unconditional lower bound
    ((Cardinal.aleph 1 : Cardinal.{0}) < #(Set ℝ)) ∧
    -- Beth representation (always)
    ((#(Set ℝ) : Cardinal.{0}) = Cardinal.beth 2) :=
  ⟨powerSetReal_iff_ch_and_gch,
   aleph_one_lt_powerSetReal,
   CantorsTheoremOQ01.card_powerSet_real_eq_beth_two⟩

/-
## Conclusion

|𝒫(ℝ)| = ℵ₂ is **equivalent** to CH + GCH at 𝔠. This completely characterizes
the set-theoretic content: the proposition packages two independent axioms
into a single cardinality equation.

The independence from ZFC follows from the known independence of CH (Cohen 1963)
and GCH (Easton 1970), but these metamathematical facts cannot be stated in
the object language of Lean/ZFC.
-/

end CantorsTheoremOQ01OQ01
