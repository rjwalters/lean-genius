import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic

/-
# The Cardinality of 𝒫(ℝ): What is |P(R)|?

## Open Question: cantors-theorem-oq-01

**Question**: What is the cardinality of the power set of the real numbers, 𝒫(ℝ)?

This question has a definitive ZFC answer: |𝒫(ℝ)| = 2^|ℝ| = 2^𝔠 = 2^(2^ℵ₀) = ℶ₂.

But there is a residual **open question** in ZFC: what is this cardinality in the
*aleph hierarchy*? Under the Generalized Continuum Hypothesis (GCH), |𝒫(ℝ)| = ℵ₂.
Without GCH, the aleph-index of 2^𝔠 is undetermined — independent of ZFC.

## What We Prove

### ✅ Provable in ZFC:
- `card_real_eq_continuum` — |ℝ| = 𝔠 = 2^ℵ₀
- `card_powerSet_real_formula` — |𝒫(ℝ)| = 2^𝔠 = 2^(2^ℵ₀)
- `card_real_lt_card_powerSet_real` — |ℝ| < |𝒫(ℝ)| (Cantor's theorem)
- `card_powerSet_real_eq_beth_two` — |𝒫(ℝ)| = ℶ₂ (second beth number)
- `aleph_one_lt_card_powerSet_real` — ℵ₁ < |𝒫(ℝ)|
- `aleph_two_le_card_powerSet_real_of_not_CH` — ℵ₂ ≤ |𝒫(ℝ)| (under ¬CH)

### ❌ Cannot be proved in ZFC alone (independent):
- Whether |𝒫(ℝ)| = ℵ₂ (GCH for the second level)
- The exact aleph-index of 2^𝔠

## Historical Context

The beth hierarchy: ℶ₀ = ℵ₀ = |ℕ|, ℶ₁ = 2^ℵ₀ = 𝔠 = |ℝ|, ℶ₂ = 2^𝔠 = |𝒫(ℝ)|.
Under GCH + CH: ℶ₂ = ℵ₂. Without GCH, Easton's theorem shows ℶ₂ can be
almost any regular cardinal above ℵ₁.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorsTheoremOQ01

open Cardinal

-- ============================================================
-- PART 1: The Cardinality of ℝ
-- ============================================================

/-- **The cardinality of ℝ equals the continuum 𝔠 = 2^ℵ₀**.
    This is Mathlib's `Cardinal.mk_real`. -/
theorem card_real_eq_continuum : (#ℝ : Cardinal.{0}) = 𝔠 :=
  Cardinal.mk_real

/-- ℝ is strictly larger than ℕ: |ℝ| = 𝔠 > ℵ₀. -/
theorem card_real_gt_aleph_zero : (ℵ₀ : Cardinal.{0}) < #ℝ := by
  rw [card_real_eq_continuum]
  exact Cardinal.aleph0_lt_continuum

-- ============================================================
-- PART 2: The Power Set Formula for ℝ
-- ============================================================

/-- The power set formula: |𝒫(α)| = 2^|α| (Mathlib's `Cardinal.mk_set`). -/
theorem card_set_formula (α : Type*) : #(Set α) = 2 ^ #α :=
  Cardinal.mk_set

/-- **|𝒫(ℝ)| = 2^𝔠**: The power set of ℝ has cardinality 2^𝔠 = 2^(2^ℵ₀). -/
theorem card_powerSet_real_formula : (#(Set ℝ) : Cardinal.{0}) = 2 ^ 𝔠 := by
  rw [Cardinal.mk_set, card_real_eq_continuum]

-- ============================================================
-- PART 3: Cantor's Theorem Applied to ℝ
-- ============================================================

/-- **Cantor's Theorem for ℝ**: |ℝ| < |𝒫(ℝ)|.

    For any cardinal κ, κ < 2^κ. Applied to κ = #ℝ = 𝔠, this gives
    the fundamental strict inequality: the power set strictly exceeds ℝ. -/
theorem card_real_lt_card_powerSet_real : (#ℝ : Cardinal.{0}) < #(Set ℝ) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor #ℝ

/-- |𝒫(ℝ)| is uncountable. -/
theorem card_powerSet_real_gt_aleph_zero : (ℵ₀ : Cardinal.{0}) < #(Set ℝ) :=
  lt_trans card_real_gt_aleph_zero card_real_lt_card_powerSet_real

/-- |𝒫(ℝ)| strictly exceeds the continuum 𝔠. -/
theorem continuum_lt_card_powerSet_real : (𝔠 : Cardinal.{0}) < #(Set ℝ) :=
  card_real_eq_continuum ▸ card_real_lt_card_powerSet_real

-- ============================================================
-- PART 4: Beth Number Interpretation
-- ============================================================

/-
  The beth number hierarchy: ℶ₀ = ℵ₀, ℶ₁ = 2^ℵ₀ = 𝔠, ℶ₂ = 2^𝔠, ...
  Each beth number is the power set of the previous one.
-/

/-- ℶ₁ = 𝔠: the first beth number equals the continuum. -/
theorem beth_one_eq_continuum : (Cardinal.beth 1 : Cardinal.{0}) = 𝔠 := by
  have h1 : (1 : Ordinal) = Order.succ 0 := by rw [Order.succ_eq_add_one]; norm_num
  rw [h1, Cardinal.beth_succ, Cardinal.beth_zero]
  exact Cardinal.two_power_aleph0

/-- **|𝒫(ℝ)| = ℶ₂**: The power set of ℝ is the second beth number.

    ℶ₀ = ℵ₀ = |ℕ|, ℶ₁ = 2^ℵ₀ = 𝔠 = |ℝ|, ℶ₂ = 2^𝔠 = |𝒫(ℝ)|. -/
theorem card_powerSet_real_eq_beth_two : (#(Set ℝ) : Cardinal.{0}) = Cardinal.beth 2 := by
  rw [card_powerSet_real_formula]
  -- ℶ₂ = 2^ℶ₁ (beth succ formula)
  have h2 : (Cardinal.beth 2 : Cardinal.{0}) = 2 ^ Cardinal.beth 1 := by
    have h12 : (2 : Ordinal) = Order.succ 1 := by rw [Order.succ_eq_add_one]; norm_num
    rw [h12, Cardinal.beth_succ]
  -- ℶ₁ = 𝔠 (beth₁ = continuum)
  rw [h2, beth_one_eq_continuum]

/-- ℶ₂ > ℶ₁ = 𝔠: the beth tower is strictly increasing. -/
theorem beth_two_gt_beth_one : (Cardinal.beth 1 : Cardinal.{0}) < Cardinal.beth 2 :=
  Cardinal.beth_strictMono (by exact_mod_cast (show (1 : ℕ) < 2 from by norm_num))

-- ============================================================
-- PART 5: Position in the Aleph Hierarchy
-- ============================================================

/-- **ℵ₁ ≤ 𝔠**: The continuum is at least ℵ₁ (provable in ZFC). -/
theorem aleph_one_le_continuum_zfc : (Cardinal.aleph 1 : Cardinal.{0}) ≤ 𝔠 :=
  Cardinal.aleph_one_le_continuum

/-- **ℵ₁ < |𝒫(ℝ)|**: The power set of ℝ is strictly above ℵ₁. -/
theorem aleph_one_lt_card_powerSet_real : (Cardinal.aleph 1 : Cardinal.{0}) < #(Set ℝ) :=
  lt_of_le_of_lt aleph_one_le_continuum_zfc continuum_lt_card_powerSet_real

/-- The Continuum Hypothesis at universe level 0. -/
def CH : Prop := (𝔠 : Cardinal.{0}) = Cardinal.aleph 1

/-- Under ¬CH, the continuum strictly exceeds ℵ₁. -/
theorem not_ch_continuum_gt_aleph_one (hnch : ¬CH) : (Cardinal.aleph 1 : Cardinal.{0}) < 𝔠 := by
  rcases lt_or_eq_of_le aleph_one_le_continuum_zfc with h | h
  · exact h
  · exfalso; exact hnch h.symm

/-- Under ¬CH, ℵ₂ ≤ |𝒫(ℝ)|.

    If ¬CH: ℵ₁ < 𝔠, so ℵ₂ = (ℵ₁)⁺ ≤ 𝔠 ≤ |𝒫(ℝ)|. -/
theorem aleph_two_le_card_powerSet_real_of_not_CH (hnch : ¬CH) :
    (Cardinal.aleph 2 : Cardinal.{0}) ≤ #(Set ℝ) := by
  have h1 : (Cardinal.aleph 1 : Cardinal.{0}) < 𝔠 := not_ch_continuum_gt_aleph_one hnch
  have h2 : (Cardinal.aleph 2 : Cardinal.{0}) = Order.succ (Cardinal.aleph 1) := by
    have h12 : (2 : Ordinal) = Order.succ (1 : Ordinal) := by
      rw [Order.succ_eq_add_one]; norm_num
    rw [h12, Cardinal.aleph_succ]
  rw [h2]
  exact le_trans (Order.succ_le_of_lt h1)
    (le_of_lt continuum_lt_card_powerSet_real)

-- ============================================================
-- PART 6: The GCH Question — Open in ZFC
-- ============================================================

/-
  The Generalized Continuum Hypothesis (GCH) at the continuum level:
  2^𝔠 = (𝔠)⁺ (the successor of 𝔠)

  Under CH + GCH: 𝔠 = ℵ₁, so (𝔠)⁺ = ℵ₂, giving |𝒫(ℝ)| = ℵ₂.
  This is independent of ZFC (Gödel 1938, Cohen 1963, Easton 1970).
-/

/-- GCH at the continuum level: 2^𝔠 equals the successor cardinal of 𝔠. -/
def GCH_at_continuum : Prop :=
  (2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0}) = Order.succ (𝔠 : Cardinal.{0})

/-- Under CH + GCH at 𝔠, the power set of ℝ equals ℵ₂. -/
theorem gch_and_ch_implies_powerSet_real_eq_aleph_two
    (hgch : GCH_at_continuum) (hch : CH) :
    (#(Set ℝ) : Cardinal.{0}) = Cardinal.aleph 2 := by
  rw [card_powerSet_real_formula]
  unfold GCH_at_continuum at hgch
  unfold CH at hch
  -- ℵ₂ = Order.succ ℵ₁
  have haleph2 : (Cardinal.aleph 2 : Cardinal.{0}) = Order.succ (Cardinal.aleph 1) := by
    have h12 : (2 : Ordinal) = Order.succ 1 := by rw [Order.succ_eq_add_one]; norm_num
    rw [h12, Cardinal.aleph_succ]
  -- ℵ₂ = Order.succ ℵ₁ = Order.succ 𝔠 (by CH), and 2^𝔠 = Order.succ 𝔠 (by GCH)
  rw [haleph2, ← hch]
  exact hgch

/-- Under ¬GCH at 𝔠 (with CH), the power set of ℝ exceeds ℵ₂.

    When GCH fails at 𝔠: 2^𝔠 > (𝔠)⁺. Under CH, (𝔠)⁺ = ℵ₂. -/
theorem not_gch_at_continuum_implies_gt_aleph_two
    (hngch : ¬GCH_at_continuum) (hch : CH) :
    (Cardinal.aleph 2 : Cardinal.{0}) < #(Set ℝ) := by
  rw [card_powerSet_real_formula]
  unfold GCH_at_continuum at hngch
  unfold CH at hch
  -- (𝔠)⁺ < 2^𝔠 (strict from Cantor + ¬GCH)
  have hsucc_le : Order.succ (𝔠 : Cardinal.{0}) ≤ (2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0}) :=
    Order.succ_le_of_lt (Cardinal.cantor (𝔠 : Cardinal.{0}))
  have hlt : Order.succ (𝔠 : Cardinal.{0}) < (2 : Cardinal.{0}) ^ (𝔠 : Cardinal.{0}) :=
    lt_of_le_of_ne hsucc_le (Ne.symm hngch)
  -- ℵ₂ = Order.succ ℵ₁ = Order.succ 𝔠 (using CH: 𝔠 = ℵ₁)
  have haleph2 : (Cardinal.aleph 2 : Cardinal.{0}) = Order.succ (Cardinal.aleph 1) := by
    have h12 : (2 : Ordinal) = Order.succ 1 := by rw [Order.succ_eq_add_one]; norm_num
    rw [h12, Cardinal.aleph_succ]
  rw [haleph2, ← hch]
  exact hlt

-- ============================================================
-- PART 7: König's Constraint on |𝒫(ℝ)|
-- ============================================================

/-
  König's theorem (1905): cf(2^𝔠) > 𝔠.

  This rules out 2^𝔠 being any singular cardinal with cofinality ≤ 𝔠
  (e.g., ℵ_ω has cofinality ω ≤ 𝔠, so |𝒫(ℝ)| ≠ ℵ_ω).

  **Formalized in** `Proofs/CantorsTheoremOQ01OQ03.lean` (open question
  `cantors-theorem-oq-01-oq-03`, resolved YES on 2026-05-12). Key
  theorems available there:

  * `CantorsTheoremOQ01OQ03.konig_general` —
    `∀ {κ : Cardinal.{0}}, ℵ₀ ≤ κ → κ < (2 ^ κ).ord.cof`,
    König's cofinality bound in full generality, proved as an
    immediate corollary of Mathlib's `Cardinal.lt_cof_power`.

  * `CantorsTheoremOQ01OQ03.cf_powerSet_real_gt_continuum` —
    `𝔠 < (#(Set ℝ)).ord.cof`, the application to |𝒫(ℝ)|.

  * `CantorsTheoremOQ01OQ03.cf_powerSet_real_ne_aleph0` —
    `(#(Set ℝ)).ord.cof ≠ ℵ₀`, the singular-ruling-out corollary
    that justifies the `|𝒫(ℝ)| ≠ ℵ_ω` slogan above (any ZFC model
    with `|𝒫(ℝ)| = ℵ_ω` would force the cofinality to be ℵ₀).

  We deliberately do *not* `import Proofs.CantorsTheoremOQ01OQ03`
  here: that file imports *this* file as its parent, so the import
  direction is fixed (child → parent). Readers wanting the
  machine-checked statement should open the child file directly.
-/

-- ============================================================
-- PART 8: Summary
-- ============================================================

/-- **All ZFC-provable facts about |𝒫(ℝ)|**.

    1. Power set formula: |𝒫(ℝ)| = 2^𝔠
    2. Cantor strict inequality: |ℝ| < |𝒫(ℝ)|
    3. Beth tower: |𝒫(ℝ)| = ℶ₂
    4. Aleph lower bound: ℵ₁ < |𝒫(ℝ)|

    **Open question**: What is the aleph-index of ℶ₂?
    - Under GCH + CH: ℶ₂ = ℵ₂ (provable)
    - Without GCH: undetermined (independent of ZFC, via Easton's theorem) -/
theorem cantors_theorem_oq01_summary :
    -- 1. Power set formula
    ((#(Set ℝ) : Cardinal.{0}) = 2 ^ 𝔠) ∧
    -- 2. Cantor strict inequality
    ((#ℝ : Cardinal.{0}) < #(Set ℝ)) ∧
    -- 3. Beth₂ representation
    ((#(Set ℝ) : Cardinal.{0}) = Cardinal.beth 2) ∧
    -- 4. ℵ₁ lower bound
    ((Cardinal.aleph 1 : Cardinal.{0}) < #(Set ℝ)) :=
  ⟨card_powerSet_real_formula,
   card_real_lt_card_powerSet_real,
   card_powerSet_real_eq_beth_two,
   aleph_one_lt_card_powerSet_real⟩

/-
## Conclusion

|𝒫(ℝ)| = 2^𝔠 = 2^(2^ℵ₀) = ℶ₂, the second beth number.

The beth tower: ℶ₀ = ℵ₀ = |ℕ|, ℶ₁ = 𝔠 = |ℝ|, ℶ₂ = |𝒫(ℝ)|.

The residual open question: what is the aleph-index of ℶ₂?
- Under GCH + CH: |𝒫(ℝ)| = ℵ₂
- Without GCH: König rules out many values, but the exact index
  is independent of ZFC (Easton's theorem, 1970)
-/

end CantorsTheoremOQ01

-- Export key theorems
#check CantorsTheoremOQ01.card_powerSet_real_formula
#check CantorsTheoremOQ01.card_real_lt_card_powerSet_real
#check CantorsTheoremOQ01.card_powerSet_real_eq_beth_two
#check CantorsTheoremOQ01.aleph_one_lt_card_powerSet_real
#check CantorsTheoremOQ01.cantors_theorem_oq01_summary
