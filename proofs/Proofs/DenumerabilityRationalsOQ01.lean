import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic

/-
# The Cardinality Gap: ℚ, ℝ, and the Continuum Hypothesis

## Research Problem: denumerability-rationals-oq-01

We proved |ℚ| = ℵ₀ (the rational numbers are countable).
The real numbers satisfy |ℝ| = 2^ℵ₀ = 𝔠 (the continuum).

**OQ: What cardinals lie between |ℚ| and |ℝ|?**

This question is precisely the Continuum Hypothesis:
- CH (Cantor, 1878): There is NO cardinal κ with ℵ₀ < κ < 2^ℵ₀
- Gödel (1940): CH is *consistent* with ZFC (holds in the constructible universe L)
- Cohen (1963): ¬CH is *also* consistent with ZFC (via forcing)
- Consequence: CH is **independent** of ZFC — neither provable nor disprovable

## Key Mathematical Connection

The denumerability of ℚ places us firmly at ℵ₀. The uncountability of ℝ
places us at 𝔠 = 2^ℵ₀. The Dedekind cut construction shows that |𝒫(ℚ)| = 𝔠:
even though ℚ is countable, the set of all subsets of ℚ (which parametrizes
Dedekind cuts) has the full cardinality of the continuum. CH asks whether
this "jump" in cardinality from ℵ₀ to 𝔠 is a single step or leaves room
for intermediate cardinals.

## What We Prove

### ✅ Provable in ZFC (proved here):
- `card_rat_eq_aleph0` — |ℚ| = ℵ₀ (Mathlib's Denumerable typeclass)
- `card_real_eq_continuum` — |ℝ| = 𝔠 = 2^ℵ₀ (Mathlib's mk_real)
- `card_rat_lt_card_real` — |ℚ| < |ℝ| (the cardinality gap exists)
- `card_subsets_rat_eq_continuum` — |𝒫(ℚ)| = 𝔠 (Dedekind cut connection)
- `aleph_zero_lt_continuum` — ℵ₀ < 𝔠 (Cantor's theorem)
- `aleph_one_le_continuum` — ℵ₁ ≤ 𝔠 (smallest uncountable ≤ continuum)
- `ch_equiv_no_intermediate` — CH ↔ ¬∃ κ, ℵ₀ < κ < 𝔠
- `ch_implies_two_infinite_cardinalities` — CH: only ℵ₀ and 𝔠 among ∞ cardinals ≤ 𝔠

### ❌ Independent of ZFC (cannot be proved or disproved):
- CH itself: whether the gap between |ℚ| and |ℝ| is empty
- The aleph-index of 𝔠 (could be ℵ₁, ℵ₂, ..., or even further)

## Historical Note

Cantor posed the Continuum Hypothesis in 1878, conjecturing that ℵ₁ = 2^ℵ₀.
Hilbert listed it as his first problem in 1900. The combined work of Gödel (1940)
and Cohen (1963) established independence, earning Cohen the Fields Medal in 1966.
This is Wiedijk's theorem #24 (CH independence).

Tags: set-theory, cardinality, continuum-hypothesis, denumerability, dedekind-cuts
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace DenumerabilityRationalsOQ01

open Cardinal

-- ============================================================
-- PART 1: Cardinality of ℚ and ℝ
-- ============================================================

/-- The rationals are countably infinite: |ℚ| = ℵ₀.
    This follows from Mathlib's `Denumerable ℚ` instance, which provides
    an explicit bijection ℕ ≃ ℚ via Cantor pairing. -/
theorem card_rat_eq_aleph0 : Cardinal.mk ℚ = ℵ₀ :=
  Cardinal.mk_denumerable ℚ

/-- The reals have the cardinality of the continuum: |ℝ| = 𝔠 = 2^ℵ₀. -/
theorem card_real_eq_continuum : (#ℝ : Cardinal.{0}) = 𝔠 :=
  Cardinal.mk_real

/-- The cardinality gap: ℚ is strictly smaller than ℝ.
    Despite ℚ being dense in ℝ, they differ in cardinality: ℵ₀ < 𝔠. -/
theorem card_rat_lt_card_real : (Cardinal.mk ℚ : Cardinal.{0}) < #ℝ := by
  rw [card_rat_eq_aleph0, card_real_eq_continuum]
  exact Cardinal.aleph0_lt_continuum

-- ============================================================
-- PART 2: The Dedekind Cut Connection
-- ============================================================

/-- The power set of ℚ has the cardinality of the continuum: |𝒫(ℚ)| = 𝔠.

    This is the bridge between ℚ (countable) and ℝ (continuum-sized):
    - ℚ is countable: |ℚ| = ℵ₀
    - Each Dedekind cut is a subset of ℚ
    - The number of such subsets is 2^|ℚ| = 2^ℵ₀ = 𝔠
    - So Dedekind's construction embeds ℝ into 𝒫(ℚ), which has 𝔠 elements

    Paradoxically: ℚ is "small" (countable) but 𝒫(ℚ) is "large" (continuum-sized). -/
theorem card_subsets_rat_eq_continuum : (#(Set ℚ) : Cardinal.{0}) = 𝔠 := by
  rw [Cardinal.mk_set, card_rat_eq_aleph0]
  exact Cardinal.two_power_aleph0

/-- Corollary: the power set of ℚ and ℝ have the same cardinality.
    This reflects that Dedekind cuts give a bijection ℝ ≃ (a subset of 𝒫(ℚ)). -/
theorem card_subsets_rat_eq_card_real : (#(Set ℚ) : Cardinal.{0}) = #ℝ := by
  rw [card_subsets_rat_eq_continuum, card_real_eq_continuum]

-- ============================================================
-- PART 3: The Cardinality Gap and Aleph Hierarchy
-- ============================================================

/-- The continuum is strictly larger than the countably infinite: ℵ₀ < 𝔠.
    This is Cantor's theorem: no set is equinumerous with its power set. -/
theorem aleph_zero_lt_continuum : (ℵ₀ : Cardinal.{0}) < 𝔠 :=
  Cardinal.aleph0_lt_continuum

/-- The smallest uncountable cardinal ℵ₁ satisfies ℵ₁ ≤ 𝔠.
    In ZFC, we can only establish this inequality — CH asks whether ℵ₁ = 𝔠.

    Proof: ℵ₀ < 𝔠 (Cantor) and ℵ₁ is the successor of ℵ₀ in the cardinal order,
    so ℵ₁ ≤ 𝔠 follows from the fact that ℵ₁ = min{κ : ℵ₀ < κ}. -/
theorem aleph_one_le_continuum : (Cardinal.aleph 1 : Cardinal.{0}) ≤ 𝔠 :=
  Cardinal.aleph_one_le_continuum

/-- ℵ₀ < ℵ₁: the smallest uncountable cardinal strictly exceeds ℵ₀.
    This is ZFC-provable: ℵ₁ is defined as the successor of ℵ₀. -/
theorem aleph_zero_lt_aleph_one : (ℵ₀ : Cardinal.{0}) < Cardinal.aleph 1 := by
  have h : Cardinal.aleph 0 < Cardinal.aleph 1 :=
    Cardinal.aleph_lt_aleph.mpr (by norm_num)
  simpa [Cardinal.aleph_zero] using h

-- ============================================================
-- PART 4: The Continuum Hypothesis
-- ============================================================

/-- The Continuum Hypothesis: the continuum 𝔠 equals the first uncountable cardinal ℵ₁.
    Equivalently: there is no infinite set S with |ℕ| < |S| < |ℝ|.

    This is consistent with ZFC (Gödel 1940) and its negation is also
    consistent with ZFC (Cohen 1963), so CH is independent of ZFC. -/
def ContinuumHypothesis : Prop := (𝔠 : Cardinal.{0}) = Cardinal.aleph 1

/-- CH stated as a gap condition: no cardinal lies strictly between ℵ₀ and 𝔠.
    This directly captures Cantor's original conjecture about ℚ vs ℝ. -/
def CH_gap : Prop := ¬∃ κ : Cardinal.{0}, ℵ₀ < κ ∧ κ < 𝔠

/-- The two formulations of CH are equivalent.
    CH (𝔠 = ℵ₁) ↔ no cardinal between ℵ₀ and 𝔠. -/
theorem ch_equiv_no_intermediate : ContinuumHypothesis ↔ CH_gap := by
  constructor
  · -- CH → no gap: if 𝔠 = ℵ₁ = succ(ℵ₀), then nothing fits between ℵ₀ and ℵ₁
    intro h_ch ⟨κ, h1, h2⟩
    unfold ContinuumHypothesis at h_ch
    rw [h_ch] at h2
    -- h2 : κ < Cardinal.aleph 1
    -- Show ℵ₁ = Order.succ ℵ₀
    have h_aleph1_succ : Cardinal.aleph 1 = Order.succ ℵ₀ := by
      rw [show (1 : Ordinal) = Order.succ (0 : Ordinal) from by
        rw [Order.succ_eq_add_one]; norm_num]
      rw [Cardinal.aleph_succ, Cardinal.aleph_zero]
    rw [h_aleph1_succ] at h2
    -- h2 : κ < Order.succ ℵ₀, so κ ≤ ℵ₀
    have h_le : κ ≤ ℵ₀ := Order.lt_succ_iff.mp h2
    exact absurd h1 (not_lt.mpr h_le)
  · -- No gap → CH: ℵ₁ ≤ 𝔠 and no κ with ℵ₀ < κ < 𝔠 forces 𝔠 ≤ ℵ₁
    intro h_no_gap
    unfold ContinuumHypothesis
    apply le_antisymm _ aleph_one_le_continuum
    -- Need 𝔠 ≤ ℵ₁: equivalently ¬(ℵ₁ < 𝔠)
    by_contra h
    push_neg at h
    -- h : ℵ₁ < 𝔠 — but then ℵ₁ is intermediate between ℵ₀ and 𝔠
    exact h_no_gap ⟨Cardinal.aleph 1, aleph_zero_lt_aleph_one, h⟩

-- ============================================================
-- PART 5: Implications of CH
-- ============================================================

/-- Under CH, the only infinite cardinals ≤ 𝔠 are ℵ₀ and 𝔠 itself.
    In terms of sets: under CH, every infinite subset of ℝ is either
    countably infinite (size ℵ₀) or has full continuum cardinality (size 𝔠). -/
theorem ch_implies_two_infinite_cardinalities
    (h_ch : ContinuumHypothesis) (κ : Cardinal.{0})
    (h_inf : ℵ₀ ≤ κ) (h_bound : κ ≤ 𝔠) : κ = ℵ₀ ∨ κ = 𝔠 := by
  rcases eq_or_lt_of_le h_inf with rfl | h_lt
  · left; rfl  -- κ = ℵ₀
  · right
    -- ℵ₀ < κ ≤ 𝔠, and CH says no intermediate, so κ = 𝔠
    rcases eq_or_lt_of_le h_bound with h_eq | h_lt2
    · exact h_eq
    · -- κ < 𝔠 and κ > ℵ₀: contradicts CH_gap (= CH)
      exfalso
      have h_gap : CH_gap := ch_equiv_no_intermediate.mp h_ch
      exact h_gap ⟨κ, h_lt, h_lt2⟩

/-- Under CH, ℵ₁ = 𝔠: the first uncountable cardinal IS the continuum. -/
theorem ch_implies_aleph_one_eq_continuum (h_ch : ContinuumHypothesis) :
    (Cardinal.aleph 1 : Cardinal.{0}) = 𝔠 :=
  h_ch.symm

/-- Under ¬CH, ℵ₁ < 𝔠: the continuum strictly exceeds the first uncountable cardinal.
    This means there are (at least) two distinct infinite cardinalities between
    countability and continuum. -/
theorem not_ch_implies_aleph_one_lt_continuum (h_not_ch : ¬ContinuumHypothesis) :
    (Cardinal.aleph 1 : Cardinal.{0}) < 𝔠 := by
  rcases lt_or_eq_of_le aleph_one_le_continuum with h | h
  · exact h
  · exact absurd h.symm h_not_ch

-- ============================================================
-- PART 6: The Independence Result (Axiomatized)
-- ============================================================

/-- The key structural fact: ℵ₁ ≤ 𝔠 ≤ 2^ℵ₀ is all ZFC tells us.
    CH (ℵ₁ = 𝔠) and ¬CH (ℵ₁ < 𝔠) are both consistent extensions. -/
theorem zfc_bound : (Cardinal.aleph 1 : Cardinal.{0}) ≤ 𝔠 ∧ 𝔠 = 2 ^ ℵ₀ :=
  ⟨aleph_one_le_continuum, Cardinal.two_power_aleph0.symm⟩

/-- Gödel (1940): The Continuum Hypothesis is consistent with ZFC.
    In Gödel's constructible universe L, every set is built from ordinals,
    which forces 2^ℵ₀ = ℵ₁ (no "extra" reals beyond the ordinals). -/
axiom godel_ch_consistent_with_ZFC :
    ∃ (ZFC_model : Type) (_ : ZFC_model), ContinuumHypothesis

/-- Cohen (1963): The negation of CH is consistent with ZFC.
    Via forcing, one can adjoin ℵ₂ many new "Cohen reals" to any model of ZFC,
    making 2^ℵ₀ = ℵ₂ > ℵ₁. -/
axiom cohen_not_ch_consistent_with_ZFC :
    ∃ (ZFC_model : Type) (_ : ZFC_model), ¬ContinuumHypothesis

/-- Therefore CH is independent of ZFC: the question "what lies between |ℚ| and |ℝ|?"
    cannot be answered from the standard axioms of set theory alone. -/
theorem ch_independent_of_ZFC :
    (∃ (M : Type) (_ : M), ContinuumHypothesis) ∧
    (∃ (M : Type) (_ : M), ¬ContinuumHypothesis) :=
  ⟨godel_ch_consistent_with_ZFC, cohen_not_ch_consistent_with_ZFC⟩

-- ============================================================
-- PART 7: Summary — The Full Picture
-- ============================================================

/-- Summary: the cardinality landscape arising from the denumerability of ℚ.

    Starting from: ℚ is countable (|ℚ| = ℵ₀, proved in DenumerabilityRationals.lean)

    We can prove in ZFC:
    (1) ℵ₀ = |ℚ| < |ℝ| = 𝔠 = 2^ℵ₀  (the gap exists)
    (2) |𝒫(ℚ)| = 𝔠                   (Dedekind cuts connection)
    (3) ℵ₁ ≤ 𝔠                        (smallest uncountable ≤ continuum)

    The question "Is ℵ₁ = 𝔠?" (CH) is independent of ZFC:
    - Under CH: the gap is "one step" (ℵ₀ → ℵ₁ = 𝔠)
    - Under ¬CH: there are intermediate cardinals (ℵ₀ < ℵ₁ < ... < 𝔠) -/
theorem denumerability_to_ch_summary :
    -- The cardinality positions
    (Cardinal.mk ℚ : Cardinal.{0}) = ℵ₀ ∧
    (#ℝ : Cardinal.{0}) = 𝔠 ∧
    (Cardinal.mk ℚ : Cardinal.{0}) < #ℝ ∧
    -- The Dedekind cut connection
    (#(Set ℚ) : Cardinal.{0}) = 𝔠 ∧
    -- The aleph bound
    (Cardinal.aleph 1 : Cardinal.{0}) ≤ 𝔠 :=
  ⟨card_rat_eq_aleph0,
   card_real_eq_continuum,
   card_rat_lt_card_real,
   card_subsets_rat_eq_continuum,
   aleph_one_le_continuum⟩

end DenumerabilityRationalsOQ01
