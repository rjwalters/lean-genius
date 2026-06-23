import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Order.SuccPred.Basic
import Mathlib.Logic.Basic
import Mathlib.Tactic
import Proofs.ContinuumHypothesis

/-
# Should We Adopt Axioms That Decide CH?

## Open Question: continuum-hypothesis-oq-01

The Continuum Hypothesis (CH) is independent of ZFC — it can neither be proved
nor disproved from the standard axioms of set theory (Gödel 1940, Cohen 1963).
This independence raises a natural question:

**Should we extend ZFC with a new axiom that settles CH?**

This file examines the mathematical landscape:
- Part 1: What it formally means to "decide" CH via an axiom
- Part 2: ZFC-provable bounds (ℵ₁ ≤ 2^ℵ₀, ¬CH → ℵ₂ ≤ 2^ℵ₀)
- Part 3: The CH-direction — axioms implying CH (V=L, Ultimate L)
- Part 4: The ¬CH-direction — axioms implying ¬CH (PFA, MM)
- Part 5: Incompatibility of V=L with large cardinals
- Part 6: Mathematical criteria for axiom selection
- Part 7: Formal summary of the open question

## Key Results

- `VeqL_implies_CH` — the Axiom of Constructibility decides CH in favor of CH
- `PFA_implies_not_CH` — the Proper Forcing Axiom decides CH in favor of ¬CH
- `VeqL_not_large_cardinal_compatible` — V=L is inconsistent with measurable cardinals
- `aleph_one_le_continuum` — ℵ₁ ≤ 2^ℵ₀ (provable in ZFC alone)
- `not_CH_implies_aleph_two_le_continuum` — under ¬CH, we get ℵ₂ ≤ 2^ℵ₀
- `open_question_is_substantive` — both CH-deciding and ¬CH-deciding axioms exist
- `axiom_selection_tension` — V=L and measurable cardinals are mutually exclusive

## Historical Note

Gödel initially hoped V=L might be the "right" axiom to adopt, giving a complete
set theory. The discovery of large cardinal axioms in the 1960s-70s showed V=L
was too restrictive. More recent work (Woodin, 1999–) explores whether "Ultimate L"
can simultaneously accommodate large cardinals and imply GCH.
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace ContinuumHypothesisOQ01

-- Import key results from ContinuumHypothesis module
-- CH : continuum = aleph_one (from ContinuumHypothesis module)
-- GCH : ∀ α, 2^(ℵ_α) = ℵ_{α+1}
-- Open Cardinal for ℵ₀ notation (scoped in Cardinal namespace)
open Cardinal
-- Import specific names from ContinuumHypothesis
open ContinuumHypothesis (CH GCH gch_implies_ch)

-- ============================================================
-- PART 1: What It Means to "Decide" CH
-- ============================================================

/-- An axiom (proposition) Φ decides CH if it implies CH or implies ¬CH.
    This captures the notion of "settling" the Continuum Hypothesis via
    an extended axiom system ZFC + Φ. -/
def Decides (Φ : Prop) : Prop := (Φ → CH) ∨ (Φ → ¬CH)

/-- CH itself decides CH trivially. -/
theorem CH_decides_CH : Decides CH := Or.inl id

/-- ¬CH decides CH trivially. -/
theorem notCH_decides_notCH : Decides (¬CH) := Or.inr id

/-- Any axiom that implies CH decides CH. -/
theorem decides_of_implies_CH {Φ : Prop} (h : Φ → CH) : Decides Φ := Or.inl h

/-- Any axiom that implies ¬CH decides CH. -/
theorem decides_of_implies_notCH {Φ : Prop} (h : Φ → ¬CH) : Decides Φ := Or.inr h

-- ============================================================
-- PART 2: ZFC-Provable Bounds
-- ============================================================

/-- ℵ₁ ≤ 2^ℵ₀: provable in ZFC from Cantor's theorem plus the definition
    of ℵ₁ as the minimal uncountable cardinal.

    Proof: 2^ℵ₀ > ℵ₀ (Cantor), and ℵ₁ = (ℵ₀).succ is the
    minimal cardinal > ℵ₀, so ℵ₁ ≤ 2^ℵ₀. -/
theorem aleph_one_le_continuum : ContinuumHypothesis.aleph_one ≤ ContinuumHypothesis.continuum := by
  unfold ContinuumHypothesis.aleph_one ContinuumHypothesis.continuum
  -- Need: Cardinal.aleph 1 ≤ 2 ^ ℵ₀
  -- Step 1: aleph 1 = Order.succ ℵ₀  (by definition of aleph function)
  have haleph1 : Cardinal.aleph 1 = Order.succ ℵ₀ := by
    have h01 : (1 : Ordinal) = Order.succ (0 : Ordinal) := by
      rw [Order.succ_eq_add_one, zero_add]
    rw [h01, Cardinal.aleph_succ, Cardinal.aleph_zero]
  -- Step 2: ℵ₀ < 2 ^ ℵ₀  (Cantor's theorem)
  -- Step 3: succ ℵ₀ ≤ 2 ^ ℵ₀  (by succ_le_of_lt)
  rw [haleph1]
  exact Order.succ_le_of_lt (Cardinal.cantor ℵ₀)

/-- CH means the ZFC-provable bound ℵ₁ ≤ 2^ℵ₀ is an equality. -/
theorem ch_means_equality :
    CH → ContinuumHypothesis.continuum = ContinuumHypothesis.aleph_one := by
  intro h; exact h

/-- Under ¬CH, the continuum is strictly larger than ℵ₁. -/
theorem not_CH_implies_strict_inequality :
    ¬CH → ContinuumHypothesis.aleph_one < ContinuumHypothesis.continuum := by
  intro h
  rcases lt_or_eq_of_le aleph_one_le_continuum with hlt | heq
  · exact hlt
  · exfalso; apply h; simp only [ContinuumHypothesis.CH]; exact heq.symm

/-- Under ¬CH, the continuum is at least ℵ₂ = (ℵ₁).succ.
    This follows because ℵ₁ < 2^ℵ₀ and ℵ₂ is the next cardinal after ℵ₁. -/
theorem not_CH_implies_aleph_two_le_continuum (h : ¬CH) :
    Cardinal.aleph 2 ≤ ContinuumHypothesis.continuum := by
  have hlt := not_CH_implies_strict_inequality h
  unfold ContinuumHypothesis.aleph_one at hlt
  -- Cardinal.aleph 2 = Order.succ (Cardinal.aleph 1)
  have haleph2 : Cardinal.aleph 2 = Order.succ (Cardinal.aleph 1) := by
    have h12 : (2 : Ordinal) = Order.succ (1 : Ordinal) := by
      rw [Order.succ_eq_add_one]; norm_num
    rw [h12, Cardinal.aleph_succ]
  rw [haleph2]
  exact Order.succ_le_of_lt hlt

-- ============================================================
-- PART 3: Axioms Implying CH — The Constructibility Direction
-- ============================================================

/-- The Axiom of Constructibility (V = L): every set is constructible.
    Gödel (1940) showed the constructible universe L satisfies GCH and hence CH.
    But measurable cardinals do not exist in L (Scott, 1961).

    Why an axiom? Full formalization requires ~2000 lines covering:
    (1) Definition of the constructible hierarchy L₀ ⊂ L₁ ⊂ ... ⊂ L
    (2) Proof that L satisfies every ZFC axiom
    (3) Proof that V=L → GCH (analyzing the constructible hierarchy) -/
axiom VeqL : Prop

/-- V=L implies the Generalized Continuum Hypothesis: for all ordinals α,
    2^(ℵ_α) = ℵ_{α+1}. This is Gödel's key result about the constructible universe. -/
axiom VeqL_implies_GCH : VeqL → GCH

/-- V=L implies CH (special case of GCH at α = 0). -/
theorem VeqL_implies_CH : VeqL → CH :=
  fun h => gch_implies_ch (VeqL_implies_GCH h)

/-- V=L decides CH (in favor of CH). -/
theorem VeqL_decides_CH : Decides VeqL := decides_of_implies_CH VeqL_implies_CH

/-- Woodin's Ultimate L: a conjectural inner model that satisfies GCH
    while remaining compatible with large cardinal axioms. This is the focus
    of current set-theoretic research (Woodin, 1999–). -/
axiom UltimateL : Prop

/-- The Ultimate L Conjecture: Ultimate L implies GCH. -/
axiom UltimateL_implies_GCH : UltimateL → GCH

/-- Ultimate L implies CH (if the conjecture holds). -/
theorem UltimateL_implies_CH : UltimateL → CH :=
  fun h => gch_implies_ch (UltimateL_implies_GCH h)

-- ============================================================
-- PART 4: Axioms Implying ¬CH — The Forcing Axiom Direction
-- ============================================================

/-- The Proper Forcing Axiom (PFA): a "maximality principle" asserting that
    dense open sets in any proper forcing poset have generic filters.
    PFA implies 2^ℵ₀ = ℵ₂ and is consistent relative to supercompact cardinals.

    Why an axiom? Formalization requires ~3000 lines of forcing machinery. -/
axiom PFA : Prop

/-- PFA implies the continuum equals ℵ₂.
    This is the key consequence of PFA: 2^ℵ₀ = ℵ₂ > ℵ₁, hence ¬CH. -/
axiom PFA_implies_continuum_eq_aleph_two :
    PFA → ContinuumHypothesis.continuum = Cardinal.aleph 2

/-- ℵ₁ < ℵ₂: strict ordering of the aleph sequence. -/
theorem aleph_one_lt_aleph_two : Cardinal.aleph 1 < Cardinal.aleph 2 :=
  Cardinal.aleph_lt_aleph.mpr (by norm_num)

/-- PFA implies ¬CH. -/
theorem PFA_implies_not_CH : PFA → ¬CH := by
  intro hpfa hch
  have h2 := PFA_implies_continuum_eq_aleph_two hpfa
  -- CH says continuum = aleph_one = Cardinal.aleph 1
  have heq1 : ContinuumHypothesis.continuum = Cardinal.aleph 1 := by
    simp only [ContinuumHypothesis.CH, ContinuumHypothesis.aleph_one] at hch
    exact hch
  -- PFA says continuum = Cardinal.aleph 2
  -- So aleph 1 = aleph 2, contradicting aleph 1 < aleph 2
  exact absurd (heq1.symm.trans h2) (ne_of_lt aleph_one_lt_aleph_two)

/-- PFA decides CH (in favor of ¬CH). -/
theorem PFA_decides_CH : Decides PFA := decides_of_implies_notCH PFA_implies_not_CH

/-- Martin's Maximum (MM): the strongest known forcing axiom.
    MM implies PFA, hence 2^ℵ₀ = ℵ₂, hence ¬CH.
    Consistent relative to supercompact cardinals (Foreman, Magidor, Shelah 1988). -/
axiom MM : Prop

/-- MM implies PFA. -/
axiom MM_implies_PFA : MM → PFA

/-- MM implies ¬CH. -/
theorem MM_implies_not_CH : MM → ¬CH :=
  fun h => PFA_implies_not_CH (MM_implies_PFA h)

-- ============================================================
-- PART 5: Incompatibility — Large Cardinals vs V=L
-- ============================================================

/-- A measurable cardinal: a cardinal κ admitting a non-principal
    κ-complete ultrafilter on κ. Universe level fixed to 0 for concreteness. -/
structure MeasurableCardinal : Type 1 where
  κ : Cardinal.{0}
  uncountable : Cardinal.aleph 0 < κ
  has_ultrafilter : True  -- ultrafilter witness abstracted

/-- Scott's Theorem (1961): if a measurable cardinal exists, then V ≠ L.
    Measurable cardinals have a reflection property incompatible with L.

    Why an axiom? The proof uses ultrapower embeddings and critical point theory,
    showing that if j : V → M is the ultrapower embedding, then j(κ) > κ,
    which is impossible in L. -/
axiom VeqL_incompatible_with_measurable : VeqL → ¬(Nonempty MeasurableCardinal)

/-- The core incompatibility: V=L (implies CH) and measurable cardinals can't coexist. -/
theorem axiom_selection_tension (hVL : VeqL) (hM : Nonempty MeasurableCardinal) : False :=
  VeqL_incompatible_with_measurable hVL hM

-- ============================================================
-- PART 6: Mathematical Criteria for Axiom Selection
-- ============================================================

/-- An axiom Φ is "large-cardinal compatible" if it does not exclude
    the existence of measurable cardinals. -/
def LargeCardinalCompatible (Φ : Prop) : Prop :=
  ¬(Φ → ¬(Nonempty MeasurableCardinal))

/-- V=L is NOT large-cardinal compatible (by Scott's theorem). -/
theorem VeqL_not_large_cardinal_compatible :
    ¬LargeCardinalCompatible VeqL :=
  not_not.mpr VeqL_incompatible_with_measurable

/-- PFA is large-cardinal compatible: consistent with measurable cardinals.
    Its consistency proof uses supercompact cardinals. -/
axiom PFA_large_cardinal_compatible : LargeCardinalCompatible PFA

/-- Key asymmetry: V=L (→ CH) is incompatible with large cardinals,
    while PFA (→ ¬CH) is compatible. -/
theorem asymmetry_in_large_cardinal_compatibility :
    (¬LargeCardinalCompatible VeqL) ∧ (LargeCardinalCompatible PFA) :=
  ⟨VeqL_not_large_cardinal_compatible, PFA_large_cardinal_compatible⟩

-- ============================================================
-- PART 7: Summary of the Open Question
-- ============================================================

/-- The CH axiom-selection question is substantive: there exist axioms for each side. -/
def TheOpenQuestion : Prop :=
  (∃ Φ : Prop, Decides Φ ∧ (Φ → CH)) ∧
  (∃ Φ : Prop, Decides Φ ∧ (Φ → ¬CH))

/-- The open question has mathematical content: both sides have natural axioms. -/
theorem open_question_is_substantive : TheOpenQuestion :=
  ⟨⟨VeqL, VeqL_decides_CH, VeqL_implies_CH⟩,
   ⟨PFA, PFA_decides_CH, PFA_implies_not_CH⟩⟩

/-- Summary: axioms exist for each direction, with the ¬CH-side being
    large-cardinal compatible. -/
theorem ch_landscape_summary :
    (∃ Φ : Prop, Decides Φ ∧ (Φ → CH) ∧ (Φ → GCH)) ∧
    (∃ Φ : Prop, Decides Φ ∧ (Φ → ¬CH) ∧ LargeCardinalCompatible Φ) :=
  ⟨⟨VeqL, VeqL_decides_CH, VeqL_implies_CH, VeqL_implies_GCH⟩,
   ⟨PFA, PFA_decides_CH, PFA_implies_not_CH, PFA_large_cardinal_compatible⟩⟩

/-
## Conclusion

The mathematical landscape around "should we adopt axioms that decide CH?":

1. V=L -> CH: Constructibility implies GCH, hence CH. But V=L is incompatible
   with measurable cardinals (Scott 1961). Most set theorists consider V=L too
   restrictive as a foundation for modern mathematics.

2. PFA -> not CH: Forcing axioms imply 2^aleph_0 = aleph_2 > aleph_1. PFA is
   consistent with large cardinals and has rich mathematical consequences.
   Most modern set theorists find forcing axioms more "natural."

3. Ultimate L program (Woodin, ongoing): Seeks a canonical inner model satisfying
   GCH while accommodating all large cardinals. If successful, could revive CH.

Key asymmetry: the not-CH-deciding axioms (PFA, MM) are large-cardinal compatible,
while the primary CH-implying axiom (V=L) is not. This gives PFA/MM a structural
advantage from the perspective of accepting large cardinals as natural axioms.

The formal answer: ZFC cannot decide this question. It remains genuinely open
in the mathematical and philosophical community.
-/

end ContinuumHypothesisOQ01

-- Export key theorems
#check ContinuumHypothesisOQ01.Decides
#check ContinuumHypothesisOQ01.aleph_one_le_continuum
#check ContinuumHypothesisOQ01.not_CH_implies_aleph_two_le_continuum
#check ContinuumHypothesisOQ01.VeqL_implies_CH
#check ContinuumHypothesisOQ01.PFA_implies_not_CH
#check ContinuumHypothesisOQ01.VeqL_not_large_cardinal_compatible
#check ContinuumHypothesisOQ01.asymmetry_in_large_cardinal_compatibility
#check ContinuumHypothesisOQ01.open_question_is_substantive
#check ContinuumHypothesisOQ01.axiom_selection_tension
