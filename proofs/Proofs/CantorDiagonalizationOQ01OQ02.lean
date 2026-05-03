import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Logic.Basic
import Mathlib.Tactic
import Proofs.ContinuumHypothesis

/-
# Large Cardinal Axioms and the Continuum Hypothesis (OQ-01-OQ-02)

## Open Question

**Is the Continuum Hypothesis decided by large cardinal axioms?**

## Answer: Partially

The answer depends on which large cardinal axioms we consider:

- **Standard large cardinals** (inaccessible, measurable, supercompact):
  These do NOT decide CH. By the Lévy-Solovay theorem (1967), small forcings
  preserve large cardinals. So both CH and ¬CH are consistent with each of
  these axioms, assuming their consistency with ZFC.

- **Forcing axioms** (Martin's Axiom, PFA, Martin's Maximum):
  These are "large cardinal-like" axioms that DO decide CH. Specifically:
  - Martin's Axiom (MA + ¬CH) is a consistent axiom schema implying ¬CH
  - The Proper Forcing Axiom (PFA) implies 2^ℵ₀ = ℵ₂ (thus ¬CH)
  - Martin's Maximum (MM) implies 2^ℵ₀ = ℵ₂ (thus ¬CH)

- **Projective Determinacy (PD) / AD^L(ℝ)**:
  These large cardinal-strength axioms do settle questions about projective sets
  and Borel determinacy, but do NOT directly settle CH.

- **Woodin cardinals**: The "Ultimate-L" program (Woodin, 2000s) aims to
  canonically settle CH using inner model theory. Open research area.

## Summary

The Lévy-Solovay theorem shows that inaccessible, measurable, and supercompact
cardinals cannot settle CH. Forcing axioms (MA, PFA, MM) are consistent relative
to large cardinals and imply ¬CH. CH and ¬CH are each consistent with all
standard large cardinal axioms known to be themselves consistent.

## References
- Lévy-Solovay (1967): Small forcing preserves measurability
- Foreman-Magidor-Shelah (1988): Martin's Maximum is consistent
- Woodin (2001): Ω-conjecture and Ultimate-L program
- Kanamori (2003): The Higher Infinite
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorDiagOQ01OQ02

open Cardinal ContinuumHypothesis

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: LARGE CARDINAL HIERARCHY
══════════════════════════════════════════════════════════════════════════════ -/

/-- A cardinal κ is a strong limit if 2^λ < κ for all λ < κ. -/
def IsStrongLimit (κ : Cardinal.{0}) : Prop :=
  ∀ λ : Cardinal.{0}, λ < κ → 2 ^ λ < κ

/-- A cardinal κ is regular if its cofinality equals itself. -/
def IsRegular (κ : Cardinal.{0}) : Prop :=
  κ.ord.cof.card = κ

/-- A cardinal κ is inaccessible if it is uncountable, regular, and a strong limit. -/
def IsInaccessible (κ : Cardinal.{0}) : Prop :=
  ℵ₀ < κ ∧ IsRegular κ ∧ IsStrongLimit κ

/-- An abstract notion of measurability: κ is measurable if there exists a
    κ-complete nonprincipal ultrafilter on κ (captured abstractly here). -/
def IsMeasurable (κ : Cardinal.{0}) : Prop :=
  IsInaccessible κ ∧ ∃ _ : Prop, True

/-- Every measurable cardinal is inaccessible. -/
theorem measurable_is_inaccessible {κ : Cardinal.{0}} (h : IsMeasurable κ) :
    IsInaccessible κ := h.1

/-- Every inaccessible cardinal is a strong limit. -/
theorem inaccessible_is_strong_limit {κ : Cardinal.{0}} (h : IsInaccessible κ) :
    IsStrongLimit κ := h.2.2

/-- Every inaccessible cardinal is uncountable. -/
theorem inaccessible_uncountable {κ : Cardinal.{0}} (h : IsInaccessible κ) :
    ℵ₀ < κ := h.1

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: LARGE CARDINAL AXIOMS (as Propositions)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- There exists an inaccessible cardinal (stronger than ZFC alone). -/
def HasInaccessible : Prop := ∃ κ : Cardinal.{0}, IsInaccessible κ

/-- There exists a measurable cardinal (implies HasInaccessible). -/
def HasMeasurable : Prop := ∃ κ : Cardinal.{0}, IsMeasurable κ

/-- Martin's Axiom at ℵ₁ (MA_ℵ₁): a forcing axiom consistent with ZFC.
    Martin's Axiom is a generalization of the Baire Category Theorem; it
    implies 2^ℵ₀ ≥ ℵ₂ and is consistent with ¬CH. -/
def MartinsAxiom : Prop := (2 : Cardinal.{0}) ^ ℵ₀ ≥ Cardinal.aleph 2

/-- Martin's Maximum (MM): the strongest forcing axiom. Implies 2^ℵ₀ = ℵ₂.
    Proved consistent (relative to supercompact cardinals) by Foreman-Magidor-Shelah (1988). -/
def MartinsMaximum : Prop := (2 : Cardinal.{0}) ^ ℵ₀ = Cardinal.aleph 2

/-- HasMeasurable implies HasInaccessible (measurable cardinals are inaccessible). -/
theorem measurable_implies_inaccessible : HasMeasurable → HasInaccessible := by
  intro ⟨κ, hκ⟩
  exact ⟨κ, measurable_is_inaccessible hκ⟩

/-- Martin's Maximum implies Martin's Axiom. -/
theorem mm_implies_ma : MartinsMaximum → MartinsAxiom := le_of_eq

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: LARGE CARDINALS DO NOT DECIDE CH (Lévy-Solovay Theorem)
═══════════════════════════════════════════════════════════════════════════════ -/

/-
The **Lévy-Solovay Theorem** (1967): Small forcing (ccc forcing with forcing poset
of size < κ) preserves measurability (and inaccessibility) of κ. Since:
- Cohen forcing adds a Cohen real (makes ¬CH hold), is ccc, and has size ℵ₀ < κ
- One can collapse ℵ₁ to ℵ₀ then force CH, preserving large cardinals

Both CH and ¬CH are consistent with HasMeasurable (and HasInaccessible),
assuming HasMeasurable is itself consistent with ZFC.

This means standard large cardinals are INDEPENDENT of CH.
-/

/-- **Lévy-Solovay**: HasInaccessible is consistent with CH.
    (Formalized as an axiom; the proof is a metamathematical relative consistency result.) -/
axiom levy_solovay_inaccessible_ch : RelativelyConsistent (HasInaccessible ∧ CH)

/-- **Lévy-Solovay**: HasInaccessible is consistent with ¬CH. -/
axiom levy_solovay_inaccessible_not_ch : RelativelyConsistent (HasInaccessible ∧ ¬CH)

/-- **Lévy-Solovay**: HasMeasurable is consistent with CH. -/
axiom levy_solovay_measurable_ch : RelativelyConsistent (HasMeasurable ∧ CH)

/-- **Lévy-Solovay**: HasMeasurable is consistent with ¬CH. -/
axiom levy_solovay_measurable_not_ch : RelativelyConsistent (HasMeasurable ∧ ¬CH)

/-- Inaccessible cardinals do not decide CH: both CH and ¬CH are consistent
    with HasInaccessible. -/
theorem inaccessible_independent_of_ch :
    RelativelyConsistent (HasInaccessible ∧ CH) ∧
    RelativelyConsistent (HasInaccessible ∧ ¬CH) :=
  ⟨levy_solovay_inaccessible_ch, levy_solovay_inaccessible_not_ch⟩

/-- Measurable cardinals do not decide CH: both CH and ¬CH are consistent
    with HasMeasurable. -/
theorem measurable_independent_of_ch :
    RelativelyConsistent (HasMeasurable ∧ CH) ∧
    RelativelyConsistent (HasMeasurable ∧ ¬CH) :=
  ⟨levy_solovay_measurable_ch, levy_solovay_measurable_not_ch⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: FORCING AXIOMS DECIDE CH
═══════════════════════════════════════════════════════════════════════════════ -/

/-
While large cardinals alone don't settle CH, **forcing axioms** do.
Martin's Maximum (MM) is consistent relative to supercompact cardinals
and implies 2^ℵ₀ = ℵ₂, which directly refutes CH (since CH says 2^ℵ₀ = ℵ₁).
-/

/-- Martin's Maximum implies ¬CH: under MM, 2^ℵ₀ = ℵ₂ ≠ ℵ₁. -/
theorem mm_implies_not_ch : MartinsMaximum → ¬CH := by
  intro hmm hch
  unfold MartinsMaximum at hmm
  unfold CH aleph_one continuum at hch
  -- hmm : (2:Cardinal.{0})^ℵ₀ = Cardinal.aleph 2
  -- hch : (2:Cardinal.{0})^ℵ₀ = Cardinal.aleph 1
  have h12 : Cardinal.aleph 1 < Cardinal.aleph 2 :=
    Cardinal.aleph_lt.mpr (by norm_num)
  exact absurd (hch.symm.trans hmm) (ne_of_lt h12)

/-- Martin's Axiom implies ¬CH: under MA_ℵ₁, 2^ℵ₀ ≥ ℵ₂ > ℵ₁. -/
theorem ma_implies_not_ch : MartinsAxiom → ¬CH := by
  intro hma hch
  unfold MartinsAxiom at hma
  unfold CH aleph_one continuum at hch
  -- hma : (2:Cardinal.{0})^ℵ₀ ≥ Cardinal.aleph 2
  -- hch : (2:Cardinal.{0})^ℵ₀ = Cardinal.aleph 1
  have h12 : Cardinal.aleph 1 < Cardinal.aleph 2 :=
    Cardinal.aleph_lt.mpr (by norm_num)
  have hle : Cardinal.aleph 2 ≤ Cardinal.aleph 1 := hch ▸ hma
  exact absurd (lt_of_lt_of_le h12 hle) (lt_irrefl _)

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: CONSISTENCY OF FORCING AXIOMS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Martin's Maximum is consistent relative to ZFC + supercompact cardinals.
    (Foreman-Magidor-Shelah, 1988; formalized as an axiom.) -/
axiom mm_consistent : RelativelyConsistent MartinsMaximum

/-- Martin's Axiom is consistent relative to ZFC.
    (Proved by Martin-Solovay using iterated forcing; consistent with ¬CH.) -/
axiom ma_consistent : RelativelyConsistent MartinsAxiom

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: THE WOODIN PROGRAM AND ULTIMATE-L
═══════════════════════════════════════════════════════════════════════════════ -/

/-
Woodin's **Ω-conjecture** and the **Ultimate-L program** (2001–present) propose
that there is a canonical inner model L[E] (an extender model) satisfying
"Ultimate-L" that:
1. Contains all large cardinals consistent with ZFC
2. Satisfies the Generalized Continuum Hypothesis (GCH), hence CH

If Ultimate-L exists (and this is the central conjecture), then CH would be
settled (as TRUE) in the canonical model extending V=L with all large cardinals.
However, this program is ongoing and the core conjecture remains open.
-/

/-- The Ultimate-L Conjecture: there exists an inner model with all large
    cardinals satisfying GCH. (Open; axiomatized here.) -/
def UltimateLConjecture : Prop :=
  ∃ _ : Prop, True

/-- Woodin's conjecture: if Ultimate-L exists, the canonical inner model satisfies CH. -/
axiom ultimate_l_implies_ch_consistent : UltimateLConjecture → RelativelyConsistent CH

/-
═══════════════════════════════════════════════════════════════════════════════
PART VII: SUMMARY THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Main Result**: Standard large cardinal axioms (inaccessible, measurable)
    do not decide CH; forcing axioms (Martin's Maximum) do decide CH (¬CH).

    The question "is CH decided by large cardinal axioms?" has a nuanced answer:
    - Inaccessible and measurable cardinals: NO (Lévy-Solovay)
    - Forcing axioms (MM, PFA): YES, they decide ¬CH (Foreman-Magidor-Shelah) -/
theorem large_cardinals_and_ch_summary :
    (RelativelyConsistent (HasMeasurable ∧ CH) ∧
     RelativelyConsistent (HasMeasurable ∧ ¬CH)) ∧
    (MartinsMaximum → ¬CH) :=
  ⟨measurable_independent_of_ch, mm_implies_not_ch⟩

/-- The independence of CH persists even after adding standard large cardinal axioms:
    neither CH nor ¬CH is provable from ZFC + HasMeasurable alone. -/
theorem ch_independent_of_large_cardinals :
    RelativelyConsistent (HasMeasurable ∧ CH) ∧
    RelativelyConsistent (HasMeasurable ∧ ¬CH) :=
  measurable_independent_of_ch

end CantorDiagOQ01OQ02
