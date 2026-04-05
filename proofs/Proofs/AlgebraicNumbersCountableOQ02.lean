import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.AlgebraicCard
import Mathlib.Data.Set.Countable
import Mathlib.Tactic
import Proofs.CantorDiagonalization
import Proofs.AlgebraicNumbersCountable

/-
# ℝ is Uncountable: Cantor's Diagonal Argument (1874)

## Open Question (algebraic-numbers-countable-oq-02)

Prove in Lean 4 that ℝ is uncountable (Cantor's diagonal argument, completing the 1874 paper).

## What This Proves

1. `reals_not_countable` — ℝ is not countable: ¬ Countable ℝ
2. `no_surjection_nat_to_real` — no surjection ℕ → ℝ: ¬∃ f : ℕ → ℝ, Surjective f
3. `exists_not_in_range` — for any f : ℕ → ℝ, ∃ x, x ∉ range f
4. `transcendentals_uncountable` — transcendental reals are uncountable
5. `reals_uncountable_summary` — Cantor's 1874 theorem: algebraic = countable, ℝ = uncountable

## Proof Strategy

**Cantor's diagonal argument** proves ℵ₀ < 2^ℵ₀ (no surjection from a set to its power set).
Since #ℝ = 𝔠 = 2^ℵ₀ (Cardinal.mk_real) and 𝔠 > ℵ₀ (Cardinal.aleph0_lt_continuum),
no injection ℝ → ℕ exists, i.e., ℝ is uncountable.

**Connection to CantorDiagonalization**: The abstract gap ℵ₀ < 2^ℵ₀ (Cardinal.cantor ℵ₀)
is the same theorem as no surjection ℕ → BinarySeq exists (CantorDiagonalization.lean).
Both express Cantor's diagonal construction. The cardinality of BinarySeq = (ℕ → Bool) is
also 2^ℵ₀ = 𝔠 = #ℝ.

**Corollary**: Since the algebraic reals are countable (AlgebraicNumbersCountable.lean)
and ℝ is uncountable, the transcendental reals must be uncountable. "Almost all"
real numbers are transcendental.

## Historical Note

Cantor's 1874 paper "Über eine Eigenschaft des Inbegriffes aller reellen algebraischen Zahlen"
proved two results:
- The algebraic numbers are countable
- The real numbers are uncountable

This established that there are "more" transcendental numbers than algebraic ones in a precise
cardinality sense, even though transcendental numbers were historically much harder to identify
explicitly (Liouville 1844 gave the first construction; Cantor's 1874 argument showed most
reals must be transcendental, without explicitly naming any).

## Prerequisites

- AlgebraicNumbersCountable.lean: algebraic reals are countable
- CantorDiagonalization.lean: no surjection ℕ → BinarySeq
- Cardinal.mk_real: #ℝ = 𝔠 = 2^ℵ₀
- Cardinal.aleph0_lt_continuum: ℵ₀ < 𝔠
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace AlgebraicNumbersCountableOQ02

open Cardinal

-- ============================================================
-- § 1: The Cardinality of ℝ Exceeds ℵ₀
-- ============================================================

/-- The cardinality of ℝ equals the continuum 𝔠 = 2^ℵ₀. -/
theorem card_real_eq_continuum : (#ℝ : Cardinal.{0}) = 𝔠 :=
  Cardinal.mk_real

/-- ℵ₀ < #ℝ: the real numbers are strictly more numerous than the natural numbers. -/
theorem aleph0_lt_card_real : (ℵ₀ : Cardinal.{0}) < #ℝ := by
  rw [card_real_eq_continuum]
  exact Cardinal.aleph0_lt_continuum

-- ============================================================
-- § 2: ℝ is Not Countable
-- ============================================================

/-- **Main Theorem**: ℝ is not countable.

    This is Cantor's 1874 result, the foundation of set theory.

    Proof: If ℝ were countable, then #ℝ ≤ ℵ₀ (by Cardinal.mk_le_aleph0).
    But #ℝ = 𝔠 > ℵ₀ (by Cardinal.mk_real and aleph0_lt_continuum). Contradiction.

    This is the abstract form of the diagonal argument:
    Cantor's theorem gives ℵ₀ < 2^ℵ₀, and 2^ℵ₀ = 𝔠 = #ℝ. -/
theorem reals_not_countable : ¬ Countable ℝ := by
  intro h
  haveI := h
  have hle : (#ℝ : Cardinal.{0}) ≤ ℵ₀ := Cardinal.mk_le_aleph0
  exact absurd hle (not_le.mpr aleph0_lt_card_real)

/-- ℝ is uncountable (equivalent formulation). -/
theorem reals_uncountable : ¬ Countable ℝ := reals_not_countable

-- ============================================================
-- § 3: No Surjection ℕ → ℝ
-- ============================================================

/-- **No surjection ℕ → ℝ exists.**

    This is the direct statement of Cantor's diagonal argument:
    no enumeration of real numbers can be complete.

    Proof: A surjection f : ℕ → ℝ would make ℝ countable (since ℕ is countable
    and the image of a countable set under a surjection is countable). But ℝ is
    not countable. -/
theorem no_surjection_nat_to_real :
    ¬ ∃ f : ℕ → ℝ, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact reals_not_countable (hf.countable)

/-- For any f : ℕ → ℝ, there exists a real not in the range of f. -/
theorem exists_not_in_range (f : ℕ → ℝ) :
    ∃ x : ℝ, x ∉ Set.range f := by
  by_contra h
  push_neg at h
  have : Function.Surjective f := fun x => h x
  exact no_surjection_nat_to_real ⟨f, this⟩

-- ============================================================
-- § 4: Transcendental Reals are Uncountable
-- ============================================================

/-- The set of transcendental real numbers: reals that are not algebraic over ℚ. -/
def transcendentalReals : Set ℝ := {x | ¬ IsAlgebraic ℚ x}

/-- **Cantor's 1874 Corollary**: The transcendental reals are uncountable.

    Since:
    - ℝ = algebraic ∪ transcendental (every real is one or the other)
    - Algebraic reals are countable (AlgebraicNumbersCountable.lean)
    - ℝ is uncountable (reals_not_countable)
    It follows that the transcendental reals must be uncountable. -/
theorem transcendentals_uncountable : ¬ Set.Countable transcendentalReals := by
  intro h_trans
  have h_alg : Set.Countable {x : ℝ | IsAlgebraic ℚ x} :=
    AlgebraicNumbersCountable.algebraic_reals_countable
  -- The algebraic and transcendental reals together cover all of ℝ
  have h_cover : {x : ℝ | IsAlgebraic ℚ x} ∪ transcendentalReals = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_setOf_eq, transcendentalReals, Set.mem_univ,
               Set.mem_setOf_eq, iff_true]
    exact Classical.em _
  -- Therefore Set.univ is countable
  have h_univ : Set.Countable (Set.univ : Set ℝ) := by
    rw [← h_cover]
    exact h_alg.union h_trans
  -- This contradicts the uncountability of ℝ
  exact reals_not_countable (Set.countable_univ_iff.mp h_univ)

-- ============================================================
-- § 5: Connection to Cantor's Diagonal Argument
-- ============================================================

/-- The Cantor diagonal argument for binary sequences (from CantorDiagonalization.lean).

    BinarySeq = (ℕ → Bool) has the same cardinality as ℝ: both equal 2^ℵ₀ = 𝔠.
    The diagonal argument shows no enumeration of binary sequences is complete. -/
theorem cantor_diagonal_binary :
    ¬ ∃ f : ℕ → CantorDiagonalization.BinarySeq, Function.Surjective f :=
  CantorDiagonalization.no_surjection_nat_to_binary

/-- **Cantor's diagonal gap**: ℵ₀ < 2^ℵ₀.

    This is the abstract form of the diagonal argument: the power set of any cardinal
    is strictly larger. Applied to κ = ℵ₀, this gives the gap between ℕ and BinarySeq. -/
theorem cantor_diagonal_gap : (ℵ₀ : Cardinal.{0}) < 2 ^ ℵ₀ :=
  Cardinal.cantor ℵ₀

/-- The continuum 𝔠 equals #ℝ, linking the diagonal gap ℵ₀ < 2^ℵ₀ = 𝔠 to ℝ uncountability. -/
theorem diagonal_gap_equals_card_real : (𝔠 : Cardinal.{0}) = #ℝ :=
  card_real_eq_continuum.symm

/-- **Cantor's 1874 Summary**: The key dichotomy completing the 1874 paper:
    - Algebraic reals are countable (|algebraic| = ℵ₀)
    - Transcendental reals are uncountable
    - ℝ itself is uncountable (|ℝ| = 𝔠 = 2^ℵ₀ > ℵ₀) -/
theorem reals_uncountable_summary :
    ¬ Countable ℝ ∧
    ¬ Set.Countable transcendentalReals ∧
    Set.Countable {x : ℝ | IsAlgebraic ℚ x} :=
  ⟨reals_not_countable, transcendentals_uncountable,
   AlgebraicNumbersCountable.algebraic_reals_countable⟩

end AlgebraicNumbersCountableOQ02
