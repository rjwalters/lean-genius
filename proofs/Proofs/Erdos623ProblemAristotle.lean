/-
  Aristotle targets for Erdos623Problem (Erdős #623: Independent Sets for Free Functions at ℵ_ω)
  Routine supporting lemmas for automated proof search.
  See Erdos623Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open problem (erdos_623_conjecture — open in ZFC)
  - NOT the axiom erdos_hajnal_below_aleph_omega (axiom, Aristotle skips)
  - Routine results: classical logic manipulation, standard cardinal facts, corollaries of axioms

  Targets:
  1. aleph_omega_is_singular: ¬aleph_omega.IsRegular
     ℵ_ω is not a regular cardinal (cofinality is ω < ℵ_ω itself).
     Proof sketch:
     - Assume h : aleph_omega.IsRegular
     - h.cof_eq gives cof(aleph_omega.ord) = aleph_omega.ord
     - cofinality_aleph_omega (proved in file): cof(aleph_omega.ord) = ω
     - Together: aleph_omega.ord = ω, contradicting aleph_omega being uncountable
     - Try: Cardinal.not_isRegular_aleph_omega from Mathlib if available

  2. erdos_623_dichotomy: erdos_623_conjecture ∨ erdos_623_negative
     Classical logic: negating the conjecture gives the negative via push_neg.
     Proof sketch:
     - The proof already handles the positive case (left; exact h)
     - For ¬erdos_623_conjecture: push_neg transforms it to exactly erdos_623_negative
       push_neg at h gives:
       h : ∃ X, #X = aleph_omega ∧ ∃ f : Finset X → X, IsFreeFunction f ∧
               ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y
     - Obtain X, hX, f, hf, hneg from h; exact ⟨X, hX, f, hf, hneg⟩

  3. weak_follows_from_strong: erdos_623_conjecture → erdos_623_weak
     Strong (∀ f) implies weak (∃ f) by picking any free function via exists_free_function.
     Proof sketch:
     - Fix X with hX : #X = aleph_omega
     - X is Infinite: aleph_omega is an infinite cardinal (≥ ℵ₀), so #X ≥ ℵ₀ → Infinite X
       Use: Cardinal.infinite_iff.mpr and that aleph_omega ≥ ℵ₀
     - Apply exists_free_function X [Infinite X] [Nonempty X] to get ⟨f, hf⟩
     - Apply h X hX f hf to get ⟨Y, hYinf, hYind⟩
     - Exact ⟨f, Y, hf, hYinf, hYind⟩

  Excluded:
  - singleton_independent sorry: B = ∅ case requires f ∅ ≠ x which isn't given
  - counterexample_at_aleph_n: requires constructing a type of exact cardinality ℵ_n (universe issues)
  - erdos_623_conjecture itself: open problem
-/
import Mathlib
import Proofs.Erdos623Problem

namespace Erdos623.Aristotle

open Erdos623 Cardinal

-- ============================================================
-- Aristotle Target 1: ℵ_ω is singular
-- ============================================================

/-- **ℵ_ω is not regular** (Aristotle target):
    ℵ_ω is singular: cofinality ω < ℵ_ω, so it fails regularity.

    Proof sketch:
    1. Assume h : aleph_omega.IsRegular
    2. h.cof_eq : aleph_omega.ord.cof = aleph_omega.ord  (regularity condition)
    3. cofinality_aleph_omega : aleph_omega.ord.cof = ω   (proved in main file)
    4. From 2,3: aleph_omega.ord = ω (Ordinal equality)
    5. But ℵ_ω = sup{ℵ_n : n < ω} > ℵ₀, so aleph_omega.ord > ω — contradiction
    Note: Try `exact Cardinal.not_isRegular_aleph_omega` if Mathlib has it. -/
theorem aleph_omega_is_singular : ¬(Erdos623.aleph_omega).IsRegular := by
  sorry

-- ============================================================
-- Aristotle Target 2: Classical dichotomy
-- ============================================================

/-- **Dichotomy: conjecture or counterexample** (Aristotle target):
    Either the Erdős conjecture holds for all free functions on ℵ_ω-sets,
    or there is an explicit counterexample.

    Proof sketch:
    - The proof by_cases splits on erdos_623_conjecture
    - Positive case: left; exact h (already done)
    - Negative case h : ¬erdos_623_conjecture:
      push_neg at h transforms to:
      h : ∃ X, #X = aleph_omega ∧ ∃ f : Finset X → X,
            IsFreeFunction f ∧ ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y
      This is exactly erdos_623_negative.
      obtain ⟨X, hX, f, hf, hneg⟩ := h; exact ⟨X, hX, f, hf, hneg⟩ -/
theorem erdos_623_dichotomy :
    Erdos623.erdos_623_conjecture ∨ Erdos623.erdos_623_negative := by
  by_cases h : Erdos623.erdos_623_conjecture
  · left; exact h
  · right
    sorry

-- ============================================================
-- Aristotle Target 3: Weak version follows from strong
-- ============================================================

/-- **Weak follows from strong** (Aristotle target):
    If the conjecture holds for ALL free functions (strong form),
    then there EXISTS a free function with an infinite independent set (weak form).

    Proof sketch:
    1. Intro X hX : fix a set X with #X = aleph_omega
    2. X is Infinite since aleph_omega ≥ ℵ₀:
       - aleph_omega = ℵ_ω = sup{ℵ_n : n < ω} ≥ ℵ₀
       - #X = aleph_omega ≥ ℵ₀ → Infinite X (by Cardinal.infinite_iff)
    3. X is Nonempty from Infinite X (Infinite.nonempty)
    4. exists_free_function X gives ⟨f, hf⟩ where IsFreeFunction f
    5. h X hX f hf gives ⟨Y, hYinf, hYind⟩
    6. Exact ⟨f, Y, hf, hYinf, hYind⟩ -/
theorem weak_follows_from_strong (h : Erdos623.erdos_623_conjecture) :
    Erdos623.erdos_623_weak := by
  sorry

end Erdos623.Aristotle
