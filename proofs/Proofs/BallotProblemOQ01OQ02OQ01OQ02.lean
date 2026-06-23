/-
# Ballot Problem OQ-01-OQ-02-OQ-01-OQ-02: General Uniform Fiber Transfer

Open Question from ballot-problem-oq-01-oq-02-oq-01:
"Can the uniformOn_fiber_transfer pattern be generalized: if a measurable map
between finite probability spaces has uniform fibers, does it preserve all
event probabilities (not just uniformOn)?"

## The Answer

YES — uniform fibers preserve uniformOn probability for ALL events simultaneously.
If f : α → β sends S ⊆ α surjectively onto T ⊆ β (finite sets), and every
fiber f⁻¹(t) ∩ S has the same ncard k, then for ANY event P ⊆ T:

  uniformOn S (f⁻¹' P) = uniformOn T P

## Why This Is Stronger Than OQ-01

OQ-01 proved this for ONE specific event P = staysPositive and ONE specific
function (ballot projection). This file proves it for an ABSTRACT function f
and ALL events P simultaneously, via a single general theorem.

## Proof Strategy

1. S-decomposition (via surjectivity): S = ⋃_{t ∈ T} (S ∩ f⁻¹'{t})
2. P-fiber decomposition: S ∩ f⁻¹'P = ⋃_{t ∈ P} (S ∩ f⁻¹'{t})
3. Uniform counting (ncard_biUnion_eq_of_uniform):
   ncard(S) = k · ncard(T), ncard(S ∩ f⁻¹'P) = k · ncard(P)
4. ENNReal ratio: the factor k cancels in numerator/denominator

## Status: Verified (0 axioms, 0 sorries)
-/

import Proofs.BallotProblemOQ01OQ02OQ01
import Mathlib.Tactic

open ProbabilityTheory Set

namespace BallotGeneralFiberTransfer

/-
══════════════════════════════════════════════════════════════
PART I: FIBER GEOMETRY LEMMAS
══════════════════════════════════════════════════════════════ -/

/-- Decompose a preimage intersection into a union of singleton fiber intersections:
    `A ∩ f⁻¹'P = ⋃ t ∈ P, (A ∩ f⁻¹'{t})`. -/
theorem preimage_inter_eq_iUnion {α β : Type*} (f : α → β) (A : Set α) (P : Set β) :
    A ∩ f ⁻¹' P = ⋃ t ∈ P, A ∩ f ⁻¹' {t} := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_iUnion, mem_singleton_iff]
  constructor
  · rintro ⟨hxA, hxP⟩
    exact ⟨f x, hxP, hxA, rfl⟩
  · rintro ⟨t, ht, hxA, rfl⟩
    exact ⟨hxA, ht⟩

/-- When f is surjective from A onto T, A decomposes as ⋃_{t ∈ T} (A ∩ f⁻¹'{t}). -/
theorem surjOn_fiber_decomp {α β : Type*} (f : α → β) (A : Set α) (T : Set β)
    (hf : SurjOn f A T) :
    A = ⋃ t ∈ T, A ∩ f ⁻¹' {t} := by
  ext x
  simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
  constructor
  · intro hxA
    exact ⟨f x, hf (mem_image_of_mem f hxA), hxA, rfl⟩
  · rintro ⟨_, _, hxA, _⟩
    exact hxA

/-- Fibers over distinct points are disjoint. -/
theorem singleton_fiber_disjoint {α β : Type*} (f : α → β) (A : Set α)
    (t₁ t₂ : β) (hne : t₁ ≠ t₂) :
    Disjoint (A ∩ f ⁻¹' {t₁}) (A ∩ f ⁻¹' {t₂}) := by
  simp only [disjoint_left, mem_inter_iff, mem_preimage, mem_singleton_iff]
  intro x ⟨_, hxt1⟩ ⟨_, hxt2⟩
  exact hne (hxt1 ▸ hxt2)

/-
══════════════════════════════════════════════════════════════
PART II: UNIFORM FIBER COUNTING
══════════════════════════════════════════════════════════════ -/

/-- Uniform fiber counting: when fibers have uniform ncard k over T,
    any sub-collection over P ⊆ T counts k * ncard(P) elements. -/
theorem uniform_fiber_count {α β : Type*} (f : α → β)
    (A : Set α) (hA : A.Finite) (T : Set β) (hT : T.Finite)
    (k : ℕ) (hk : ∀ t ∈ T, (A ∩ f ⁻¹' {t}).ncard = k)
    (P : Set β) (hPT : P ⊆ T) :
    (A ∩ f ⁻¹' P).ncard = k * P.ncard := by
  rw [preimage_inter_eq_iUnion f A P]
  apply BallotFiberTransfer.ncard_biUnion_eq_of_uniform
  · exact hT.subset hPT
  · intro t ht
    exact hA.subset inter_subset_left
  · intro t₁ ht₁ t₂ ht₂ hne
    exact singleton_fiber_disjoint f A t₁ t₂ hne
  · intro t ht
    exact hk t (hPT ht)

/-
══════════════════════════════════════════════════════════════
PART III: MAIN THEOREM
══════════════════════════════════════════════════════════════ -/

/-- **General Uniform Fiber Transfer Theorem** (answer to OQ-01-OQ-02-OQ-01-OQ-02).

    If f : α → β is surjective from A onto T (finite sets) with uniform fiber
    sizes k (i.e., `(A ∩ f⁻¹'{t}).ncard = k` for all t ∈ T), then for ANY
    event P ⊆ T, the uniformOn probability is preserved under pullback:

      `uniformOn A (f⁻¹' P) = uniformOn T P`

    This is strictly stronger than the ballot OQ-01 result: that proved this
    for ONE specific function and ONE specific event; this holds for ALL abstract
    functions with uniform fibers and ALL events simultaneously. -/
theorem uniformOn_fiber_transfer_all {α β : Type*} (f : α → β)
    (A : Set α) (T : Set β)
    (hA : A.Finite) (hT : T.Finite)
    (hA_ne : A.Nonempty) (hT_ne : T.Nonempty)
    (hf : SurjOn f A T)
    (k : ℕ) (hk_pos : 0 < k)
    (hk : ∀ t ∈ T, (A ∩ f ⁻¹' {t}).ncard = k)
    (P : Set β) (hPT : P ⊆ T) :
    uniformOn A (f ⁻¹' P) = uniformOn T P := by
  -- Step 1: Compute ncard(A) = k * ncard(T) via surjectivity decomposition
  have hA_ncard : A.ncard = k * T.ncard := by
    rw [surjOn_fiber_decomp f A T hf]
    exact BallotFiberTransfer.ncard_biUnion_eq_of_uniform
      (fun t => A ∩ f ⁻¹' {t}) T hT
      (fun t _ => hA.subset inter_subset_left)
      (fun t₁ _ t₂ _ hne => singleton_fiber_disjoint f A t₁ t₂ hne)
      k hk
  -- Step 2: Compute ncard(A ∩ f⁻¹' P) = k * ncard(P)
  have hAP_ncard : (A ∩ f ⁻¹' P).ncard = k * P.ncard :=
    uniform_fiber_count f A hA T hT k hk P hPT
  -- Step 3: ncard(T ∩ P) = ncard(P) since P ⊆ T
  have hTP : T ∩ P = P := inter_eq_right.mpr hPT
  -- Step 4: Positive ncard needed for ENNReal division
  have hT_pos : 0 < T.ncard := by
    apply Set.ncard_pos hT; exact hT_ne
  have hA_pos : 0 < A.ncard := by
    rw [hA_ncard]; exact Nat.mul_pos hk_pos hT_pos
  -- Step 5: Assemble via ENNReal ratio
  simp only [ProbabilityTheory.uniformOn]
  rw [ENNReal.div_eq_div_iff
    (by exact_mod_cast hA_pos.ne' : (↑A.ncard : ENNReal) ≠ 0)
    (ENNReal.natCast_ne_top _)
    (by exact_mod_cast hT_pos.ne' : (↑T.ncard : ENNReal) ≠ 0)
    (ENNReal.natCast_ne_top _)]
  -- Goal: ncard(A ∩ f⁻¹'P) * ncard(T) = ncard(T ∩ P) * ncard(A)
  rw [hTP]
  exact_mod_cast (show (A ∩ f ⁻¹' P).ncard * T.ncard = P.ncard * A.ncard by
    rw [hAP_ncard, hA_ncard]; ring)

/-
══════════════════════════════════════════════════════════════
PART IV: COROLLARIES
══════════════════════════════════════════════════════════════ -/

/-- Specialization: the uniform fiber transfer holds for ALL events P,
    not just the specific ballot event from OQ-01. -/
theorem uniformOn_preserves_all_events {α β : Type*} (f : α → β)
    (A : Set α) (T : Set β)
    (hA : A.Finite) (hT : T.Finite)
    (hA_ne : A.Nonempty) (hT_ne : T.Nonempty)
    (hf : SurjOn f A T)
    (k : ℕ) (hk_pos : 0 < k)
    (hk : ∀ t ∈ T, (A ∩ f ⁻¹' {t}).ncard = k) :
    ∀ P : Set β, P ⊆ T →
      uniformOn A (f ⁻¹' P) = uniformOn T P :=
  fun P hPT => uniformOn_fiber_transfer_all f A T hA hT hA_ne hT_ne hf k hk_pos hk P hPT

/-- Complement transfer: the probability of the complement event is also preserved. -/
theorem uniformOn_complement_transfer {α β : Type*} (f : α → β)
    (A : Set α) (T : Set β)
    (hA : A.Finite) (hT : T.Finite)
    (hA_ne : A.Nonempty) (hT_ne : T.Nonempty)
    (hf : SurjOn f A T)
    (k : ℕ) (hk_pos : 0 < k)
    (hk : ∀ t ∈ T, (A ∩ f ⁻¹' {t}).ncard = k)
    (P : Set β) (hPT : P ⊆ T) :
    uniformOn A (f ⁻¹' (T \ P)) = uniformOn T (T \ P) :=
  uniformOn_fiber_transfer_all f A T hA hT hA_ne hT_ne hf k hk_pos hk (T \ P) diff_subset

/-- Union transfer: the fiber transfer respects finite unions of events. -/
theorem uniformOn_union_transfer {α β : Type*} (f : α → β)
    (A : Set α) (T : Set β)
    (hA : A.Finite) (hT : T.Finite)
    (hA_ne : A.Nonempty) (hT_ne : T.Nonempty)
    (hf : SurjOn f A T)
    (k : ℕ) (hk_pos : 0 < k)
    (hk : ∀ t ∈ T, (A ∩ f ⁻¹' {t}).ncard = k)
    (P Q : Set β) (hPT : P ⊆ T) (hQT : Q ⊆ T) :
    uniformOn A (f ⁻¹' (P ∪ Q)) = uniformOn T (P ∪ Q) :=
  uniformOn_fiber_transfer_all f A T hA hT hA_ne hT_ne hf k hk_pos hk (P ∪ Q)
    (union_subset hPT hQT)

end BallotGeneralFiberTransfer
