import Proofs.Erdos85OrderFortyNineSevenHighT0EmptyCountingCore
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSemanticExclusion

/-!
# Counting exclusion of canonical H7/T0 empty cubes

Transport of `sevenHighT0_countingCertificate_contradiction` to canonical
completion graphs: the empty fiber of the transported `Fin 49` graph is
labelled by `finGraphEmptyFiberEquiv`, and its adjacency is the canonical
empty-sector mask.  Consequences: semantic exclusion of all 15 counting
classes (in particular `F6_t2`), and a capstone needing checked UNSAT only
for the 28 structural cubes.
-/

namespace Erdos85

open SimpleGraph

/-- Core counting theorem: a canonical completion graph cannot have an
empty-sector mask for which some vertex subset violates the actual
capacity inequality. -/
theorem sevenHighT0Canonical_emptyMask_ne_of_countingCertificate
    (mask : Nat) (U : Finset (Fin 7))
    (hcert : sevenHighT0CountingCertificateHolds mask U)
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    sevenHighT0CanonicalEmptySemanticMask H ≠ mask := by
  intro hmask
  letI : DecidableRel
      (antipodalGraph (sevenHighT0CanonicalFinGraph H)).Adj :=
    Classical.decRel _
  letI : DecidableRel
      (triangleFreeEdgeGraph (sevenHighT0CanonicalFinGraph H)).Adj :=
    Classical.decRel _
  obtain ⟨hfree, hmin, hHigh, hzero⟩ := semantics.finGraph_hypotheses
  let φ := semantics.finGraphEmptyFiberEquiv
  let ψ : Fin 7 → (↑(sevenHighT0LowSupportFiber
      (sevenHighT0CanonicalFinGraph H) 0) : Set (Fin 49)) := fun a =>
    ⟨(φ a).1, Finset.mem_coe.2 (φ a).2⟩
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply φ.injective
    apply Subtype.ext
    exact congrArg Subtype.val hab
  have hψsurj : ∀ x, ∃ a, ψ a = x := by
    intro x
    refine ⟨φ.symm ⟨x.1, Finset.mem_coe.1 x.2⟩, ?_⟩
    apply Subtype.ext
    change (φ (φ.symm ⟨x.1, Finset.mem_coe.1 x.2⟩)).1 = x.1
    rw [φ.apply_symm_apply]
  have hadj : ∀ a b : Fin 7,
      (sevenHighT0CanonicalFinGraph H).Adj (ψ a).1 (ψ b).1 ↔
        sevenHighT0CountingMaskAdj mask a.1 b.1 = true := by
    intro a b
    have h1 := semantics.finGraphEmptyFiberIso.map_adj_iff (v := a) (w := b)
    have h2 := sevenHighT0CanonicalEmptySemanticMaskAdj_eq H a b
    rw [hmask] at h2
    change _ ↔ sevenHighT0CanonicalEmptySemanticMaskAdj mask a.1 b.1 = true
    rw [h2, decide_eq_true_iff]
    exact h1
  have hedges := sevenHighT0CanonicalEmptySemanticMask_countP_eq_internalEdgeCount
    semantics
  rw [hmask] at hedges
  exact sevenHighT0_countingCertificate_contradiction
    (sevenHighT0CanonicalFinGraph H) hfree hmin hHigh hzero mask U
    ψ hψinj hψsurj hadj hedges.symm hcert

/-- Every counting class is semantically excluded. -/
theorem sevenHighT0CanonicalEmptyCube_semanticExclusion_of_counting
    {edgeCount typeIndex : Nat}
    (hmem : (edgeCount, typeIndex) ∈ sevenHighT0CountingCubes) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex := by
  intro H _ semantics
  obtain ⟨c, hc, hfst⟩ := List.mem_map.1 hmem
  have hall := List.all_eq_true.1 sevenHighT0CountingCertificates_hold c hc
  have hcert := of_decide_eq_true hall
  rw [hfst] at hcert
  exact sevenHighT0Canonical_emptyMask_ne_of_countingCertificate
    _ _ hcert semantics

/-- `F6_t2`, the only counting class without an LRAT certificate, is
excluded by the counting argument with `U = {0,1}`. -/
theorem sevenHighT0CanonicalEmptyCube_f6_t2_semanticExclusion :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion 6 2 :=
  sevenHighT0CanonicalEmptyCube_semanticExclusion_of_counting (by decide)

private theorem sevenHighT0MixedEvidence_of_structural
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalEmptyCubeChecked edgeCount typeIndex)
    (edgeCount typeIndex : Nat)
    (h : (edgeCount, typeIndex) ∈ sevenHighT0CountingCubes ∨
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes) :
    SevenHighT0CanonicalEmptyCubeMixedEvidence edgeCount typeIndex := by
  rcases h with h | h
  · exact .semantic
      (sevenHighT0CanonicalEmptyCube_semanticExclusion_of_counting h)
  · exact .checked (hstruct _ _ h)

/-- With the 15 counting classes discharged in Lean, checked UNSAT proofs of
the 28 structural cube CNFs alone exclude every canonical H7/T0 completion. -/
theorem sevenHighT0Canonical_noCompletion_of_structuralChecked
    (hstruct : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalEmptyCubeChecked edgeCount typeIndex) :
    ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H → False := by
  obtain ⟨h6, h7, h8, h9⟩ := sevenHighT0EmptyCube_counting_or_structural
  exact sevenHighT0Canonical_noCompletion_of_mixedEvidenceVectors
    (fun i => sevenHighT0MixedEvidence_of_structural hstruct _ _ (h6 i))
    (fun i => sevenHighT0MixedEvidence_of_structural hstruct _ _ (h7 i))
    (fun i => sevenHighT0MixedEvidence_of_structural hstruct _ _ (h8 i))
    (fun i => sevenHighT0MixedEvidence_of_structural hstruct _ _ (h9 i))

end Erdos85

#print axioms Erdos85.sevenHighT0Canonical_emptyMask_ne_of_countingCertificate
#print axioms Erdos85.sevenHighT0CanonicalEmptyCube_semanticExclusion_of_counting
#print axioms Erdos85.sevenHighT0CanonicalEmptyCube_f6_t2_semanticExclusion
#print axioms Erdos85.sevenHighT0Canonical_noCompletion_of_structuralChecked
