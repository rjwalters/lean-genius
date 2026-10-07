import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSemanticExclusion
import Proofs.Erdos85OrderFortyNineSevenHighT0ExteriorCapacityInequality

/-!
# Counting exclusion of canonical H7/T0 empty cubes

The actual vertex-subset inequality
`sevenHigh_t0_vertex_subset_exterior_capacity_inequality` says that for every
subset `U` of the empty-support fiber `E` (with `a = e(E)`)

    35 ≤ 4a + ∑_{v ∈ U} (7 - 2 d_E(v)) + |F[E \ U]|,

where `F` is the graph of pairs of `E` with no common neighbor inside `E`.
For a canonical completion this file transports the right-hand side to the
21-bit empty-sector mask on `Fin 7` (as an upper bound), producing a
computable certificate check.  One vertex subset per class then excludes the
15 counting classes (`R/Q7_H7_UNIVERSAL_SINGLETON_CAPACITY_20260910.md`),
including `F6_t2`, the one counting class without an LRAT certificate.

The finite certificate checks are closed by kernel `decide`.
-/

namespace Erdos85

open SimpleGraph

/-- Degree of `v` in the empty-sector graph encoded by `mask`. -/
def sevenHighT0CountingMaskDegree (mask : Nat) (v : Fin 7) : Nat :=
  (Finset.univ.filter fun w : Fin 7 =>
    sevenHighT0CanonicalEmptySemanticMaskAdj mask v.1 w.1 = true).card

/-- Ordered allowed pairs (`a < b`, no common mask-neighbor) avoiding `U`. -/
def sevenHighT0CountingAllowedAvoiding
    (mask : Nat) (U : Finset (Fin 7)) : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter fun p =>
    p.1 < p.2 ∧ p.1 ∉ U ∧ p.2 ∉ U ∧
      ∀ w : Fin 7,
        ¬ (sevenHighT0CanonicalEmptySemanticMaskAdj mask p.1.1 w.1 = true ∧
          sevenHighT0CanonicalEmptySemanticMaskAdj mask p.2.1 w.1 = true)

/-- Computable upper bound on the capacity side of the subset inequality. -/
def sevenHighT0CountingUpperBound (mask : Nat) (U : Finset (Fin 7)) : Nat :=
  (∑ v ∈ U, (7 - 2 * sevenHighT0CountingMaskDegree mask v)) +
    (sevenHighT0CountingAllowedAvoiding mask U).card

/-- The certificate condition for one mask and one vertex subset. -/
def sevenHighT0CountingCertificateHolds
    (mask : Nat) (U : Finset (Fin 7)) : Prop :=
  4 * (List.range 21).countP mask.testBit +
    sevenHighT0CountingUpperBound mask U < 35

instance (mask : Nat) (U : Finset (Fin 7)) :
    Decidable (sevenHighT0CountingCertificateHolds mask U) := by
  unfold sevenHighT0CountingCertificateHolds
  infer_instance

/-- Core counting theorem: a canonical completion graph cannot have an
empty-sector mask for which some vertex subset violates the actual
capacity inequality. -/
theorem sevenHighT0Canonical_emptyMask_ne_of_countingCertificate
    (mask : Nat) (U : Finset (Fin 7))
    (hcert : sevenHighT0CountingCertificateHolds mask U)
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    sevenHighT0CanonicalEmptySemanticMask H ≠ mask := by
  classical
  intro hmask
  let G := sevenHighT0CanonicalFinGraph H
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨hfree, hmin, hHigh, hzero⟩ := semantics.finGraph_hypotheses
  let E := sevenHighT0LowSupportFiber G 0
  let φ := semantics.finGraphEmptyFiberEquiv
  let ψ : Fin 7 → (↑E : Set (Fin 49)) := fun a =>
    ⟨(φ a).1, Finset.mem_coe.2 (φ a).2⟩
  have hψval : ∀ a, (ψ a).1 = (φ a).1 := fun _ => rfl
  have hψinj : Function.Injective ψ := by
    intro a b hab
    apply φ.injective
    apply Subtype.ext
    exact congrArg Subtype.val hab
  have hψsurj : ∀ x : (↑E : Set (Fin 49)), ∃ a, ψ a = x := by
    intro x
    refine ⟨φ.symm ⟨x.1, Finset.mem_coe.1 x.2⟩, ?_⟩
    apply Subtype.ext
    rw [hψval, φ.apply_symm_apply]
  -- adjacency inside `E` is the mask adjacency
  have hadj : ∀ a b : Fin 7, G.Adj (φ a).1 (φ b).1 ↔
      sevenHighT0CanonicalEmptySemanticMaskAdj mask a.1 b.1 = true := by
    intro a b
    have h1 := semantics.finGraphEmptyFiberIso.map_adj_iff (v := a) (w := b)
    have h2 := sevenHighT0CanonicalEmptySemanticMaskAdj_eq H a b
    rw [hmask] at h2
    rw [h2, decide_eq_true_iff]
    exact h1
  let emb : Fin 7 ↪ (↑E : Set (Fin 49)) := ⟨ψ, hψinj⟩
  have hineq := sevenHigh_t0_vertex_subset_exterior_capacity_inequality
    G hfree hmin hHigh hzero (U.map emb)
  -- internal edge count
  have hedges : sevenHighT0InternalEdgeCount G 0 =
      (List.range 21).countP mask.testBit := by
    have h := sevenHighT0CanonicalEmptySemanticMask_countP_eq_internalEdgeCount
      semantics
    rw [hmask] at h
    exact h.symm
  -- degree capacities
  have hsum : (∑ v ∈ U.map emb,
      (7 - 2 * (G.neighborFinset v.val ∩ E).card)) ≤
      ∑ v ∈ U, (7 - 2 * sevenHighT0CountingMaskDegree mask v) := by
    rw [Finset.sum_map]
    apply Finset.sum_le_sum
    intro a _
    have hdeg : sevenHighT0CountingMaskDegree mask a ≤
        (G.neighborFinset (emb a).val ∩ E).card := by
      unfold sevenHighT0CountingMaskDegree
      apply Finset.card_le_card_of_injOn (fun w => (φ w).1)
      · intro w hw
        have hw' := (Finset.mem_filter.1 (Finset.mem_coe.1 hw)).2
        rw [Finset.mem_coe, Finset.mem_inter, mem_neighborFinset]
        exact ⟨(hadj a w).2 hw', (φ w).2⟩
      · intro w _ w' _ hww'
        exact φ.injective (Subtype.ext hww')
    omega
  -- allowed pairs avoiding `U`
  have hallowed :
      ((insideCommonFreeGraph G E).edgeFinset.filter
        (fun e => ∀ v ∈ U.map emb, v ∉ e)).card ≤
        (sevenHighT0CountingAllowedAvoiding mask U).card := by
    have hkey : ∀ a b : Fin 7, a < b →
        (insideCommonFreeGraph G E).Adj (ψ a) (ψ b) →
        ψ a ∉ U.map emb → ψ b ∉ U.map emb →
        (a, b) ∈ sevenHighT0CountingAllowedAvoiding mask U := by
      intro a b hab hF ha hb
      unfold sevenHighT0CountingAllowedAvoiding
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hab, ?_, ?_, ?_⟩
      · intro haU
        exact ha (Finset.mem_map_of_mem emb haU)
      · intro hbU
        exact hb (Finset.mem_map_of_mem emb hbU)
      · intro w hw
        apply hF.2 (ψ w)
        exact ⟨(hadj a w).2 hw.1, (hadj b w).2 hw.2⟩
    calc
      ((insideCommonFreeGraph G E).edgeFinset.filter
          (fun e => ∀ v ∈ U.map emb, v ∉ e)).card ≤
          ((sevenHighT0CountingAllowedAvoiding mask U).image
            (fun p => s(ψ p.1, ψ p.2))).card := by
        apply Finset.card_le_card
        intro e he
        rw [Finset.mem_filter, mem_edgeFinset] at he
        obtain ⟨hedge, havoid⟩ := he
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨a, rfl⟩ := hψsurj x
          obtain ⟨b, rfl⟩ := hψsurj y
          have hF : (insideCommonFreeGraph G E).Adj (ψ a) (ψ b) := hedge
          have ha : ψ a ∉ U.map emb := fun h =>
            havoid _ h (Sym2.mem_mk_left _ _)
          have hb : ψ b ∉ U.map emb := fun h =>
            havoid _ h (Sym2.mem_mk_right _ _)
          have hne : a ≠ b := by
            intro h
            subst h
            exact hF.1 rfl
          rw [Finset.mem_image]
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact ⟨(a, b), hkey a b hlt hF ha hb, rfl⟩
          · exact ⟨(b, a), hkey b a hgt hF.symm hb ha, Sym2.eq_swap⟩
      _ ≤ (sevenHighT0CountingAllowedAvoiding mask U).card :=
        Finset.card_image_le
  unfold sevenHighT0CountingCertificateHolds sevenHighT0CountingUpperBound
    at hcert
  omega

/-- The fifteen counting classes, each with its vertex-subset certificate
`U` (Lean empty-vertex labels `0..6`). -/
def sevenHighT0CountingCertificates : List ((Nat × Nat) × List (Fin 7)) :=
  [((6, 0), [0, 1, 2]), ((6, 1), [0, 1]), ((6, 2), [0, 1]),
   ((6, 3), [3]), ((6, 4), [0, 4]), ((6, 6), [0, 4]),
   ((6, 7), [0, 1]), ((6, 9), [0, 4]), ((6, 10), [0, 4]),
   ((6, 11), [0, 4]), ((6, 12), [0, 4]), ((6, 13), [0]),
   ((7, 1), [1, 3]), ((7, 7), [0, 4]), ((7, 12), [0, 4])]

/-- The counting-excluded cube indices. -/
def sevenHighT0CountingCubes : List (Nat × Nat) :=
  sevenHighT0CountingCertificates.map Prod.fst

/-- The 28 structural cubes not covered by the counting argument. -/
def sevenHighT0StructuralCubes : List (Nat × Nat) :=
  [(6, 5), (6, 8), (6, 14), (6, 15), (6, 16), (6, 17), (6, 18),
   (7, 0), (7, 2), (7, 3), (7, 4), (7, 5), (7, 6), (7, 8), (7, 9),
   (7, 10), (7, 11), (7, 13), (7, 14),
   (8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 6),
   (9, 0), (9, 1)]

set_option maxRecDepth 100000 in
/-- Every listed subset certificate is a strict contradiction. -/
theorem sevenHighT0CountingCertificates_hold :
    sevenHighT0CountingCertificates.all (fun c =>
      decide (sevenHighT0CountingCertificateHolds
        (sevenHighT0CanonicalEmptyRepresentativeMask c.1.1 c.1.2)
        c.2.toFinset)) = true := by
  decide

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

/-- Each of the 43 cubes is a counting cube or a structural cube. -/
theorem sevenHighT0EmptyCube_counting_or_structural :
    (∀ i : Fin 19, (6, i.1) ∈ sevenHighT0CountingCubes ∨
        (6, i.1) ∈ sevenHighT0StructuralCubes) ∧
    (∀ i : Fin 15, (7, i.1) ∈ sevenHighT0CountingCubes ∨
        (7, i.1) ∈ sevenHighT0StructuralCubes) ∧
    (∀ i : Fin 7, (8, i.1) ∈ sevenHighT0CountingCubes ∨
        (8, i.1) ∈ sevenHighT0StructuralCubes) ∧
    (∀ i : Fin 2, (9, i.1) ∈ sevenHighT0CountingCubes ∨
        (9, i.1) ∈ sevenHighT0StructuralCubes) := by
  decide

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
#print axioms Erdos85.sevenHighT0CountingCertificates_hold
#print axioms Erdos85.sevenHighT0CanonicalEmptyCube_semanticExclusion_of_counting
#print axioms Erdos85.sevenHighT0CanonicalEmptyCube_f6_t2_semanticExclusion
#print axioms Erdos85.sevenHighT0Canonical_noCompletion_of_structuralChecked
