import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeCnf
import Proofs.Erdos85OrderFortyNineSevenHighT0ExteriorCapacityInequality

/-!
# Counting exclusion of H7/T0 empty-sector classes: graph core

The actual vertex-subset inequality
`sevenHigh_t0_vertex_subset_exterior_capacity_inequality` says that for every
subset `U` of the empty-support fiber `E` (with `a = e(E)`)

    35 ≤ 4a + ∑_{v ∈ U} (7 - 2 d_E(v)) + |F[E \ U]|,

where `F` is the graph of pairs of `E` with no common neighbor inside `E`.
Given a labelling `ψ : Fin 7 → E` under which adjacency in `E` is read from a
21-bit mask, `sevenHighT0_countingCertificate_contradiction` bounds the
right-hand side by a computable quantity on `Fin 7`.  One vertex subset per
class then excludes the 15 counting classes of
`R/Q7_H7_UNIVERSAL_SINGLETON_CAPACITY_20260910.md`, including `F6_t2`.
The finite certificate checks are closed by kernel `decide` (no
`native_decide`).

This module is independent of the canonical CNF satisfaction layer; the
canonical-completion wrapper is `...CanonicalEmptyCubeCounting`.
-/

namespace Erdos85

open SimpleGraph

/-- Mask adjacency on empty labels; definitionally the same function as
`sevenHighT0CanonicalEmptySemanticMaskAdj`. -/
def sevenHighT0CountingMaskAdj (mask left right : Nat) : Bool :=
  left != right && mask.testBit
    (sevenHighT0CanonicalLabelPairs.idxOf
      (min left right, max left right))


open SimpleGraph

/-- Degree of `v` in the empty-sector graph encoded by `mask`. -/
def sevenHighT0CountingMaskDegree (mask : Nat) (v : Fin 7) : Nat :=
  (Finset.univ.filter fun w : Fin 7 =>
    sevenHighT0CountingMaskAdj mask v.1 w.1 = true).card

/-- Ordered allowed pairs (`a < b`, no common mask-neighbor) avoiding `U`. -/
def sevenHighT0CountingAllowedAvoiding
    (mask : Nat) (U : Finset (Fin 7)) : Finset (Fin 7 × Fin 7) :=
  Finset.univ.filter fun p =>
    p.1 < p.2 ∧ p.1 ∉ U ∧ p.2 ∉ U ∧
      ∀ w : Fin 7,
        ¬ (sevenHighT0CountingMaskAdj mask p.1.1 w.1 = true ∧
          sevenHighT0CountingMaskAdj mask p.2.1 w.1 = true)

/-- Computable upper bound on the capacity side of the subset inequality. -/
def sevenHighT0CountingUpperBound (mask : Nat) (U : Finset (Fin 7)) : Nat :=
  (∑ v ∈ U, (7 - 2 * sevenHighT0CountingMaskDegree mask v)) +
    (sevenHighT0CountingAllowedAvoiding mask U).card

/-- The certificate condition for one mask and one vertex subset. -/
abbrev sevenHighT0CountingCertificateHolds
    (mask : Nat) (U : Finset (Fin 7)) : Prop :=
  4 * (List.range 21).countP mask.testBit +
    sevenHighT0CountingUpperBound mask U < 35

/-- Generic counting contradiction on an actual H7/T0 graph `G` on `Fin 49`
whose empty fiber is labelled by `ψ : Fin 7 → E` compatibly with `mask`. -/
theorem sevenHighT0_countingCertificate_contradiction
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 7)
    (hzero : orderFortyNineHighIncidenceCount G 3 = 0)
    (mask : Nat) (U : Finset (Fin 7))
    (ψ : Fin 7 → (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)))
    (hψinj : Function.Injective ψ)
    (hψsurj : ∀ x, ∃ a, ψ a = x)
    (hadj : ∀ a b : Fin 7, G.Adj (ψ a).1 (ψ b).1 ↔
      sevenHighT0CountingMaskAdj mask a.1 b.1 = true)
    (hedges : sevenHighT0InternalEdgeCount G 0 =
      (List.range 21).countP mask.testBit)
    (hcert : sevenHighT0CountingCertificateHolds mask U) : False := by
  classical
  let emb : Fin 7 ↪ (↑(sevenHighT0LowSupportFiber G 0) : Set (Fin 49)) :=
    ⟨ψ, hψinj⟩
  have hineq := sevenHigh_t0_vertex_subset_exterior_capacity_inequality
    G hfree hmin hHigh hzero (U.map emb)
  -- degree capacities
  have hsum : (∑ v ∈ U.map emb,
      (7 - 2 * (G.neighborFinset v.val ∩
        sevenHighT0LowSupportFiber G 0).card)) ≤
      ∑ v ∈ U, (7 - 2 * sevenHighT0CountingMaskDegree mask v) := by
    rw [Finset.sum_map]
    apply Finset.sum_le_sum
    intro a _
    have hdeg : sevenHighT0CountingMaskDegree mask a ≤
        (G.neighborFinset (emb a).val ∩
          sevenHighT0LowSupportFiber G 0).card := by
      unfold sevenHighT0CountingMaskDegree
      apply Finset.card_le_card_of_injOn (fun w => (ψ w).1)
      · intro w hw
        have hw' := (Finset.mem_filter.1 (Finset.mem_coe.1 hw)).2
        rw [Finset.mem_coe, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
        exact ⟨(hadj a w).2 hw', Finset.mem_coe.1 (ψ w).2⟩
      · intro w _ w' _ hww'
        exact hψinj (Subtype.ext hww')
    show 7 - 2 * (G.neighborFinset (emb a).val ∩
        sevenHighT0LowSupportFiber G 0).card ≤
      7 - 2 * sevenHighT0CountingMaskDegree mask a
    omega
  -- allowed pairs avoiding `U`
  have hkey : ∀ a b : Fin 7, a < b →
      (insideCommonFreeGraph G (sevenHighT0LowSupportFiber G 0)).Adj
        (ψ a) (ψ b) →
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
  have hallowed :
      ((insideCommonFreeGraph G (sevenHighT0LowSupportFiber G 0)).edgeFinset.filter
        (fun e => ∀ v ∈ U.map emb, v ∉ e)).card ≤
        (sevenHighT0CountingAllowedAvoiding mask U).card := by
    calc
      ((insideCommonFreeGraph G (sevenHighT0LowSupportFiber G 0)).edgeFinset.filter
          (fun e => ∀ v ∈ U.map emb, v ∉ e)).card ≤
          ((sevenHighT0CountingAllowedAvoiding mask U).image
            (fun p => s(ψ p.1, ψ p.2))).card := by
        apply Finset.card_le_card
        intro e he
        rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
        obtain ⟨hedge, havoid⟩ := he
        induction e using Sym2.ind with
        | h x y =>
          obtain ⟨a, rfl⟩ := hψsurj x
          obtain ⟨b, rfl⟩ := hψsurj y
          have hF : (insideCommonFreeGraph G
              (sevenHighT0LowSupportFiber G 0)).Adj (ψ a) (ψ b) := hedge
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

/-- The `F6_t2` certificate on its own: `a = 6` needs `|X| ≥ 11`, while the
subset `U = {0,1}` (the two degree-3 vertices) bounds `|X| ≤ 10`. -/
theorem sevenHighT0CountingCertificate_f6_t2 :
    sevenHighT0CountingCertificateHolds
      (sevenHighT0CanonicalEmptyRepresentativeMask 6 2) {0, 1} := by
  decide

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

end Erdos85

#print axioms Erdos85.sevenHighT0_countingCertificate_contradiction
#print axioms Erdos85.sevenHighT0CountingCertificates_hold
#print axioms Erdos85.sevenHighT0CountingCertificate_f6_t2
#print axioms Erdos85.sevenHighT0EmptyCube_counting_or_structural
