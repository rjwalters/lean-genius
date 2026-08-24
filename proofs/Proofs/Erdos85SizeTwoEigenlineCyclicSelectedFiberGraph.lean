import Proofs.Erdos85SizeTwoEigenlineCyclicCentralFiberSubsystem
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReconstruction
import Proofs.Erdos85SizeTwoEigenlineCyclicRawMatchingAgreement
import Proofs.Erdos85GadgetExtension

/-!
# The graph carried by one selected cyclic difference fiber

This is the graph-theoretic interface for the loopless single-fiber target.
Route reversal makes the routes from a difference fiber back to itself into
an undirected graph on the base group.  The retained `AgreementAt` law says
that two distinct vertices have at most one common neighbor, so this selected
fiber graph is `C4`-free without assuming any agreement law on other fibers.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The subgraph of the reconstructed route graph induced on the cells with
fixed difference `t`, parametrized by their base coordinate. -/
def sizeTwoCyclicSelectedFiberGraph
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) : SimpleGraph (ZMod q) :=
  (sizeTwoCyclicCodeGraph q a code).comap
    (fun x => sizeTwoCyclicCellAt q a x t)

/-- A selected-fiber adjacency is exactly a route whose target difference is
again `t`. -/
theorem sizeTwoCyclicSelectedFiberGraph_adj_iff
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (t : sizeTwoAllowedDifference q a) (x y : ZMod q) :
    (sizeTwoCyclicSelectedFiberGraph code t).Adj x y ↔
      ∃ r : SizeTwoAdmissibleTargetRow q t.1,
        y = x + r.1 ∧ code.targetDifference x t r = t := by
  rw [sizeTwoCyclicSelectedFiberGraph, SimpleGraph.comap_adj,
    sizeTwoCyclicCodeGraph_adj_iff q a code hloop]
  unfold sizeTwoCyclicCodeRouteRel
  rw [sizeTwoCyclicExteriorCellEquiv_cellAt]
  constructor
  · rintro ⟨r, hcell⟩
    have h := congrArg (sizeTwoCyclicExteriorCellEquiv q a) hcell
    refine ⟨r, ?_, ?_⟩
    · exact congrArg Prod.fst h
    · apply Subtype.ext
      simpa using (congrArg (fun z => z.2.1) h).symm
  · rintro ⟨r, hy, ht⟩
    refine ⟨r, ?_⟩
    rw [hy, ht]

/-- A common neighbor in the selected-fiber graph gives an absolute target
edge belonging to both raw source matchings. -/
def sizeTwoCyclicSelectedFiberCommonNeighborToIntersection
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (t : sizeTwoAllowedDifference q a) (x z : ZMod q)
    [DecidableRel (sizeTwoCyclicSelectedFiberGraph code t).Adj]
    (y : {y : ZMod q // y ∈
      (sizeTwoCyclicSelectedFiberGraph code t).neighborFinset x ∩
      (sizeTwoCyclicSelectedFiberGraph code t).neighborFinset z}) :
    {e : SizeTwoCyclicAbsoluteGridEdge q //
      e ∈ sizeTwoCyclicRawSourceMatching code.toPermutationCode.perm (x, t) ∩
        sizeTwoCyclicRawSourceMatching code.toPermutationCode.perm (z, t)} := by
  classical
  let G := sizeTwoCyclicSelectedFiberGraph code t
  have hy := Finset.mem_inter.mp y.2
  have hxy : G.Adj x y.1 := (G.mem_neighborFinset x y.1).mp hy.1
  have hzy : G.Adj z y.1 := (G.mem_neighborFinset z y.1).mp hy.2
  let ex := (sizeTwoCyclicSelectedFiberGraph_adj_iff
    code hloop t x y.1).mp hxy
  let ez := (sizeTwoCyclicSelectedFiberGraph_adj_iff
    code hloop t z y.1).mp hzy
  let rx := Classical.choose ex
  let rz := Classical.choose ez
  have hxspec := Classical.choose_spec ex
  have hzspec := Classical.choose_spec ez
  have hyx := hxspec.1
  have htx := hxspec.2
  have hyz := hzspec.1
  have htz := hzspec.2
  refine ⟨(y.1, y.1 + t.1), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
  · apply (sizeTwoCyclicRawSourceMatching_mem_iff
      code.toPermutationCode.perm (x, t) _).mpr
    refine ⟨rx, ?_⟩
    apply Prod.ext
    · exact hyx.symm
    · change x + (code.toPermutationCode.perm x t rx).1 = y.1 + t.1
      have hc := code.target_column_eq x t rx
      rw [← hc, htx, hyx]
      abel
  · apply (sizeTwoCyclicRawSourceMatching_mem_iff
      code.toPermutationCode.perm (z, t) _).mpr
    refine ⟨rz, ?_⟩
    apply Prod.ext
    · exact hyz.symm
    · change z + (code.toPermutationCode.perm z t rz).1 = y.1 + t.1
      have hc := code.target_column_eq z t rz
      rw [← hc, htz, hyz]
      abel

theorem sizeTwoCyclicSelectedFiberCommonNeighborToIntersection_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (t : sizeTwoAllowedDifference q a) (x z : ZMod q)
    [DecidableRel (sizeTwoCyclicSelectedFiberGraph code t).Adj] :
    Function.Injective
      (sizeTwoCyclicSelectedFiberCommonNeighborToIntersection
        code hloop t x z) := by
  intro y y' h
  apply Subtype.ext
  exact congrArg (fun e => e.1.1) h

/-- One-fiber agreement is precisely enough to make the selected-fiber graph
`C4`-free.  No agreement hypothesis on any other difference is used. -/
theorem sizeTwoCyclicSelectedFiberGraph_not_containsC4
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (hloop : code.Loopless)
    (t : sizeTwoAllowedDifference q a)
    (hagreement : code.toRoutingData.AgreementAt t) :
    ¬ containsC4 (ZMod q) (sizeTwoCyclicSelectedFiberGraph code t) := by
  classical
  let G := sizeTwoCyclicSelectedFiberGraph code t
  letI : DecidableRel G.Adj := Classical.decRel _
  apply not_containsC4_of_forall_common_le_one
  intro x z hxz
  have hne : z - x ≠ 0 := sub_ne_zero.mpr hxz.symm
  calc
    (G.neighborFinset x ∩ G.neighborFinset z).card =
        Fintype.card {y : ZMod q // y ∈
          G.neighborFinset x ∩ G.neighborFinset z} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card {e : SizeTwoCyclicAbsoluteGridEdge q //
          e ∈ sizeTwoCyclicRawSourceMatching code.toPermutationCode.perm (x, t) ∩
            sizeTwoCyclicRawSourceMatching code.toPermutationCode.perm (z, t)} :=
      Fintype.card_le_of_injective
        (sizeTwoCyclicSelectedFiberCommonNeighborToIntersection
          code hloop t x z)
        (sizeTwoCyclicSelectedFiberCommonNeighborToIntersection_injective
          code hloop t x z)
    _ = Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
          code.toPermutationCode.perm x (z - x) t t) := by
      rw [Fintype.card_coe]
      exact sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement
        code.toPermutationCode.perm (x, t) (z, t)
    _ ≤ 1 := hagreement x (z - x) hne

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicSelectedFiberGraph_adj_iff
#print axioms Erdos85.sizeTwoCyclicSelectedFiberGraph_not_containsC4
