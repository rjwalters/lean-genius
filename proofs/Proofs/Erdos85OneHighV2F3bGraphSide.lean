import Proofs.Erdos85OneHighCanonicalMate
import Proofs.Erdos85PairedBlockRigidity

/-!
# Graph-side F3b equality for the exact v2 orbit formula

Composes the encoded common-pair transport
(`card_oneHighEncodedCommonPairBlock_eq_outerNondefect`) with exact
outer nondefect block rigidity
(`graph_exact_outerNondefectBlocks_of_mate_involution`) to express the
encoded unpaired common-pair cardinality as `20` plus the two
cross-mate miss counts — the raw graph-side input for the v2 F3b
ledger `count_eq`.  The worker-table transport (matched-only counts
equal full deficits) is supplied by the F1 bridge and composes on top.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Encoded unpaired common-pair count: for a far pair `s, t` of high
branches (neither equal nor mates), the encoded common-pair block has
cardinality exactly `20` plus the two cross-mate miss counts. -/
theorem card_oneHighEncodedCommonPairBlock_eq_twenty_add_missCounts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateInv : Function.Involutive mate)
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hts : t ≠ s) (htm : t ≠ mate s) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    (oneHighEncodedCommonPairBlock R (branchLabel s)
        (branchLabel t)).card =
      20 + highBranchMissCount G v s (mate t) +
        highBranchMissCount G v t (mate s) := by
  intro E R
  have hst : s ≠ t := fun h => hts h.symm
  have htrans := card_oneHighEncodedCommonPairBlock_eq_outerNondefect
    G hfree branchLabel leafLabel s t hst
  have hmem : t ∈ (Finset.univ.erase s).erase (mate s) :=
    Finset.mem_erase.mpr ⟨htm,
      Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩⟩
  have hrigid := (graph_exact_outerNondefectBlocks_of_mate_involution
    G hfree hmin hcard hv hunique hexternal houterDegree
      mate hmateInv hmateAdj s).2 t hmem
  calc (oneHighEncodedCommonPairBlock R (branchLabel s)
        (branchLabel t)).card
      = (orderFortyNineOuterNondefectBlock G v s t).card := htrans
    _ = 20 + highBranchMissCount G v s (mate t) +
        highBranchMissCount G v t (mate s) := hrigid

end

end Erdos85
