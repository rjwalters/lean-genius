import Proofs.Erdos85OneHighCanonicalMate
import Proofs.Erdos85PairedBlockRigidity

/-! # Graph-side F3b equality for the exact v2 orbit formula -/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- For far high branches, the encoded common-pair block has cardinality
`20` plus the two cross-mate directed miss counts. -/
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
  calc
    (oneHighEncodedCommonPairBlock R (branchLabel s)
        (branchLabel t)).card =
        (orderFortyNineOuterNondefectBlock G v s t).card := htrans
    _ = 20 + highBranchMissCount G v s (mate t) +
        highBranchMissCount G v t (mate s) := hrigid

end

end Erdos85
