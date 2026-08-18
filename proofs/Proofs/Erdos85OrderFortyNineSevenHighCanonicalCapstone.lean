import Proofs.Erdos85OrderFortyNineSevenHighProfileMasks
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-!
# Certificate-facing capstone for the canonical seven-high census

The graph normalization and certificate replay lanes meet here.  A graph
cover supplies one of the canonical representative Boolean terminals; checked
exclusion of every representative then inhabits the corresponding semantic
triple-cell socket.
-/

namespace Erdos85

open SimpleGraph
open OrderFortyNineSevenHighCensus

def SevenHighCanonicalRepresentativeExcluded (blocks index : Nat) : Prop :=
  ∀ edges : BitVec 1176,
    orderFortyNineBooleanConstraints 7
      (representativeMasks blocks index) edges → False

def SevenHighCanonicalGraphCover (blocks : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 7 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ index, index < (reps blocks).length ∧ ∃ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 7
        (representativeMasks blocks index) edges

theorem orderFortyNineTripleCellExcluded_seven_of_canonical
    {blocks : Nat} (hcover : SevenHighCanonicalGraphCover blocks)
    (hexcluded : ∀ index, index < (reps blocks).length →
      SevenHighCanonicalRepresentativeExcluded blocks index) :
    OrderFortyNineTripleCellExcluded 7 blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨index, hindex, edges, hedges⟩ :=
    hcover G inferInstance inferInstance inferInstance
      hfree hmin hhigh hblocks
  exact hexcluded index hindex edges hedges

/-- The exact canonical-certificate interface for the complete seven-high
stratum.  Its representative obligations total fourteen. -/
theorem orderFortyNineStratumExcluded_seven_of_canonical
    (hcover : ∀ blocks, blocks ≤ 7 → SevenHighCanonicalGraphCover blocks)
    (hexcluded : ∀ blocks index, blocks ≤ 7 →
      index < (reps blocks).length →
        SevenHighCanonicalRepresentativeExcluded blocks index) :
    OrderFortyNineStratumExcluded 7 := by
  apply orderFortyNineStratumExcluded_seven_of_tripleCells
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 0 (by omega)) (fun index hindex =>
        hexcluded 0 index (by omega) hindex)
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 1 (by omega)) (fun index hindex =>
        hexcluded 1 index (by omega) hindex)
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 2 (by omega)) (fun index hindex =>
        hexcluded 2 index (by omega) hindex)
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 3 (by omega)) (fun index hindex =>
        hexcluded 3 index (by omega) hindex)
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 4 (by omega)) (fun index hindex =>
        hexcluded 4 index (by omega) hindex)
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 5 (by omega)) (fun index hindex =>
        hexcluded 5 index (by omega) hindex)
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 6 (by omega)) (fun index hindex =>
        hexcluded 6 index (by omega) hindex)
  · exact orderFortyNineTripleCellExcluded_seven_of_canonical
      (hcover 7 (by omega)) (fun index hindex =>
        hexcluded 7 index (by omega) hindex)

end Erdos85
