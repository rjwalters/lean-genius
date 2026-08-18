import Proofs.Erdos85OrderFortyNineSmallHighProfileMasks
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-!
# Canonical capstone for the three- and five-high strata

There is one canonical mask representative for each admissible triple count:
indices `0,1` at h=3 and `0,1,2` at h=5.  This file isolates the graph-side
normalization obligations and connects their representative exclusions to the
stratum sockets in the order-49 capstone.
-/

namespace Erdos85

open SimpleGraph
open OrderFortyNineSmallHighCensus

def ThreeHighCanonicalRepresentativeExcluded (index : Nat) : Prop :=
  ∀ edges : BitVec 1176,
    orderFortyNineBooleanConstraints 3
      (threeHighRepresentativeMasks index) edges → False

def FiveHighCanonicalRepresentativeExcluded (index : Nat) : Prop :=
  ∀ edges : BitVec 1176,
    orderFortyNineBooleanConstraints 5
      (fiveHighRepresentativeMasks index) edges → False

def ThreeHighCanonicalGraphCover (blocks : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 3 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 3
        (threeHighRepresentativeMasks blocks) edges

def FiveHighCanonicalGraphCover (blocks : Nat) : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (¬ containsC4 (Fin 49) G) →
    (∀ x : Fin 49, 7 ≤ G.degree x) →
    (orderFortyNineHighVertices G).card = 5 →
    orderFortyNineHighIncidenceCount G 3 = blocks →
    ∃ edges : BitVec 1176,
      orderFortyNineBooleanConstraints 5
        (fiveHighRepresentativeMasks blocks) edges

theorem orderFortyNineTripleCellExcluded_three_of_canonical
    {blocks : Nat} (hcover : ThreeHighCanonicalGraphCover blocks)
    (hexcluded : ThreeHighCanonicalRepresentativeExcluded blocks) :
    OrderFortyNineTripleCellExcluded 3 blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨edges, hedges⟩ := hcover G inferInstance inferInstance inferInstance
    hfree hmin hhigh hblocks
  exact hexcluded edges hedges

theorem orderFortyNineTripleCellExcluded_five_of_canonical
    {blocks : Nat} (hcover : FiveHighCanonicalGraphCover blocks)
    (hexcluded : FiveHighCanonicalRepresentativeExcluded blocks) :
    OrderFortyNineTripleCellExcluded 5 blocks := by
  intro G _ _ _ hfree hmin hhigh hblocks
  obtain ⟨edges, hedges⟩ := hcover G inferInstance inferInstance inferInstance
    hfree hmin hhigh hblocks
  exact hexcluded edges hedges

theorem orderFortyNineStratumExcluded_three_of_canonical
    (hcover : ∀ blocks, blocks ≤ 1 → ThreeHighCanonicalGraphCover blocks)
    (hexcluded : ∀ index, index ≤ 1 →
      ThreeHighCanonicalRepresentativeExcluded index) :
    OrderFortyNineStratumExcluded 3 := by
  apply orderFortyNineStratumExcluded_three_of_tripleCells
  · exact orderFortyNineTripleCellExcluded_three_of_canonical
      (hcover 0 (by omega)) (hexcluded 0 (by omega))
  · exact orderFortyNineTripleCellExcluded_three_of_canonical
      (hcover 1 (by omega)) (hexcluded 1 (by omega))

theorem orderFortyNineStratumExcluded_five_of_canonical
    (hcover : ∀ blocks, blocks ≤ 2 → FiveHighCanonicalGraphCover blocks)
    (hexcluded : ∀ index, index ≤ 2 →
      FiveHighCanonicalRepresentativeExcluded index) :
    OrderFortyNineStratumExcluded 5 := by
  apply orderFortyNineStratumExcluded_five_of_tripleCells
  · exact orderFortyNineTripleCellExcluded_five_of_canonical
      (hcover 0 (by omega)) (hexcluded 0 (by omega))
  · exact orderFortyNineTripleCellExcluded_five_of_canonical
      (hcover 1 (by omega)) (hexcluded 1 (by omega))
  · exact orderFortyNineTripleCellExcluded_five_of_canonical
      (hcover 2 (by omega)) (hexcluded 2 (by omega))

end Erdos85
