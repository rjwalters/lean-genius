import Assembly
import Pruning
import Proofs.Erdos85ThreeHighDistinctRepresentativeWitness
import Proofs.Erdos85ThreeHighNativePairSearch

/-! Concrete strong-witness census connection. The final rejection theorem
retains every finite search rejection as an explicit hypothesis. -/

namespace DeficientUStrongCensus
open Erdos85 SimpleGraph
set_option maxRecDepth 100000
attribute [local irreducible] threeHighCrossDomain

theorem actual_distinct_witness
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 3) :
    ∃ (r : Fin 370) (q : Fin 21) (cross : ThreeHighCross),
      (r,q) ∈ DeficientUOrbitPruning.remainingPairs ∧
      cross ∈ threeHighCrossDomain (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  obtain ⟨r,q,cross,hq,hc,he,hj⟩ := threeHigh_deficient_distinct_representative_witness
    DeficientUNormalizedAssembly.representative DeficientUNormalizedAssembly.covered
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  exact ⟨r,q,cross,DeficientUOrbitPruning.actual_pair_mem r q cross hq hc he,hc,he,hj⟩

theorem excluded_of_rejections
    (hreject : ∀ (r : Fin 370) (q : Fin 21), (r,q) ∈ DeficientUOrbitPruning.remainingPairs →
      threeHighNativePairSearch (DeficientUNormalizedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) = false)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 3) : False := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  exact threeHighNativePairSearch_no_joint _ _ (hreject r q hp) cross hc he hj

end DeficientUStrongCensus

#print axioms DeficientUStrongCensus.actual_distinct_witness
#print axioms DeficientUStrongCensus.excluded_of_rejections
