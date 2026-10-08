import Full276
import CapacityReduction

/-! Concrete strong-witness census connection. The final rejection theorem
retains every finite search rejection as an explicit hypothesis. -/

namespace FullUStrongFinalCensus
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
      Set (Fin 49))).edgeFinset.card = 4) :
    ∃ (r : Fin 55) (q : Fin 21) (cross : ThreeHighCross), (r,q) ∈ FullCapacityPruning.remainingPairs ∧
      cross ∈ threeHighCrossDomain (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        threeHighCanonicalRow = true ∧
      ThreeHighDistinctJointWitness (threeHighEmptyAdj (FullURestrictedAssembly.representative r)
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := FullUStrongCensus.actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have ht := FullTerminalPruning.actual_pair_mem r q cross hp hc he hj.forget
  have hf := FullCapacityPruning.actual_pair_mem r q cross ht hc he hj.forget
  exact ⟨r,q,cross,hf,hc,he,hj⟩

theorem excluded_of_rejections
    (hreject : ∀ (r : Fin 55) (q : Fin 21), (r,q) ∈ FullCapacityPruning.remainingPairs →
      threeHighNativePairSearch (FullURestrictedAssembly.representative r)
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
      Set (Fin 49))).edgeFinset.card = 4) : False := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := actual_distinct_witness
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  exact threeHighNativePairSearch_no_joint _ _ (hreject r q hp) cross hc he hj

end FullUStrongFinalCensus

#print axioms FullUStrongFinalCensus.actual_distinct_witness
#print axioms FullUStrongFinalCensus.excluded_of_rejections
