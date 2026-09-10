import Proofs.Erdos85ThreeHighEmptyTemplate
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyAdmissibility

namespace Erdos85
open SimpleGraph

abbrev ThreeHighCross := Fin 15 → Fin 8 → Bool

/-- Necessary conditions on the U-R incidence matrix, for fixed internal graphs.
This definition supplies a finite domain; it does not enumerate that domain. -/
def threeHighCrossDomain (UAdj : Fin 15 → Fin 15 → Bool)
    (RAdj : Fin 8 → Fin 8 → Bool) : Finset ThreeHighCross :=
  Finset.univ.filter fun cross =>
    encodedC4Free (threeHighEmptyAdj UAdj RAdj cross) = true ∧
    encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
      (fun i => if i = 23 then 6 else 4) = true

theorem mem_threeHighCrossDomain_iff
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross) :
    cross ∈ threeHighCrossDomain UAdj RAdj ↔
      encodedC4Free (threeHighEmptyAdj UAdj RAdj cross) = true ∧
      encodedDegreeProfile (threeHighEmptyAdj UAdj RAdj cross)
        (fun i => if i = 23 then 6 else 4) = true := by
  simp only [threeHighCrossDomain, Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] threeHighCrossDomain encodedC4Free encodedDegreeProfile

theorem threeHigh_triple_cross_domain_mem
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
    (heu : (e 23).val = u)
    (UAdj : Fin 15 → Fin 15 → Bool) (RAdj : Fin 8 → Fin 8 → Bool)
    (cross : ThreeHighCross)
    (hB : ∀ p q, decide (G.Adj (e p).val (e q).val) =
      threeHighEmptyAdj UAdj RAdj cross p q) :
    cross ∈ threeHighCrossDomain UAdj RAdj := by
  exact (mem_threeHighCrossDomain_iff UAdj RAdj cross).mpr
    (threeHigh_triple_empty_encoding_admissible G hfree hmin hHigh hone z hz hu huz
      e heu (threeHighEmptyAdj UAdj RAdj cross) hB)

end Erdos85
#print axioms Erdos85.mem_threeHighCrossDomain_iff
#print axioms Erdos85.threeHigh_triple_cross_domain_mem
