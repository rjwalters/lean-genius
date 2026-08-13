import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85Relabel

/-!
# Plateau-core descent to connected components

Every proper connected component of a plateau core inherits all plateau-core
axioms.  Relabeling the component onto its finite cardinality therefore gives
a strictly smaller plateau core at the same degree.  This reduces the global
program to connected minimal cores without discarding one-step
nonextendability.
-/

namespace Erdos85

open SimpleGraph

/-- A proper connected component of a plateau core, canonically relabeled
onto `Fin c.supp.ncard`, is itself a plateau core at the same degree. -/
theorem C4PlateauCore.exists_component_plateauCore
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      ∀ c : G.ConnectedComponent, c.supp.ncard < m →
        C4PlateauCore c.supp.ncard d := by
  obtain ⟨G, hdec, hmin, hfree, hcomponents⟩ :=
    hcore.exists_component_local_obstructions hm
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  intro c hc
  dsimp at hcomponents
  obtain ⟨hminC, hfreeC, hcoverC, hnoC⟩ := hcomponents c
  let K := G.induce c.supp
  have hcard : Fintype.card c.supp = c.supp.ncard :=
    Set.fintypeCard_eq_ncard c.supp
  let H : SimpleGraph (Fin c.supp.ncard) := K.overFin hcard
  let e : K ≃g H := K.overFinIso hcard
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  refine ⟨H, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact e.minDegree_eq.symm.trans hminC
  · intro hC4
    exact hfreeC ((containsC4_iff_of_iso e).mpr hC4)
  · intro u v huv
    have huvK : K.Adj (e.symm u) (e.symm v) :=
      e.symm.map_rel_iff.mp huv
    rcases hcoverC huvK with hu | hv
    · left
      calc
        H.degree u = K.degree (e.symm u) := by
          simpa using (e.degree_eq (e.symm u)).symm
        _ = d := hu
    · right
      calc
        H.degree v = K.degree (e.symm v) := by
          simpa using (e.degree_eq (e.symm v)).symm
        _ = d := hv
  · intro L hLdec hLmin
    by_contra hLfree
    exact hnoC hc ⟨L, hLdec, hLmin, hLfree⟩

end Erdos85
