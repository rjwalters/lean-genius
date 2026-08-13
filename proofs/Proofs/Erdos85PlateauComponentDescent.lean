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

/-- In a finite graph, a connected component is proper as soon as there is a
distinct connected component. -/
theorem connectedComponent_ncard_lt_card_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c e : G.ConnectedComponent) (hce : c ≠ e) :
    c.supp.ncard < Fintype.card V := by
  classical
  have hsum : (∑ a : G.ConnectedComponent, a.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ a : G.ConnectedComponent, a.supp.ncard) =
          ∑ a : G.ConnectedComponent, Fintype.card a.supp := by
            apply Finset.sum_congr rfl
            intro a _
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq a.supp).symm
      _ = Fintype.card (Σ a : G.ConnectedComponent, a.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
  have hpair : c.supp.ncard + e.supp.ncard ≤
      ∑ a : G.ConnectedComponent, a.supp.ncard := by
    calc
      c.supp.ncard + e.supp.ncard =
          ∑ a ∈ ({c, e} : Finset G.ConnectedComponent), a.supp.ncard := by
            simp [hce]
      _ ≤ ∑ a ∈ (Finset.univ : Finset G.ConnectedComponent),
          a.supp.ncard := by
            exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by simp)
      _ = ∑ a : G.ConnectedComponent, a.supp.ncard := by simp
  have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
  omega

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

/-- A plateau representative with two distinct components exposes a strictly
smaller plateau core at the same degree. -/
theorem C4PlateauCore.exists_strictly_smaller_component_plateauCore
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      ∀ c e : G.ConnectedComponent, c ≠ e →
        c.supp.ncard < m ∧ C4PlateauCore c.supp.ncard d := by
  obtain ⟨G, hdec, hmin, hfree, hdescend⟩ :=
    hcore.exists_component_plateauCore hm
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  intro c e hce
  have hc : c.supp.ncard < m := by
    simpa using connectedComponent_ncard_lt_card_of_ne G c e hce
  exact ⟨hc, hdescend c hc⟩

end Erdos85
