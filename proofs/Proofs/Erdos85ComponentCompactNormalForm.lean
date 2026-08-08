import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85NonextendableCompactness
import Proofs.Erdos85ConflictDegreeAccounting

/-!
# Compact normal form for proper plateau components

This file combines the componentwise nonextension reduction with the
quadratic conductor and exact nonregular conflict accounting.  It provides a
single starting interface for the remaining compression problem.
-/

namespace Erdos85

open SimpleGraph

/-- **Compact connected-obstruction normal form.**  Every proper component
of an edge-minimal plateau representative is itself an exact-degree,
edge-minimal, nonextendable obstruction.  It has quadratic order, the sharp
universal degree window, conflict independence below `d`, and exact conflict
degree `degree x * (d-1)` at each non-tight vertex. -/
theorem C4PlateauCore.exists_component_compact_normalForm
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      ∀ c : G.ConnectedComponent, c.supp.ncard < m →
        let H := G.induce c.supp
        H.minDegree = d ∧
        ¬ containsC4 c.supp H ∧
        (∀ ⦃u v : c.supp⦄, H.Adj u v →
          H.degree u = d ∨ H.degree v = d) ∧
        ¬ C4FreeMinDegreeWitness (c.supp.ncard + 1) d ∧
        c.supp.ncard + 1 < 36 * d * d ∧
        (∀ x : c.supp, H.degree x ≤ 2 * d - 2) ∧
        (Odd d → ∀ x : c.supp, H.degree x ≤ 2 * d - 3) ∧
        (commonNeighborConflict H).indepNum < d ∧
        (∀ x : c.supp, H.degree x ≠ d →
          (commonNeighborConflict H).degree x =
            H.degree x * (d - 1)) := by
  have hd : 2 ≤ d := hcore.two_le_degree hm
  obtain ⟨G, hdec, hmin, hfree, hcomponents⟩ :=
    hcore.exists_component_local_obstructions hm
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  intro c hc
  dsimp
  obtain ⟨hminC, hfreeC, hcoverC, hnoC⟩ := hcomponents c
  have hcardC : Fintype.card c.supp = c.supp.ncard := by
    exact Set.fintypeCard_eq_ncard c.supp
  obtain ⟨horder, hupper, hoddUpper, hind⟩ :=
    nonextendable_witness_compactness (G.induce c.supp)
      hcardC hd hminC.ge hfreeC (hnoC hc)
  refine ⟨hminC, hfreeC, hcoverC, hnoC hc, horder,
    hupper, hoddUpper, hind, ?_⟩
  intro x hx
  exact degree_commonNeighborConflict_eq_degree_mul_pred_of_nontight
    (G.induce c.supp) hfreeC (d := d)
      (fun {_u _v} huv ↦ hcoverC huv) x hx

end Erdos85
