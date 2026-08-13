import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85NonextendableCompactness
import Proofs.Erdos85ConflictDegreeAccounting
import Proofs.Erdos85PlateauComponentDescent

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
  obtain ⟨G, hdec, hmin, hfree, _hcover, _hnext, hcomponents⟩ :=
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

/-- **Connected compact minimal-core normal form.** An order-minimal plateau
core has a single representative carrying all graph-facing data needed by
the compactness, conflict, and surgery programs. -/
theorem OrderMinimalC4PlateauCore.exists_connected_compact_normalForm
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d)
    (hminimal : OrderMinimalC4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧
      ¬ containsC4 (Fin m) G ∧
      (∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
      ¬ C4FreeMinDegreeWitness (m + 1) d ∧
      Fintype.card G.ConnectedComponent = 1 ∧
      m + 1 < 36 * d * d ∧
      (∀ x, G.degree x ≤ 2 * d - 2) ∧
      (Odd d → ∀ x, G.degree x ≤ 2 * d - 3) ∧
      (commonNeighborConflict G).indepNum < d ∧
      (∀ x, G.degree x ≠ d →
        (commonNeighborConflict G).degree x = G.degree x * (d - 1)) := by
  obtain ⟨G, hdec, hmin, hfree, hcover, hnext, hconnected⟩ :=
    hminimal.exists_connected_representative hm hd
  letI : DecidableRel G.Adj := hdec
  have hcard : Fintype.card (Fin m) = m := Fintype.card_fin m
  obtain ⟨horder, hupper, hoddUpper, hind⟩ :=
    nonextendable_witness_compactness G hcard (by omega) hmin.ge hfree hnext
  refine ⟨G, hdec, hmin, hfree, hcover, hnext, hconnected,
    horder, hupper, hoddUpper, hind, ?_⟩
  intro x hx
  exact degree_commonNeighborConflict_eq_degree_mul_pred_of_nontight
    G hfree (d := d) (fun {_u _v} huv ↦ hcover huv) x hx

end Erdos85
