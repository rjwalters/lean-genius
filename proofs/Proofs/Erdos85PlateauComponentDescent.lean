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
      (∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
      ¬ C4FreeMinDegreeWitness (m + 1) d ∧
      ∀ c : G.ConnectedComponent, c.supp.ncard < m →
        C4PlateauCore c.supp.ncard d := by
  obtain ⟨G, hdec, hmin, hfree, hcover, hnext, hcomponents⟩ :=
    hcore.exists_component_local_obstructions hm
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, hcover, hnext, ?_⟩
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
  obtain ⟨G, hdec, hmin, hfree, _hcover, _hnext, hdescend⟩ :=
    hcore.exists_component_plateauCore hm
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  intro c e hce
  have hc : c.supp.ncard < m := by
    simpa using connectedComponent_ncard_lt_card_of_ne G c e hce
  exact ⟨hc, hdescend c hc⟩

/-- A plateau core is order-minimal (within the nondegenerate range) when no
strictly smaller order at least four carries a core at the same degree. -/
def OrderMinimalC4PlateauCore (m d : ℕ) : Prop :=
  C4PlateauCore m d ∧
    ∀ n, 4 ≤ n → n < m → ¬ C4PlateauCore n d

/-- **Connected minimal-core normal form.** Every order-minimal plateau core
of degree at least four has a connected representative. -/
theorem OrderMinimalC4PlateauCore.exists_connected_representative
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d)
    (hminimal : OrderMinimalC4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      (∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
      ¬ C4FreeMinDegreeWitness (m + 1) d ∧
      Fintype.card G.ConnectedComponent = 1 := by
  obtain ⟨G, hdec, hmin, hfree, hcover, hnext, hdescend⟩ :=
    hminimal.1.exists_component_plateauCore hm
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, hcover, hnext, ?_⟩
  by_contra hcard
  have hnonempty : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin m) := hnonempty
  have hpos : 0 < Fintype.card G.ConnectedComponent := Fintype.card_pos
  have hone : 1 < Fintype.card G.ConnectedComponent := by omega
  obtain ⟨c, e, hce⟩ := Fintype.one_lt_card_iff.mp hone
  have hc : c.supp.ncard < m := by
    simpa using connectedComponent_ncard_lt_card_of_ne G c e hce
  have hcLower : d * (d - 1) + 2 ≤ c.supp.ncard :=
    connectedComponent_clean_moore_bound G hfree (by omega) hmin.ge c
  have hfour : 4 ≤ d * (d - 1) + 2 := by
    obtain ⟨a, rfl⟩ : ∃ a, d = a + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  exact hminimal.2 c.supp.ncard (hfour.trans hcLower) hc (hdescend c hc)

/-- Every nondegenerate plateau core has a least-order plateau core at the
same degree, no larger than the original order. -/
theorem C4PlateauCore.exists_orderMinimal_le
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ n, 4 ≤ n ∧ n ≤ m ∧ OrderMinimalC4PlateauCore n d := by
  classical
  let P : ℕ → Prop := fun n ↦ 4 ≤ n ∧ C4PlateauCore n d
  have hex : ∃ n, P n := ⟨m, hm, hcore⟩
  let n := Nat.find hex
  have hn : P n := Nat.find_spec hex
  refine ⟨n, hn.1, ?_, hn.2, ?_⟩
  · exact Nat.find_min' hex ⟨hm, hcore⟩
  · intro k hk hkn hkcore
    have hle : n ≤ k := Nat.find_min' hex ⟨hk, hkcore⟩
    omega

/-- **Global connected-core reduction.** From any degree-`d ≥ 4` plateau
core one obtains a no-larger order-minimal core with a connected
representative. -/
theorem C4PlateauCore.exists_le_connected_orderMinimal
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d)
    (hcore : C4PlateauCore m d) :
    ∃ n ≤ m, OrderMinimalC4PlateauCore n d ∧
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        G.minDegree = d ∧ ¬ containsC4 (Fin n) G ∧
        (∀ ⦃u v⦄, G.Adj u v → G.degree u = d ∨ G.degree v = d) ∧
        ¬ C4FreeMinDegreeWitness (n + 1) d ∧
        Fintype.card G.ConnectedComponent = 1 := by
  obtain ⟨n, hn4, hnm, hnminimal⟩ := hcore.exists_orderMinimal_le hm
  exact ⟨n, hnm, hnminimal,
    hnminimal.exists_connected_representative hn4 hd⟩

end Erdos85
