import Proofs.Erdos85OrderSixtyFourTenSixEncoding
import Proofs.Erdos85IsCyclesComponentCharpoly

/-! # Constructing the certificate labeling of a `[10,6]` two-factor -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A connected component of a finite two-regular graph is not merely the
right size: it admits cycle coordinates preserving adjacency. -/
theorem exists_componentCycleEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (c : H.ConnectedComponent) (n : Nat) (hc : c.supp.ncard = n) :
    ∃ e : Fin n ≃ c.supp,
      ∀ i j, (cycleGraph n).Adj i j ↔ H.Adj (e i).1 (e j).1 := by
  classical
  obtain ⟨x, p, hp, hpverts, hgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph H hdeg c
  have hlen : p.length = n := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
      _ = n := hc
  clear hc
  subst n
  let e : Fin p.length ≃ c.supp :=
    (cycleVertexEquiv hp).trans (Equiv.setCongr hpverts)
  refine ⟨e, ?_⟩
  intro i j
  have hij : (cycleGraph p.length).Adj i j ↔
      p.toSubgraph.coe.Adj (cycleVertexEquiv hp i)
        (cycleVertexEquiv hp j) :=
    (isCycle_cycleGraphIsoToSubgraph hp).map_rel_iff.symm
  change (cycleGraph p.length).Adj i j ↔
    H.Adj ((Equiv.setCongr hpverts) (cycleVertexEquiv hp i)).1
      ((Equiv.setCongr hpverts) (cycleVertexEquiv hp j)).1
  rw [hij]
  rw [hgraph]
  rfl

theorem tenSixCycleGraph_left : ∀ i j : Fin 10,
    tenSixCycleGraph.Adj (Fin.castAdd 6 i) (Fin.castAdd 6 j) ↔
      (cycleGraph 10).Adj i j := by
  native_decide

theorem tenSixCycleGraph_right : ∀ i j : Fin 6,
    tenSixCycleGraph.Adj (Fin.natAdd 10 i) (Fin.natAdd 10 j) ↔
      (cycleGraph 6).Adj i j := by
  native_decide

theorem tenSixCycleGraph_cross_left_right : ∀ (i : Fin 10) (j : Fin 6),
    ¬tenSixCycleGraph.Adj (Fin.castAdd 6 i) (Fin.natAdd 10 j) := by
  native_decide

theorem tenSixCycleGraph_cross_right_left : ∀ (i : Fin 6) (j : Fin 10),
    ¬tenSixCycleGraph.Adj (Fin.natAdd 10 i) (Fin.castAdd 6 j) := by
  native_decide

/-- Two complementary cycle components of orders ten and six glue to the
exact certificate labeling `C₁₀ ⊔ C₆` on `Fin 16`. -/
theorem exists_tenSixComponentLabeling_of_two_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (a b : H.ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 10) (hb : b.supp.ncard = 6)
    (hcover : ∀ x : V, x ∈ a.supp ∨ x ∈ b.supp) :
    Nonempty (TenSixComponentLabeling H) := by
  classical
  have hbcompl : b.supp = a.suppᶜ := by
    ext x
    constructor
    · intro hxb hxa
      exact hab (ConnectedComponent.eq_of_common_vertex hxa hxb)
    · intro hxa
      rcases hcover x with hxa' | hxb
      · exact False.elim (hxa hxa')
      · exact hxb
  obtain ⟨ea, hea⟩ := exists_componentCycleEquiv H hdeg a 10 ha
  obtain ⟨eb, heb⟩ := exists_componentCycleEquiv H hdeg b 6 hb
  let ebc : Fin 6 ≃ (a.suppᶜ : Set V) :=
    eb.trans (Equiv.setCongr hbcompl)
  let split : V ≃ a.supp ⊕ (a.suppᶜ : Set V) :=
    (Equiv.Set.sumCompl a.supp).symm
  let coords : a.supp ⊕ (a.suppᶜ : Set V) ≃ Fin 10 ⊕ Fin 6 :=
    Equiv.sumCongr ea.symm ebc.symm
  let θ : V ≃ Fin 16 :=
    split.trans (coords.trans finSumFinEquiv)
  have hθleft (x : V) (hx : x ∈ a.supp) :
      θ x = Fin.castAdd 6 (ea.symm ⟨x, hx⟩) := by
    change finSumFinEquiv (coords (split x)) = _
    rw [show split x = Sum.inl ⟨x, hx⟩ by
      exact Equiv.Set.sumCompl_symm_apply_of_mem hx]
    rfl
  have hθright (x : V) (hx : x ∉ a.supp) :
      θ x = Fin.natAdd 10 (ebc.symm ⟨x, hx⟩) := by
    change finSumFinEquiv (coords (split x)) = _
    rw [show split x = Sum.inr ⟨x, hx⟩ by
      exact Equiv.Set.sumCompl_symm_apply_of_notMem hx]
    rfl
  refine ⟨⟨θ, ?_⟩⟩
  intro u v
  by_cases hu : u ∈ a.supp <;> by_cases hv : v ∈ a.supp
  · let i := ea.symm ⟨u, hu⟩
    let j := ea.symm ⟨v, hv⟩
    have hcycle : H.Adj u v ↔ (cycleGraph 10).Adj i j := by
      simpa [i, j] using (hea i j).symm
    have hfixed : (cycleGraph 10).Adj i j ↔
        tenSixCycleGraph.Adj (Fin.castAdd 6 i) (Fin.castAdd 6 j) :=
      (tenSixCycleGraph_left i j).symm
    have hθu : θ u = Fin.castAdd 6 i := by
      exact hθleft u hu
    have hθv : θ v = Fin.castAdd 6 j := by
      exact hθleft v hv
    rw [hθu, hθv]
    exact hcycle.trans hfixed
  · constructor
    · intro huv
      exact False.elim (hv ((ConnectedComponent.mem_supp_congr_adj a huv).mp hu))
    · intro hθ
      let i := ea.symm ⟨u, hu⟩
      let j := ebc.symm ⟨v, hv⟩
      have hθu : θ u = Fin.castAdd 6 i := by
        exact hθleft u hu
      have hθv : θ v = Fin.natAdd 10 j := by
        exact hθright v hv
      rw [hθu, hθv] at hθ
      exact False.elim (tenSixCycleGraph_cross_left_right i j hθ)
  · constructor
    · intro huv
      exact False.elim (hu ((ConnectedComponent.mem_supp_congr_adj a huv).mpr hv))
    · intro hθ
      let i := ebc.symm ⟨u, hu⟩
      let j := ea.symm ⟨v, hv⟩
      have hθu : θ u = Fin.natAdd 10 i := by
        exact hθright u hu
      have hθv : θ v = Fin.castAdd 6 j := by
        exact hθleft v hv
      rw [hθu, hθv] at hθ
      exact False.elim (tenSixCycleGraph_cross_right_left i j hθ)
  · let i := ebc.symm ⟨u, hu⟩
    let j := ebc.symm ⟨v, hv⟩
    have hi : (eb i).1 = u := by
      exact congrArg Subtype.val (ebc.apply_symm_apply ⟨u, hu⟩)
    have hj : (eb j).1 = v := by
      exact congrArg Subtype.val (ebc.apply_symm_apply ⟨v, hv⟩)
    have hcycle : H.Adj u v ↔ (cycleGraph 6).Adj i j := by
      rw [← hi, ← hj]
      exact (heb i j).symm
    have hfixed : (cycleGraph 6).Adj i j ↔
        tenSixCycleGraph.Adj (Fin.natAdd 10 i) (Fin.natAdd 10 j) :=
      (tenSixCycleGraph_right i j).symm
    have hθu : θ u = Fin.natAdd 10 i := by
      exact hθright u hu
    have hθv : θ v = Fin.natAdd 10 j := by
      exact hθright v hv
    rw [hθu, hθv]
    exact hcycle.trans hfixed

end

end Erdos85
