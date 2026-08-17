import Proofs.Erdos85OrderSixtyFourOutsideBlockOperator

/-! # Pointwise capacity of the outside return operator -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For fixed vertices `u,v`, each neighbor `x` of `u` contributes at most
one length-three walk `u-x-y-v` in a `C₄`-free graph: two choices of `y`
would be two common neighbors of the distinct vertices `x,v`. -/
theorem outsideReturn_walkCount_le_outsideNeighborCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V) [DecidablePred (· ∈ s)]
    (u v : s) :
    (∑ x : {x : V // x ∉ s},
        if G.Adj u.1 x.1 then
          (Finset.univ.filter fun y : {y : V // y ∉ s} ↦
            G.Adj x.1 y.1 ∧ G.Adj y.1 v.1).card
        else 0) ≤
      ((G.neighborFinset u.1).filter fun x ↦ x ∉ s).card := by
  classical
  let X : Finset {x : V // x ∉ s} :=
    Finset.univ.filter fun x ↦ G.Adj u.1 x.1
  have hXcard : X.card =
      ((G.neighborFinset u.1).filter fun x ↦ x ∉ s).card := by
    let ι : {x : V // x ∉ s} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : X.map ι =
        (G.neighborFinset u.1).filter fun x ↦ x ∉ s := by
      ext x
      simp [X, ι]
    rw [← hmap, Finset.card_map]
  rw [← hXcard]
  calc
    (∑ x : {x : V // x ∉ s},
        if G.Adj u.1 x.1 then
          (Finset.univ.filter fun y : {y : V // y ∉ s} ↦
            G.Adj x.1 y.1 ∧ G.Adj y.1 v.1).card
        else 0) =
        ∑ x ∈ X,
          (Finset.univ.filter fun y : {y : V // y ∉ s} ↦
            G.Adj x.1 y.1 ∧ G.Adj y.1 v.1).card := by
          rw [← Finset.sum_filter]
    _ ≤ ∑ _x ∈ X, 1 := by
      apply Finset.sum_le_sum
      intro x hx
      have hxv : x.1 ≠ v.1 := fun h ↦ x.2 (h ▸ v.2)
      let Y : Finset {y : V // y ∉ s} :=
        Finset.univ.filter fun y ↦ G.Adj x.1 y.1 ∧ G.Adj y.1 v.1
      have hYmap : (Y.map
          (⟨Subtype.val, Subtype.val_injective⟩ : {y : V // y ∉ s} ↪ V)) ⊆
          G.neighborFinset x.1 ∩ G.neighborFinset v.1 := by
        intro y hy
        rcases Finset.mem_map.mp hy with ⟨z, hz, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Y] at hz
        simp [hz.1, hz.2.symm]
      have hcommon := common_le_one_of_not_containsC4 hfree x.1 v.1 hxv
      change Y.card ≤ 1
      rw [← Finset.card_map
        (⟨Subtype.val, Subtype.val_injective⟩ : {y : V // y ∉ s} ↪ V)]
      exact (Finset.card_le_card hYmap).trans hcommon
    _ = X.card := by simp

/-- Every entry of `B C Bᴴ` is a natural number bounded by the number of
outside neighbors of its row vertex.  In the order-64 H16 block that number
is six, so the return operator has entries in `{0,1,…,6}`. -/
theorem outsideReturn_apply_eq_nat_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V) [DecidablePred (· ∈ s)]
    (u v : s) :
    let p : V → Prop := fun x ↦ x ∈ s
    let q : Set V := {x | ¬p x}
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
    let C := (G.induce q).adjMatrix ℂ
    ∃ n : ℕ,
      n ≤ ((G.neighborFinset u.1).filter fun x ↦ x ∉ s).card ∧
      ((B * C) * Matrix.conjTranspose B) u v = n := by
  classical
  let p : V → Prop := fun x ↦ x ∈ s
  let q : Set V := {x | ¬p x}
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := (G.induce q).adjMatrix ℂ
  let n : ℕ := ∑ x : q,
    if G.Adj u.1 x.1 then
      (Finset.univ.filter fun y : q ↦
        G.Adj x.1 y.1 ∧ G.Adj y.1 v.1).card
    else 0
  refine ⟨n, ?_, ?_⟩
  · exact outsideReturn_walkCount_le_outsideNeighborCount G hfree s u v
  · rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.toBlock_apply,
      SimpleGraph.adjMatrix_apply, Matrix.conjTranspose_apply,
      Complex.star_def]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [n]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hux : G.Adj u.1 x.1
    · simp only [hux, if_true, one_mul]
      rw [← Finset.sum_boole (R := ℂ)
        (fun y : q ↦ G.Adj x.1 y.1 ∧ G.Adj y.1 v.1) Finset.univ]
      apply Finset.sum_congr rfl
      intro y _
      change ((if G.Adj x.1 y.1 then 1 else 0) *
          (starRingEnd ℂ) (if G.Adj v.1 y.1 then 1 else 0)) =
        if G.Adj x.1 y.1 ∧ G.Adj y.1 v.1 then 1 else 0
      by_cases hxy : G.Adj x.1 y.1 <;>
        by_cases hyv : G.Adj y.1 v.1 <;>
        simp [G.adj_comm, hxy]
    · simp [hux]

/-- A diagonal entry of `B C Bᴴ` is even: it counts both orientations of
each edge of the outside graph induced on the outside neighbors of `u`. -/
theorem outsideReturn_diag_eq_twice_nat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] (u : s) :
    let p : V → Prop := fun x ↦ x ∈ s
    let q : Set V := {x | ¬p x}
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
    let C := (G.induce q).adjMatrix ℂ
    ∃ k : ℕ, ((B * C) * Matrix.conjTranspose B) u u = (2 * k : ℕ) := by
  classical
  let p : V → Prop := fun x ↦ x ∈ s
  let q : Set V := {x | ¬p x}
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := (G.induce q).adjMatrix ℂ
  let T : Set q := {x | G.Adj u.1 x.1}
  let K : SimpleGraph T := (G.induce q).induce T
  let n : ℕ := ∑ x : q,
    if G.Adj u.1 x.1 then
      (Finset.univ.filter fun y : q ↦
        G.Adj x.1 y.1 ∧ G.Adj y.1 u.1).card
    else 0
  have hentry : ((B * C) * Matrix.conjTranspose B) u u = n := by
    rw [Matrix.mul_apply]
    simp only [B, C, Matrix.mul_apply, Matrix.toBlock_apply,
      SimpleGraph.adjMatrix_apply, Matrix.conjTranspose_apply,
      Complex.star_def]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [n]
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hux : G.Adj u.1 x.1
    · simp only [hux, if_true, one_mul]
      rw [← Finset.sum_boole (R := ℂ)
        (fun y : q ↦ G.Adj x.1 y.1 ∧ G.Adj y.1 u.1) Finset.univ]
      apply Finset.sum_congr rfl
      intro y _
      change ((if G.Adj x.1 y.1 then 1 else 0) *
          (starRingEnd ℂ) (if G.Adj u.1 y.1 then 1 else 0)) =
        if G.Adj x.1 y.1 ∧ G.Adj y.1 u.1 then 1 else 0
      by_cases hxy : G.Adj x.1 y.1 <;>
        by_cases huy : G.Adj u.1 y.1 <;>
        simp [G.adj_comm, hxy]
    · simp [hux]
  have hn : n = ∑ z : T, K.degree z := by
    change n = ∑ z : {x : q // G.Adj u.1 x.1}, K.degree z
    simp only [n]
    rw [← Finset.sum_filter]
    rw [Finset.sum_subtype
      (Finset.univ.filter fun x : q ↦ G.Adj u.1 x.1)
      (p := fun x : q ↦ G.Adj u.1 x.1) (by intro x; simp)]
    apply Finset.sum_congr rfl
    intro z _
    let ι : {x : q // G.Adj u.1 x.1} ↪ q :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : (K.neighborFinset z).map ι =
        Finset.univ.filter (fun x : q ↦
          G.Adj z.1.1 x.1 ∧ G.Adj x.1 u.1) := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, hyx⟩
        have hzy := (K.mem_neighborFinset z y).mp hy
        change G.Adj z.1.1 y.1.1 at hzy
        subst x
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzy, y.2.symm⟩
      · intro hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        let y : {x : q // G.Adj u.1 x.1} := ⟨x, hx.2.symm⟩
        apply Finset.mem_map.mpr
        refine ⟨y, ?_, rfl⟩
        apply (K.mem_neighborFinset z y).mpr
        change G.Adj z.1.1 y.1.1
        exact hx.1
    rw [← K.card_neighborFinset_eq_degree, ← hmap, Finset.card_map]
    rfl
  refine ⟨K.edgeFinset.card, ?_⟩
  rw [hentry, hn, K.sum_degrees_eq_twice_card_edges]


/-- In the actual seven-component order-64 branch, every entry of the H16
outside-return operator is the cast of a natural number at most six. -/
theorem orderSixtyFour_seven_components_outsideReturn_apply_eq_nat_le_six
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let q : Set (Fin 64) := {x | ¬p x}
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      ∀ u v : c.supp, ∃ n : ℕ, n ≤ 6 ∧
        ((B * C) * Matrix.conjTranspose B) u v = n := by
  classical
  obtain ⟨c, hc16, htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  dsimp only
  intro u v
  obtain ⟨n, hn, hentry⟩ :=
    outsideReturn_apply_eq_nat_le G hfree c.supp u v
  refine ⟨n, ?_, hentry⟩
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  let inside := (G.neighborFinset u.1).filter fun x ↦ x ∈ c.supp
  let outside := (G.neighborFinset u.1).filter fun x ↦ x ∉ c.supp
  have hins : inside.card = 2 := by
    have hu := htwo u.1
    change ((G.neighborFinset u.1).filter fun y ↦
      (secondOrderDefectGraph G).connectedComponentMk y = c).card = 2 at hu
    have heq : inside = (G.neighborFinset u.1).filter fun y ↦
        (secondOrderDefectGraph G).connectedComponentMk y = c := by
      ext y
      simp [inside, SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [heq, hu]
  have hsplit : inside.card + outside.card = G.degree u.1 := by
    simpa [inside, outside, G.card_neighborFinset_eq_degree] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset u.1) (fun x ↦ x ∈ c.supp))
  have hout : outside.card = 6 := by
    rw [hins, hreg u.1] at hsplit
    omega
  change n ≤ outside.card at hn
  omega

end

end Erdos85
