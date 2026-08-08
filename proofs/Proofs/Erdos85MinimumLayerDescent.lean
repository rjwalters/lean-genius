import Proofs.Erdos85MinimumLayerDesignTerminal
import Proofs.Erdos85MinimumLayerUniversalTerminal

/-!
# Descent to the minimum defect layer

The vertices in the minimum-order defect components, with the adjacency
inherited from the ambient graph, form a smaller exact-boundary graph.  We
use a sigma type to retain the component partition explicitly.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

abbrev minimumLayerComponent {V : Type*} (D : SimpleGraph V)
    (c₀ : D.ConnectedComponent) :=
  {c : D.ConnectedComponent // c.supp.ncard = c₀.supp.ncard}

def minimumLayerVertex {V : Type*} (D : SimpleGraph V)
    (c₀ : D.ConnectedComponent) :=
  Σ c : minimumLayerComponent D c₀, c.1.supp

noncomputable instance minimumLayerComponentFintype
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) :
    Fintype (minimumLayerComponent D c₀) := by
  unfold minimumLayerComponent
  infer_instance

noncomputable instance minimumLayerVertexFintype
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) :
    Fintype (minimumLayerVertex D c₀) := by
  unfold minimumLayerVertex
  letI (c : minimumLayerComponent D c₀) : Fintype c.1.supp :=
    Fintype.ofFinset c.1.supp.toFinite.toFinset (fun x ↦ by simp)
  infer_instance

def minimumLayerVertexValue {V : Type*} {D : SimpleGraph V}
    {c₀ : D.ConnectedComponent} : minimumLayerVertex D c₀ → V :=
  fun x ↦ x.2.1

def minimumLayerGraph {V : Type*} (G D : SimpleGraph V)
    (c₀ : D.ConnectedComponent) : SimpleGraph (minimumLayerVertex D c₀) :=
  G.comap minimumLayerVertexValue

noncomputable instance minimumLayerGraphDecidableRel
    {V : Type*} (G D : SimpleGraph V) [DecidableRel G.Adj]
    (c₀ : D.ConnectedComponent) :
    DecidableRel (minimumLayerGraph G D c₀).Adj := Classical.decRel _

theorem minimumLayerVertexValue_injective
    {V : Type*} {D : SimpleGraph V} {c₀ : D.ConnectedComponent} :
    Function.Injective (minimumLayerVertexValue (D := D) (c₀ := c₀)) := by
  intro x y hxy
  have hxc : D.connectedComponentMk x.2.1 = x.1.1 :=
    (ConnectedComponent.mem_supp_iff x.1.1 x.2.1).mp x.2.2
  have hyc : D.connectedComponentMk y.2.1 = y.1.1 :=
    (ConnectedComponent.mem_supp_iff y.1.1 y.2.1).mp y.2.2
  have hc : x.1.1 = y.1.1 := hxc.symm.trans ((congrArg D.connectedComponentMk hxy).trans hyc)
  have hcsub : x.1 = y.1 := Subtype.ext hc
  cases x with
  | mk xc xv =>
    cases y with
    | mk yc yv =>
      dsimp at hcsub hxy ⊢
      subst yc
      congr
      exact Subtype.ext hxy

/-- The minimum-layer graph inherits `C₄`-freeness. -/
theorem minimumLayerGraph_c4Free
    {V : Type*} (G D : SimpleGraph V) (c₀ : D.ConnectedComponent)
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 (minimumLayerVertex D c₀) (minimumLayerGraph G D c₀) := by
  intro h
  obtain ⟨f, hf, hadj⟩ := h
  apply hfree
  refine ⟨minimumLayerVertexValue ∘ f,
    (minimumLayerVertexValue_injective.comp hf), ?_⟩
  intro i j hij
  exact hadj i j hij

/-- The minimum layer has `u*w` vertices. -/
theorem card_minimumLayerVertex
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) :
    Fintype.card (minimumLayerVertex D c₀) =
      (Finset.univ.filter
        (fun c : D.ConnectedComponent ↦ c.supp.ncard = c₀.supp.ncard)).card *
        c₀.supp.ncard := by
  classical
  letI (c : minimumLayerComponent D c₀) : Fintype c.1.supp :=
    Fintype.ofFinset c.1.supp.toFinite.toFinset (fun x ↦ by simp)
  have hsize : ∀ c : minimumLayerComponent D c₀,
      Fintype.card c.1.supp = c₀.supp.ncard := by
    intro c
    calc
      Fintype.card c.1.supp = c.1.supp.toFinset.card := by
        exact Fintype.card_of_finset' _ (fun x ↦ by simp)
      _ = c.1.supp.ncard := (Set.ncard_eq_toFinset_card' c.1.supp).symm
      _ = c₀.supp.ncard := c.2
  have hcardComp : Fintype.card (minimumLayerComponent D c₀) =
      (Finset.univ.filter
        (fun c : D.ConnectedComponent ↦ c.supp.ncard = c₀.supp.ncard)).card := by
    exact Fintype.card_subtype
      (fun c : D.ConnectedComponent ↦ c.supp.ncard = c₀.supp.ncard)
  calc
    Fintype.card (minimumLayerVertex D c₀) =
        Fintype.card (Σ c : minimumLayerComponent D c₀, c.1.supp) :=
      Fintype.card_congr (Equiv.refl _)
    _ = ∑ c : minimumLayerComponent D c₀, Fintype.card c.1.supp :=
      Fintype.card_sigma
    _ = Fintype.card (minimumLayerComponent D c₀) * c₀.supp.ncard := by
      simp_rw [hsize]
      simp
    _ = _ := by rw [hcardComp]

def minimumLayerNeighborFiber
    {V : Type*} (G D : SimpleGraph V) (c₀ : D.ConnectedComponent)
    (x : minimumLayerVertex D c₀) (e : minimumLayerComponent D c₀) :=
  {y : e.1.supp // G.Adj x.2.1 y.1}

def minimumLayerNeighborEquiv
    {V : Type*} (G D : SimpleGraph V) (c₀ : D.ConnectedComponent)
    (x : minimumLayerVertex D c₀) :
    (minimumLayerGraph G D c₀).neighborSet x ≃
      Σ e : minimumLayerComponent D c₀,
        minimumLayerNeighborFiber G D c₀ x e where
  toFun y := ⟨y.1.1, ⟨y.1.2, y.2⟩⟩
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def minimumLayerNeighborFiberEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) (x : minimumLayerVertex D c₀)
    (e : minimumLayerComponent D c₀) :
    minimumLayerNeighborFiber G D c₀ x e ≃
      ↥(componentNeighborFinset G D e.1 x.2.1) where
  toFun y := ⟨y.1, Finset.mem_filter.mpr
    ⟨(G.mem_neighborFinset x.2.1 y.1).mpr y.2,
      (ConnectedComponent.mem_supp_iff e.1 y.1).mp y.1.2⟩⟩
  invFun y := ⟨⟨y.1,
    (ConnectedComponent.mem_supp_iff e.1 y.1).mpr
      (Finset.mem_filter.mp y.2).2⟩,
    (G.mem_neighborFinset x.2.1 y.1).mp (Finset.mem_filter.mp y.2).1⟩
  left_inv y := by cases y; rfl
  right_inv y := by cases y; rfl

/-- Degree in the minimum-layer graph is the corresponding restricted
quotient row sum. -/
theorem minimumLayerGraph_degree_eq_quotient_rowSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel D.Adj] [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ v : V, D.degree v = k)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    (c₀ : D.ConnectedComponent) (x : minimumLayerVertex D c₀) :
    (minimumLayerGraph G D c₀).degree x =
      ∑ e : minimumLayerComponent D c₀,
        componentQuotientMatrix G D x.1.1 e.1 := by
  classical
  letI (e : minimumLayerComponent D c₀) : Fintype e.1.supp :=
    Fintype.ofFinite _
  letI (e : minimumLayerComponent D c₀) :
      Fintype (minimumLayerNeighborFiber G D c₀ x e) :=
    Fintype.ofFinset
      (Finset.univ.filter (fun y : e.1.supp ↦ G.Adj x.2.1 y.1)) (fun y ↦ by
        change (y ∈ Finset.univ.filter
          (fun z : e.1.supp ↦ G.Adj x.2.1 z.1)) ↔ G.Adj x.2.1 y.1
        simp)
  rw [← (minimumLayerGraph G D c₀).card_neighborSet_eq_degree]
  rw [Fintype.card_congr (minimumLayerNeighborEquiv G D c₀ x),
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro e he
  calc
    Fintype.card (minimumLayerNeighborFiber G D c₀ x e) =
        (componentNeighborFinset G D e.1 x.2.1).card := by
      rw [Fintype.card_congr (minimumLayerNeighborFiberEquiv G D c₀ x e)]
      exact Fintype.card_coe _
    _ = componentQuotientMatrix G D x.1.1 e.1 :=
      (componentQuotientMatrix_apply_eq G D k hreg hcomm
        x.1.1 e.1 x.2.2).symm

/-- The minimum defect layer is itself regular, and its order satisfies the
same exact-boundary quadratic relation. -/
theorem secondOrder_minimumLayerGraph_regular_exact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) + s =
        s * s + 3 := by
  classical
  obtain ⟨s, hrows, hdesign⟩ :=
    secondOrder_minimumLayer_design_equation_nat
      G hfree hd heven hmin hcard c₀ hc₀min
  refine ⟨s, ?_, ?_⟩
  · intro x
    rw [minimumLayerGraph_degree_eq_quotient_rowSum
      G (secondOrderDefectGraph G) 2
      (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real
        G hfree hd heven hmin hcard) c₀ x]
    have hr := hrows x.1.1 x.1.2
    let M := Finset.univ.filter
      (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        c.supp.ncard = c₀.supp.ncard)
    rw [Finset.sum_subtype
      M
      (fun _ ↦ Iff.rfl)
      (fun e : (secondOrderDefectGraph G).ConnectedComponent ↦
        componentQuotientMatrix G (secondOrderDefectGraph G) x.1.1 e)] at hr
    let e : minimumLayerComponent (secondOrderDefectGraph G) c₀ ≃ ↥M :=
      { toFun := fun c ↦ ⟨c.1, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, c.2⟩⟩
        invFun := fun c ↦ ⟨c.1, (Finset.mem_filter.mp c.2).2⟩
        left_inv := by intro c; exact Subtype.ext rfl
        right_inv := by intro c; exact Subtype.ext rfl }
    have hsum :
        (∑ a : minimumLayerComponent (secondOrderDefectGraph G) c₀,
          componentQuotientMatrix G (secondOrderDefectGraph G) x.1.1 a.1) =
        ∑ a : ↥M,
          componentQuotientMatrix G (secondOrderDefectGraph G) x.1.1 a.1 := by
      apply Fintype.sum_equiv e
      intro a
      rfl
    exact hsum.trans hr
  · rw [card_minimumLayerVertex]
    omega

private theorem card_eq_boundary_of_card_add_degree
    (n s : ℕ) (h : n + s = s * s + 3) :
    n = s * (s - 1) + 3 := by
  cases s with
  | zero => simp_all
  | succ t =>
      simp only [Nat.succ_sub_one]
      nlinarith

/-- **Minimum-layer descent.**  At the even exact boundary, the union of the
smallest second-order defect components induces another exact-boundary
`C₄`-free regular graph.  Its degree is even, and away from the two
equal-cycle degrees `4` and `12` it is strictly smaller than the ambient
degree. -/
theorem secondOrder_minimumLayer_descent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      ¬ containsC4 (minimumLayerVertex (secondOrderDefectGraph G) c₀)
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 ∧
      Even s ∧
      (d ≠ 4 → d ≠ 12 → s < d) := by
  classical
  obtain ⟨s, hreg, hexact⟩ := secondOrder_minimumLayerGraph_regular_exact
    G hfree hd heven hmin hcard c₀ hc₀min
  let H := minimumLayerGraph G (secondOrderDefectGraph G) c₀
  let n := Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀)
  have hn : n = s * (s - 1) + 3 :=
    card_eq_boundary_of_card_add_degree n s hexact
  have hoddn : Odd n := by
    obtain ⟨q, hq⟩ := Nat.even_mul_pred_self s
    refine ⟨q + 1, ?_⟩
    rw [hn, hq]
    omega
  have hsum : (∑ x, H.degree x) = n * s := by
    change (∑ x,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x) = n * s
    calc
      _ = ∑ _x : minimumLayerVertex (secondOrderDefectGraph G) c₀, s := by
        apply Finset.sum_congr rfl
        intro x _
        exact hreg x
      _ = n * s := by simp [n]
  have hevenProd : Even (n * s) := by
    rw [← hsum, H.sum_degrees_eq_twice_card_edges]
    exact even_two_mul _
  have hsEven : Even s :=
    (Nat.even_mul.mp hevenProd).resolve_left
      (Nat.not_even_iff_odd.mpr hoddn)
  refine ⟨s, hreg,
    minimumLayerGraph_c4Free G (secondOrderDefectGraph G) c₀ hfree,
    hn, hsEven, ?_⟩
  intro hd4 hd12
  have hsmall := secondOrder_minimumLayer_totalOrder_le_of_degree_ne_four_twelve
    G hfree hd heven hmin hcard hd4 hd12 c₀ hc₀min
  have hnSmall : n ≤ 2 * d - 1 := by
    simpa [n, card_minimumLayerVertex] using hsmall
  by_contra hsd
  have hds : d ≤ s := Nat.le_of_not_gt hsd
  have hprod : d * (d - 1) ≤ s * (s - 1) :=
    Nat.mul_le_mul hds (Nat.sub_le_sub_right hds 1)
  have hdm1 : 3 ≤ d - 1 := by omega
  have hthree : 3 * d ≤ (d - 1) * d := Nat.mul_le_mul_right d hdm1
  have hthree' : 3 * d ≤ d * (d - 1) := by
    simpa [Nat.mul_comm] using hthree
  have hboundary : d * (d - 1) + 3 ≤ n := by
    rw [hn]
    omega
  omega

/-- At ambient degree six, the self-similar minimum layer can only have
degree zero or two.  Thus it is respectively an edgeless three-vertex graph
or a two-regular five-vertex graph. -/
theorem secondOrder_degree_six_minimumLayer_degree_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 6 * (6 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (s = 0 ∨ s = 2) ∧
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 := by
  classical
  obtain ⟨s, hreg, _hfreeLayer, hn, hsEven, _hslt⟩ :=
    secondOrder_minimumLayer_descent G hfree (d := 6)
      (by norm_num) (by norm_num) hmin hcard c₀ hc₀min
  have hsmall := secondOrder_minimumLayer_totalOrder_le_of_degree_ne_four_twelve
    G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard
      (by norm_num) (by norm_num) c₀ hc₀min
  have hnSmall :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) ≤ 11 := by
    simpa [card_minimumLayerVertex] using hsmall
  have hsltFour : s < 4 := by
    rw [hn] at hnSmall
    by_contra hs
    have h4s : 4 ≤ s := Nat.le_of_not_gt hs
    have hpred : 3 ≤ s - 1 := by omega
    have hprod : 12 ≤ s * (s - 1) := by
      calc
        12 = 4 * 3 := by norm_num
        _ ≤ s * (s - 1) := Nat.mul_le_mul h4s hpred
    omega
  obtain ⟨q, hq⟩ := hsEven
  refine ⟨s, ?_, hreg, hn⟩
  omega

end

end Erdos85
