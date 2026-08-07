import Proofs.Erdos85SecondOrderColorTrace
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The component quotient of the even second-order defect graph

Commutation with a regular defect graph makes its connected-component
partition equitable for the original graph.  This module develops the
linear-algebraic bridge needed for the finite degree-six quotient argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def componentNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) (x : V) : Finset V :=
  (G.neighborFinset x).filter fun y => D.connectedComponentMk y = c

def componentIndicator
    {V : Type*} (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) : V → ℝ :=
  fun x => if D.connectedComponentMk x = c then 1 else 0

noncomputable def componentRepresentative
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent) : V :=
  Classical.choose c.nonempty_supp

theorem componentRepresentative_mem
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent) :
    componentRepresentative D c ∈ c.supp :=
  Classical.choose_spec c.nonempty_supp

/-- The integral component quotient: row `c`, column `e` counts neighbors in
`e` of one representative vertex of `c`.  Equitability below shows that the
choice of representative is immaterial. -/
noncomputable def componentQuotientMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent] :
    Matrix D.ConnectedComponent D.ConnectedComponent ℕ :=
  fun c e =>
    (componentNeighborFinset G D e (componentRepresentative D c)).card

def componentMembershipMatrix
    {V : Type*} (D : SimpleGraph V) [DecidableEq D.ConnectedComponent] :
    Matrix V D.ConnectedComponent ℝ :=
  fun x c => if D.connectedComponentMk x = c then 1 else 0

def realOnesMatrix (V : Type*) : Matrix V V ℝ := fun _ _ => 1

noncomputable def componentQuotientMatrixReal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent] :
    Matrix D.ConnectedComponent D.ConnectedComponent ℝ :=
  fun c e => componentQuotientMatrix G D c e

/-- The indicator of a component is a top-eigenvector of the adjacency
matrix of a regular graph. -/
theorem adjMatrix_mulVec_componentIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k)
    (c : D.ConnectedComponent) :
    (D.adjMatrix ℝ).mulVec (componentIndicator D c) =
      (k : ℝ) • componentIndicator D c := by
  funext x
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hconst : ∀ y ∈ D.neighborFinset x,
      componentIndicator D c y = componentIndicator D c x := by
    intro y hy
    have hxy : D.Adj x y := (D.mem_neighborFinset x y).mp hy
    have hcomp := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
    simp only [componentIndicator]
    rw [hcomp]
  calc
    (∑ y ∈ D.neighborFinset x, componentIndicator D c y) =
        ∑ _y ∈ D.neighborFinset x, componentIndicator D c x := by
      apply Finset.sum_congr rfl
      intro y hy
      exact hconst y hy
    _ = (D.degree x : ℝ) * componentIndicator D c x := by
      rw [Finset.sum_const, D.card_neighborFinset_eq_degree]
      simp
    _ = ((k : ℝ) • componentIndicator D c) x := by
      rw [hreg]
      simp

/-- If `G` commutes with a regular graph `D`, then every vertex in a fixed
component of `D` has the same number of `G`-neighbors in every other fixed
component. -/
theorem componentNeighborFinset_card_eq_of_adjMatrix_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    (c e : D.ConnectedComponent) {x x' : V}
    (hx : x ∈ c.supp) (hx' : x' ∈ c.supp) :
    (componentNeighborFinset G D e x).card =
      (componentNeighborFinset G D e x').card := by
  let v := componentIndicator D e
  let f := (G.adjMatrix ℝ).mulVec v
  have hDv : (D.adjMatrix ℝ).mulVec v = (k : ℝ) • v :=
    adjMatrix_mulVec_componentIndicator D k hreg e
  have hDf : (D.adjMatrix ℝ).mulVec f = (k : ℝ) • f := by
    change (D.adjMatrix ℝ).mulVec ((G.adjMatrix ℝ).mulVec v) = _
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hDv,
      Matrix.mulVec_smul]
  have hlap : (D.lapMatrix ℝ).mulVec f = 0 := by
    funext y
    rw [D.lapMatrix_mulVec_apply]
    rw [hreg]
    have hsum : ∑ z ∈ D.neighborFinset y, f z =
        ((D.adjMatrix ℝ).mulVec f) y := by
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [hsum, hDf]
    simp
  have hreach : D.Reachable x x' := by
    apply SimpleGraph.ConnectedComponent.exact
    exact hx.trans hx'.symm
  have hfx : f x = f x' :=
    (D.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hlap) x x' hreach
  have hcount : ∀ y : V,
      f y = ((componentNeighborFinset G D e y).card : ℝ) := by
    intro y
    rw [show f y = ((G.adjMatrix ℝ).mulVec v) y by rfl,
      SimpleGraph.adjMatrix_mulVec_apply]
    simp only [v, componentIndicator, componentNeighborFinset]
    rw [← Finset.sum_filter]
    simp
  rw [hcount x, hcount x'] at hfx
  exact_mod_cast hfx

theorem componentQuotientMatrix_apply_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    (c e : D.ConnectedComponent) {x : V} (hx : x ∈ c.supp) :
    componentQuotientMatrix G D c e =
      (componentNeighborFinset G D e x).card := by
  apply componentNeighborFinset_card_eq_of_adjMatrix_comm
    G D k hreg hcomm c e
  · exact componentRepresentative_mem D c
  · exact hx

/-- Detailed balance for an equitable component quotient: the number of
vertices in one component times its quotient entry toward another component
is symmetric in the two components. -/
theorem componentQuotientMatrix_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ)
    (c e : D.ConnectedComponent) :
    c.supp.ncard * componentQuotientMatrix G D c e =
      e.supp.ncard * componentQuotientMatrix G D e c := by
  have hcfin : c.supp.Finite := Set.toFinite c.supp
  have hefin : e.supp.Finite := Set.toFinite e.supp
  let cs : Finset V := hcfin.toFinset
  let es : Finset V := hefin.toFinset
  have hcardc : cs.card = c.supp.ncard := by
    exact (Set.ncard_eq_toFinset_card c.supp hcfin).symm
  have hcarde : es.card = e.supp.ncard := by
    exact (Set.ncard_eq_toFinset_card e.supp hefin).symm
  have hce (x : V) (hx : x ∈ cs) :
      (es.bipartiteAbove G.Adj x).card =
        componentQuotientMatrix G D c e := by
    have hxc : x ∈ c.supp := by simpa [cs] using hx
    rw [componentQuotientMatrix_apply_eq G D k hreg hcomm c e hxc]
    congr 1
    ext y
    simp [es, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
      SimpleGraph.ConnectedComponent.mem_supp_iff, and_comm]
  have hec (y : V) (hy : y ∈ es) :
      (cs.bipartiteBelow G.Adj y).card =
        componentQuotientMatrix G D e c := by
    have hye : y ∈ e.supp := by simpa [es] using hy
    rw [componentQuotientMatrix_apply_eq G D k hreg hcomm e c hye]
    congr 1
    ext x
    simp [cs, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
      SimpleGraph.ConnectedComponent.mem_supp_iff, G.adj_comm, and_comm]
  calc
    c.supp.ncard * componentQuotientMatrix G D c e =
        cs.card * componentQuotientMatrix G D c e := by rw [hcardc]
    _ = ∑ x ∈ cs, componentQuotientMatrix G D c e := by simp
    _ = ∑ x ∈ cs, (es.bipartiteAbove G.Adj x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hce x hx]
    _ = ∑ y ∈ es, (cs.bipartiteBelow G.Adj y).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow G.Adj
    _ = ∑ y ∈ es, componentQuotientMatrix G D e c := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hec y hy]
    _ = es.card * componentQuotientMatrix G D e c := by simp
    _ = e.supp.ncard * componentQuotientMatrix G D e c := by rw [hcarde]

/-- Matrix form of equitability: the original adjacency operator maps a
component indicator according to the integral component quotient. -/
theorem adjMatrix_mul_componentMembershipMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k)
    (hcomm : G.adjMatrix ℝ * D.adjMatrix ℝ =
      D.adjMatrix ℝ * G.adjMatrix ℝ) :
    G.adjMatrix ℝ * componentMembershipMatrix D =
      componentMembershipMatrix D * componentQuotientMatrixReal G D := by
  ext x e
  have hx : x ∈ (D.connectedComponentMk x).supp := rfl
  have hQ := componentQuotientMatrix_apply_eq
    G D k hreg hcomm (D.connectedComponentMk x) e hx
  simp only [Matrix.mul_apply, componentMembershipMatrix,
    componentQuotientMatrixReal]
  calc
    (∑ y, G.adjMatrix ℝ x y *
        (if D.connectedComponentMk y = e then 1 else 0)) =
        ((componentNeighborFinset G D e x).card : ℝ) := by
      simp only [SimpleGraph.adjMatrix_apply, componentNeighborFinset]
      calc
        (∑ y, (if G.Adj x y then (1 : ℝ) else 0) *
            if D.connectedComponentMk y = e then 1 else 0) =
            ∑ y : V, if G.Adj x y ∧ D.connectedComponentMk y = e
              then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro y _
          by_cases hxy : G.Adj x y <;>
            by_cases hy : D.connectedComponentMk y = e <;> simp [hxy, hy]
        _ = (((Finset.univ : Finset V).filter fun y =>
            G.Adj x y ∧ D.connectedComponentMk y = e).card : ℝ) := by
          simp
        _ = (((G.neighborFinset x).filter fun y =>
            D.connectedComponentMk y = e).card : ℝ) := by
          congr 2
          ext y
          simp [SimpleGraph.mem_neighborFinset]
    _ = (componentQuotientMatrix G D (D.connectedComponentMk x) e : ℝ) := by
      exact_mod_cast hQ.symm
    _ = ∑ z, (if D.connectedComponentMk x = z then 1 else 0) *
        (componentQuotientMatrix G D z e : ℝ) := by
      simp

/-- A regular graph acts by its degree on the component-membership matrix. -/
theorem adjMatrix_mul_componentMembershipMatrix_self
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (k : ℕ) (hreg : ∀ x : V, D.degree x = k) :
    D.adjMatrix ℝ * componentMembershipMatrix D =
      (k : ℝ) • componentMembershipMatrix D := by
  ext x c
  have h := congrFun
    (adjMatrix_mulVec_componentIndicator D k hreg c) x
  change (D.adjMatrix ℝ).mulVec (componentIndicator D c) x =
    ((k : ℝ) • componentIndicator D c) x
  exact h

/-- Multiplying component membership by the all-ones matrix records component
orders. -/
theorem onesMatrix_mul_componentMembershipMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent] :
    realOnesMatrix V * componentMembershipMatrix D =
      fun _ (c : D.ConnectedComponent) => (c.supp.ncard : ℝ) := by
  ext x c
  simp only [Matrix.mul_apply, realOnesMatrix, one_mul,
    componentMembershipMatrix]
  rw [Finset.sum_boole]
  norm_cast
  have hs : c.supp.Finite := Set.toFinite c.supp
  have hfinset : ({y | D.connectedComponentMk y = c} : Finset V) =
      hs.toFinset := by
    ext y
    simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
  rw [hfinset, Set.ncard_eq_toFinset_card c.supp hs]

/-- Every quotient row sums to the degree of its representative. -/
theorem sum_componentQuotientMatrix_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    (∑ e : D.ConnectedComponent, componentQuotientMatrix G D c e) =
      G.degree (componentRepresentative D c) := by
  rw [← G.card_neighborFinset_eq_degree]
  simp only [componentQuotientMatrix, componentNeighborFinset]
  calc
    (∑ e : D.ConnectedComponent,
        ((G.neighborFinset (componentRepresentative D c)).filter fun y =>
          D.connectedComponentMk y = e).card) =
        ∑ e : D.ConnectedComponent,
          ∑ y ∈ G.neighborFinset (componentRepresentative D c),
            if D.connectedComponentMk y = e then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.card_filter]
    _ = ∑ y ∈ G.neighborFinset (componentRepresentative D c),
          ∑ e : D.ConnectedComponent,
            if D.connectedComponentMk y = e then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = (G.neighborFinset (componentRepresentative D c)).card := by
      simp

/-- Real form of the integral commutation theorem, used by the Laplacian
argument above. -/
theorem adjMatrix_comm_secondOrderDefect_of_even_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    G.adjMatrix ℝ * (secondOrderDefectGraph G).adjMatrix ℝ =
      (secondOrderDefectGraph G).adjMatrix ℝ * G.adjMatrix ℝ := by
  have hz := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  ext x y
  have hxy := congrFun (congrFun hz x) y
  simp only [Matrix.mul_apply] at hxy ⊢
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hxy
  push_cast at hc
  simpa [SimpleGraph.adjMatrix_apply] using hc

/-- Real form of the even second-order matrix equation. -/
theorem adjMatrix_sq_eq_sub_secondOrderDefect_of_even_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    G.adjMatrix ℝ * G.adjMatrix ℝ =
      (↑d - 1 : ℝ) • (1 : Matrix V V ℝ) +
        realOnesMatrix V -
          (secondOrderDefectGraph G).adjMatrix ℝ := by
  have hz := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  ext x y
  have hxy := congrFun (congrFun hz x) y
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply] at hxy ⊢
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hxy
  push_cast at hc
  simpa [SimpleGraph.adjMatrix_apply,
    FriendshipTheoremOQ01.onesMatrix, realOnesMatrix] using hc

/-- The connected components of the even second-order defect two-factor form
an equitable partition for the original graph. -/
theorem secondOrder_componentNeighborFinset_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) {x x' : V}
    (hx : x ∈ c.supp) (hx' : x' ∈ c.supp) :
    (componentNeighborFinset G (secondOrderDefectGraph G) e x).card =
      (componentNeighborFinset G (secondOrderDefectGraph G) e x').card := by
  apply componentNeighborFinset_card_eq_of_adjMatrix_comm
    G (secondOrderDefectGraph G) 2
  · exact secondOrderDefectGraph_degree_eq_two
      G hfree hd heven hmin hcard
  · exact adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard
  · exact hx
  · exact hx'

/-- The second-order component quotient has constant row sum `d`. -/
theorem sum_secondOrder_componentQuotientMatrix_row_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ e, componentQuotientMatrix G (secondOrderDefectGraph G) c e) = d := by
  rw [sum_componentQuotientMatrix_row]
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, d = a + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  exact regular_of_minDegree_card_lt_nextMooreLayer
    G hfree (by omega) hmin hbelow _

/-- Detailed balance for the even second-order component quotient. -/
theorem secondOrder_componentQuotientMatrix_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    c.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) c e =
      e.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c := by
  apply componentQuotientMatrix_balance
    G (secondOrderDefectGraph G) 2
  · exact secondOrderDefectGraph_degree_eq_two
      G hfree hd heven hmin hcard
  · exact adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard

/-- The quotient of the even second-order defect partition satisfies the
Moore-type square equation `Q² = (d - 3)I + 1 rᵀ`, where `r_e` is the
order of component `e`. -/
theorem secondOrder_componentQuotientMatrixReal_sq_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentQuotientMatrixReal G (secondOrderDefectGraph G) *
        componentQuotientMatrixReal G (secondOrderDefectGraph G)) c e =
      (d - 3 : ℝ) * (if c = e then 1 else 0) + (e.supp.ncard : ℝ) := by
  let D := secondOrderDefectGraph G
  let S := componentMembershipMatrix D
  let Q := componentQuotientMatrixReal G D
  let R : Matrix V D.ConnectedComponent ℝ :=
    fun _ a => (a.supp.ncard : ℝ)
  have hAS : G.adjMatrix ℝ * S = S * Q :=
    adjMatrix_mul_componentMembershipMatrix G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real
        G hfree hd heven hmin hcard)
  have hDS : D.adjMatrix ℝ * S = (2 : ℝ) • S :=
    adjMatrix_mul_componentMembershipMatrix_self D 2
      (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
  have hJS : realOnesMatrix V * S = R :=
    onesMatrix_mul_componentMembershipMatrix D
  have hsq : G.adjMatrix ℝ * G.adjMatrix ℝ =
      (d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
        D.adjMatrix ℝ :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard
  have htransport :
      S * (Q * Q) =
        ((d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
          D.adjMatrix ℝ) * S := by
    calc
      S * (Q * Q) = (S * Q) * Q := (Matrix.mul_assoc S Q Q).symm
      _ = (G.adjMatrix ℝ * S) * Q := by rw [hAS]
      _ = G.adjMatrix ℝ * (S * Q) := Matrix.mul_assoc _ _ _
      _ = G.adjMatrix ℝ * (G.adjMatrix ℝ * S) := by rw [hAS]
      _ = (G.adjMatrix ℝ * G.adjMatrix ℝ) * S :=
        (Matrix.mul_assoc _ _ _).symm
      _ = ((d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
          D.adjMatrix ℝ) * S := by rw [hsq]
  have htransport' : S * (Q * Q) =
      (d - 1 : ℝ) • S + R - (2 : ℝ) • S := by
    calc
      S * (Q * Q) =
          ((d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
            D.adjMatrix ℝ) * S := htransport
      _ = (d - 1 : ℝ) • S + R - (2 : ℝ) • S := by
        rw [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
          hJS, hDS]
  have hentry := congrFun (congrFun htransport'
    (componentRepresentative D c)) e
  have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c
      (componentRepresentative D c)).mp
      (componentRepresentative_mem D c)
  simp [Matrix.mul_apply, S, Q, R, componentMembershipMatrix, hrep] at hentry ⊢
  by_cases hce : c = e
  · simp [hce] at hentry ⊢
    linarith
  · simp [hce] at hentry ⊢
    simpa [D] using hentry

/-- Integral form of the quotient square equation, suitable for finite
classification. -/
theorem secondOrder_componentQuotientMatrix_sq_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentQuotientMatrix G (secondOrderDefectGraph G) *
        componentQuotientMatrix G (secondOrderDefectGraph G)) c e =
      (d - 3) * (if c = e then 1 else 0) + e.supp.ncard := by
  have hreal := secondOrder_componentQuotientMatrixReal_sq_apply
    G hfree hd heven hmin hcard c e
  simp only [Matrix.mul_apply, componentQuotientMatrixReal] at hreal ⊢
  have hcast : ((d - 3 : ℕ) : ℝ) = (d : ℝ) - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ d)]
    norm_num
  rw [← hcast] at hreal
  exact_mod_cast hreal

end

end Erdos85
