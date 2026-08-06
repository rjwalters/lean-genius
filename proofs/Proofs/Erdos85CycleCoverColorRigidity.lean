import Proofs.Erdos85OddComponentClosure
import Proofs.Erdos85OrientedMassBounds

/-!
# Color rigidity of cyclic quotient covers

Every defect component is monochromatic: all its defect edges are either
original triangle-free edges or all are antipodal nonedges.  A quotient-one
cyclic cover cannot join two components of the first kind.  Indeed two
successive cover edges together with the corresponding two triangle-free
cycle edges are the rim of a `C₄`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A C4-free cycle diagonal block which contains all of its cycle edges
cannot take the reverse orientation.  Two reverse shifts of the edge
`0--1` produce the closing edge `2--(-1)`; this is either a loop (order
three) or closes the four-cycle `-1,0,1,2`. -/
theorem cycleBlock_forward_of_contains_cycle_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (hr : 3 ≤ r)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ZMod r → V) (hu : Function.Injective u)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huTri : ∀ x, G.Adj (u x) (u (x + 1)))
    (hfree : ¬ containsC4 V G) :
    ∀ x y : ZMod r,
    G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y)
    := by
  rcases graph_cycle_diagBlock_orientation hr G D hfree u hu hcomm huD with
      hfwd | hrev
  · intro x y
    exact adj_iff_of_adjMatrix_int_eq G (hfwd x y)
  · exfalso
    have hrevAdj : ∀ x y : ZMod r,
        G.Adj (u (x + 1)) (u (y - 1)) ↔ G.Adj (u x) (u y) := by
      intro x y
      exact adj_iff_of_adjMatrix_int_eq G (hrev x y)
    have hforced : G.Adj (u 2) (u (-1)) := by
      have h10 : G.Adj (u 1) (u 0) := by
        have h01 : G.Adj (u 0) (u 1) := by
          convert huTri 0 using 1 <;> norm_num
        convert (hrevAdj 0 1).mpr h01 using 1 <;> norm_num
      convert (hrevAdj 1 0).mpr h10 using 1 <;> norm_num
    by_cases heq : (2 : ZMod r) = -1
    · rw [heq] at hforced
      exact G.loopless.irrefl _ hforced
    · apply hfree
      have h01 : G.Adj (u 0) (u 1) := by simpa using huTri (0 : ZMod r)
      have h12 : G.Adj (u 1) (u 2) := by
        convert huTri (1 : ZMod r) using 1 <;> norm_num
      have hm10 : G.Adj (u (-1)) (u 0) := by
        simpa using huTri (-1 : ZMod r)
      have hne01 : u 0 ≠ u 1 := fun h ↦ by
        have hz := hu h
        haveI : Fact (1 < r) := ⟨by omega⟩
        exact (zero_ne_one : (0 : ZMod r) ≠ 1) hz
      have hne12 : u 1 ≠ u 2 := fun h ↦ by
        have hz := hu h
        have hone : (0 : ZMod r) = 1 := by linear_combination hz
        haveI : Fact (1 < r) := ⟨by omega⟩
        exact zero_ne_one hone
      have hnem10 : u (-1) ≠ u 0 := fun h ↦ by
        have hz := hu h
        have hone : (1 : ZMod r) = 0 := by
          have := congrArg Neg.neg hz
          simpa using this
        haveI : Fact (1 < r) := ⟨by omega⟩
        exact one_ne_zero hone
      exact containsC4_of_rim hm10 h01 h12 hforced
        (fun h ↦ zmod_sub_one_ne_add_one_of_three_le hr 0
          (by apply hu; simpa using h))
        (fun h ↦ by
          have hz := hu h
          have htwo : (2 : ZMod r) = 0 := hz.symm
          have hdvd : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp htwo
          have := Nat.le_of_dvd (by norm_num) hdvd
          omega)
        hnem10.symm hne01 (fun h ↦ heq (hu h)) hne12.symm

/-- A defect component whose cycle edges lie in the triangle-free color has
diagonal quotient entry exactly two.  Its rim supplies the two diagonal
neighbors, while color rigidity forces the diagonal block to be forward and
the parity-free Sidon bound supplies the matching upper bound. -/
theorem triangleFreeCycleComponent_diagonalQuotient_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) (hr : 3 ≤ r)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (hu : Function.Injective u)
    (huRange : Set.range u = c.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (huTri : ∀ x, G.Adj (u x) (u (x + 1))) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 := by
  let D := secondOrderDefectGraph G
  have hfwd := cycleBlock_forward_of_contains_cycle_edges hr G D u hu huD
    (adjMatrix_comm_secondOrderDefect_of_even G hfree hd heven hmin hcard)
    huTri hfree
  have hle := forwardComponent_diagonalQuotient_le_two G hfree hd heven
    hmin hcard c u hu huRange hfwd
  have hu0c : u 0 ∈ c.supp := by
    rw [← huRange]
    exact ⟨0, rfl⟩
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard) c c hu0c
  have hmAdj : G.Adj (u 0) (u (-1)) := by
    simpa using (huTri (-1 : ZMod r)).symm
  have hpAdj : G.Adj (u 0) (u 1) := by
    simpa using huTri (0 : ZMod r)
  have hmMem : u (-1) ∈ componentNeighborFinset G D c (u 0) := by
    have hmc : u (-1) ∈ c.supp := by
      rw [← huRange]
      exact ⟨-1, rfl⟩
    have hmk : D.connectedComponentMk (u (-1)) = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c (u (-1))).mp hmc
    simp [componentNeighborFinset, hmAdj, hmk]
  have hpMem : u 1 ∈ componentNeighborFinset G D c (u 0) := by
    have hpc : u 1 ∈ c.supp := by
      rw [← huRange]
      exact ⟨1, rfl⟩
    have hmk : D.connectedComponentMk (u 1) = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c (u 1)).mp hpc
    simp [componentNeighborFinset, hpAdj, hmk]
  have hne : u (-1) ≠ u 1 := by
    intro h
    exact zmod_sub_one_ne_add_one_of_three_le hr 0 (by
      apply hu
      simpa using h)
  have hsub : {u (-1), u 1} ⊆ componentNeighborFinset G D c (u 0) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hmMem
    · exact hpMem
  have hlower := Finset.card_le_card hsub
  rw [hQ] at hle
  rw [hQ]
  have hlower' : 2 ≤ (componentNeighborFinset G D c (u 0)).card := by
    simpa [hne] using hlower
  omega


/-- **No-cross-edge theorem.**  Two disjoint cyclic vertex sets whose cycle
edges are edges of `G` cannot have any cross edge when their cycle adjacency
operators are intertwined by a commuting defect graph.  A cross edge makes
both diagonal shifts forbidden by `C₄`-freeness, while the intertwining
recurrence says their sum contains the original edge. -/
theorem no_cross_edges_between_triangleFree_cycles
    {V : Type*} [Fintype V] [DecidableEq V]
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ZMod r → V) (v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hsep : ∀ x y, u x ≠ v y)
    (huD : ∀ x, D.neighborFinset (u x) = {u (x - 1), u (x + 1)})
    (hvD : ∀ y, D.neighborFinset (v y) = {v (y - 1), v (y + 1)})
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (huTri : ∀ x, G.Adj (u x) (u (x + 1)))
    (hvTri : ∀ y, G.Adj (v y) (v (y + 1)))
    (hfree : ¬ containsC4 V G) :
    ∀ x y, ¬ G.Adj (u x) (v y) := by
  have hupair : ∀ x, u (x - 1) ≠ u (x + 1) := fun x h ↦
    zmod_sub_one_ne_add_one_of_three_le hr x (hu h)
  have hvpair : ∀ y, v (y - 1) ≠ v (y + 1) := fun y h ↦
    zmod_sub_one_ne_add_one_of_three_le hn y (hv h)
  have hinter := entry_cycleIntertwine_of_adjMatrix_comm G D u v
    (1 : ZMod r) (1 : ZMod n) hcomm huD hvD hupair hvpair
  intro x y hxy
  have hplus : ¬ G.Adj (u (x + 1)) (v (y + 1)) := by
    intro hshift
    apply hfree
    exact containsC4_of_rim (huTri x) hshift (hvTri y).symm hxy.symm
      (hsep x (y + 1)) (hsep (x + 1) y)
      (fun h ↦ by
        have := hu h
        have hone : (1 : ZMod r) = 0 := by linear_combination this
        exact (by haveI : Fact (1 < r) := ⟨by omega⟩; exact one_ne_zero hone))
      (hsep (x + 1) (y + 1)) (hsep x y).symm
      (fun h ↦ by
        have := hv h.symm
        have hone : (1 : ZMod n) = 0 := by linear_combination this
        exact (by haveI : Fact (1 < n) := ⟨by omega⟩; exact one_ne_zero hone))
  have hminus : ¬ G.Adj (u (x + 1)) (v (y - 1)) := by
    intro hshift
    apply hfree
    exact containsC4_of_rim (huTri x) hshift (hvTri (y - 1))
      (by simpa using hxy.symm)
      (hsep x (y - 1)) (by simpa using hsep (x + 1) y)
      (fun h ↦ by
        have := hu h
        have hone : (1 : ZMod r) = 0 := by linear_combination this
        exact (by haveI : Fact (1 < r) := ⟨by omega⟩; exact one_ne_zero hone))
      (hsep (x + 1) (y - 1)) (by simpa using (hsep x y).symm)
      (fun h ↦ by
        have := hv h
        have hone : (1 : ZMod n) = 0 := by linear_combination this
        exact (by haveI : Fact (1 < n) := ⟨by omega⟩; exact one_ne_zero hone))
  have hrec := hinter (x + 1) y
  simp only [add_sub_cancel_right] at hrec
  simp [SimpleGraph.adjMatrix_apply, hxy, hplus, hminus] at hrec
  split at hrec <;> omega

/-- **Independent-color theorem in quotient form.**  Distinct defect
components whose cycle edges are both triangle-free edges of `G` have zero
component-quotient entry.  Hence all triangle-free-colored components form
an independent set in the full quotient support relation. -/
theorem componentQuotient_eq_zero_of_both_triangleFree_cycles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (u : ZMod r → V) (v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (huTri : ∀ x, G.Adj (u x) (u (x + 1)))
    (hvTri : ∀ y, G.Adj (v y) (v (y + 1))) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c e = 0 := by
  let D := secondOrderDefectGraph G
  have hsep : ∀ x y, u x ≠ v y := by
    intro x y hxy
    have hux : u x ∈ c.supp := by
      rw [← huRange]
      exact ⟨x, rfl⟩
    have hvy : v y ∈ e.supp := by
      rw [← hvRange]
      exact ⟨y, rfl⟩
    have hc : D.connectedComponentMk (u x) = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c (u x)).mp hux
    have he : D.connectedComponentMk (v y) = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e (v y)).mp hvy
    apply hce
    rw [hxy] at hc
    exact hc.symm.trans he
  have hnone := no_cross_edges_between_triangleFree_cycles hr hn G D u v
    hu hv hsep huD hvD
    (adjMatrix_comm_secondOrderDefect_of_even G hfree hd heven hmin hcard)
    huTri hvTri hfree
  have hu0c : u 0 ∈ c.supp := by
    rw [← huRange]
    exact ⟨0, rfl⟩
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard) c e hu0c
  rw [hQ]
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hydata : G.Adj (u 0) y ∧ y ∈ e.supp := by
    simpa [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
      and_comm] using hy
  have hyrange : y ∈ Set.range v := by simpa [hvRange] using hydata.2
  obtain ⟨z, rfl⟩ := hyrange
  exact hnone 0 z hydata.1

/-- Two triangle-free-colored cycles cannot be joined by a globally oriented
one-neighbour cyclic cover in a `C₄`-free graph. -/
theorem false_of_cycleCover_between_triangleFree_cycles
    {V : Type*} [Fintype V] [DecidableEq V]
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ZMod r → V) (v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hsep : ∀ x y, u x ≠ v y)
    (f : ZMod n → ZMod r)
    (hcover : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (huTri : ∀ x, G.Adj (u x) (u (x + 1)))
    (hvTri : ∀ y, G.Adj (v y) (v (y + 1)))
    (hfree : ¬ containsC4 V G) : False := by
  letI : Fact (1 < r) := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  have hcross0 : G.Adj (u (f 0)) (v 0) :=
    (hcover (f 0) 0).mpr rfl
  have hcross1 : G.Adj (u (f (0 + 1))) (v (0 + 1)) :=
    (hcover (f (0 + 1)) (0 + 1)).mpr rfl
  have huf : G.Adj (u (f 0)) (u (f (0 + 1))) := by
    rcases horient with hplus | hminus
    · rw [hplus 0]
      exact huTri (f 0)
    · rw [hminus 0]
      simpa using (huTri (f 0 - 1)).symm
  have hv01 : G.Adj (v 0) (v (0 + 1)) := hvTri 0
  have hfne : f (0 + 1) ≠ f 0 := by
    rcases horient with hplus | hminus
    · rw [hplus 0]
      intro h
      have hone : (1 : ZMod r) = 0 := by linear_combination h
      exact one_ne_zero hone
    · rw [hminus 0]
      intro h
      have hone : (1 : ZMod r) = 0 := by linear_combination -h
      exact one_ne_zero hone
  have hvne : v 0 ≠ v (0 + 1) := by
    intro h
    have heq := hv h
    have hone : (0 : ZMod n) = 1 := by simpa using heq
    exact zero_ne_one hone
  apply hfree
  exact containsC4_of_rim huf hcross1 hv01.symm hcross0.symm
    (hsep (f 0) (0 + 1))
    (hsep (f (0 + 1)) 0)
    (fun h ↦ hfne (hu h))
    (hsep (f (0 + 1)) (0 + 1))
    (hsep (f 0) 0).symm
    hvne

/-- **Graph-facing color restriction on a minimum-to-larger quotient
edge.**  If a minimum defect component has a positive quotient edge to a
strictly larger component, their cyclic defect edges cannot both be edges
of `G`.  In the second-order coloring, at least one endpoint component is
therefore antipodal-colored. -/
theorem not_both_triangleFree_of_minimumComponent_longer_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c e)
    (u : ZMod r → V) (v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)}) :
    ¬ ((∀ x, G.Adj (u x) (u (x + 1))) ∧
      (∀ y, G.Adj (v y) (v (y + 1)))) := by
  rintro ⟨huTri, hvTri⟩
  obtain ⟨f, hcover, horient, _⟩ :=
    exists_minimumComponent_longer_cycleCover G hfree hd heven hmin hcard
      hr hn c e hcmin hlt hpos u v hu hv huRange hvRange huD hvD
  have hce : c ≠ e := by
    intro h
    rw [h] at hlt
    omega
  have hsep : ∀ x y, u x ≠ v y := by
    intro x y hxy
    have hux : u x ∈ c.supp := by
      rw [← huRange]
      exact ⟨x, rfl⟩
    have hvy : v y ∈ e.supp := by
      rw [← hvRange]
      exact ⟨y, rfl⟩
    have hc : (secondOrderDefectGraph G).connectedComponentMk (u x) = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c (u x)).mp hux
    have he : (secondOrderDefectGraph G).connectedComponentMk (v y) = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e (v y)).mp hvy
    apply hce
    rw [hxy] at hc
    exact hc.symm.trans he
  exact false_of_cycleCover_between_triangleFree_cycles hr hn G u v hu hv
    hsep f hcover horient huTri hvTri hfree

end

end Erdos85
