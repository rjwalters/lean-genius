import Proofs.Erdos85OddComponentClosure

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
