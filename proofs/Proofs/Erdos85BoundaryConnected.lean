import Proofs.Erdos85EvenAntipodalQuotient
import Proofs.Erdos85ComponentFactorization

/-!
# Connectedness at the second strict Moore boundary

Every connected component inherits both `C₄`-freeness and the ambient
minimum-degree bound.  Applying the second strict Moore bound componentwise
shows that a graph at order `d(d-1)+3` has exactly one component.
-/

namespace Erdos85

open SimpleGraph

/-- A connected component of a `C₄`-free minimum-degree-`d` graph satisfies
the same second strict Moore lower bound as the whole graph. -/
theorem connectedComponent_second_strict_moore_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree) (c : G.ConnectedComponent) :
    d * (d - 1) + 3 ≤ c.supp.ncard := by
  classical
  letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
  have hfreeH : ¬ containsC4 c.supp (G.induce c.supp) := by
    rintro ⟨f, hf, hadj⟩
    apply hfree
    refine ⟨fun i => (f i).1, ?_, ?_⟩
    · intro i j hij
      exact hf (Subtype.ext hij)
    · intro i j hij
      exact hadj i j hij
  have hneighbor (x : c.supp) : G.neighborSet x.1 ⊆ c.supp := by
    intro y hxy
    have hcx : G.connectedComponentMk x.1 = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c x.1).mp x.2
    have hcy := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mpr
      (hcy.symm.trans hcx)
  have hminH : d ≤ (G.induce c.supp).minDegree := by
    apply (G.induce c.supp).le_minDegree_of_forall_le_degree
    intro x
    rw [G.degree_induce_of_neighborSet_subset (hneighbor x)]
    exact hmin.trans (G.minDegree_le_degree x.1)
  have hb := second_strict_moore_bound (G.induce c.supp) hfreeH hd hminH
  exact hb.trans_eq (by
    simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp)

/-- At the second strict Moore order, the graph is connected. -/
theorem connected_of_second_strict_moore_order
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 3 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    Fintype.card G.ConnectedComponent = 1 := by
  classical
  let L := d * (d - 1) + 3
  have hcomponent (c : G.ConnectedComponent) : L ≤ c.supp.ncard := by
    exact connectedComponent_second_strict_moore_bound G hfree hd hmin c
  have hparts : (∑ c : G.ConnectedComponent, c.supp.ncard) =
      Fintype.card V := by
    calc
      (∑ c : G.ConnectedComponent, c.supp.ncard) =
          ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
            apply Finset.sum_congr rfl
            intro c hc
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : G.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
  have hsubsingleton : Subsingleton G.ConnectedComponent := by
    constructor
    intro c e
    by_contra hce
    have hpair : 2 * L ≤ ∑ a : G.ConnectedComponent, a.supp.ncard := by
      have hle : c.supp.ncard + e.supp.ncard ≤
          ∑ a : G.ConnectedComponent, a.supp.ncard := by
        calc
          c.supp.ncard + e.supp.ncard =
              ∑ a ∈ ({c, e} : Finset G.ConnectedComponent), a.supp.ncard := by
                simp [hce]
          _ ≤ ∑ a ∈ (Finset.univ : Finset G.ConnectedComponent),
              a.supp.ncard := by
                exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by simp)
          _ = ∑ a : G.ConnectedComponent, a.supp.ncard := by simp
      have hc := hcomponent c
      have he := hcomponent e
      omega
    rw [hparts, hcard] at hpair
    dsimp [L] at hpair
    omega
  letI : Unique G.ConnectedComponent := {
    default := G.connectedComponentMk (Classical.choice inferInstance)
    uniq := fun _ => hsubsingleton.elim _ _ }
  exact Fintype.card_unique

end Erdos85
