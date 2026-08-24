import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85F2WalkBoundary

/-!
# A route between the only two odd-degree vertices

The two-pole Baer potential produces a cut graph whose only odd-degree
vertices are the two empty poles.  Handshaking inside a connected component
forces those poles into the same component, and hence supplies the actual
owner route used in equation (73rnz_bl).
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If a finite graph has exactly two odd-degree vertices, they are
reachable. -/
theorem reachable_of_odd_degree_iff_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {u v : V}
    (hodd : ∀ x, Odd (H.degree x) ↔ x = u ∨ x = v) :
    H.Reachable u v := by
  by_contra hreach
  let c : H.ConnectedComponent := H.connectedComponentMk u
  have huMem : u ∈ c.supp := by
    apply (ConnectedComponent.mem_supp_iff c u).mpr
    rfl
  have hvNot : v ∉ c.supp := by
    intro hv
    have hvc : H.connectedComponentMk v = c :=
      (ConnectedComponent.mem_supp_iff c v).mp hv
    have huc : H.connectedComponentMk u = c := rfl
    apply hreach
    exact ConnectedComponent.exact (huc.trans hvc.symm)
  let K : SimpleGraph c.supp := H.induce c.supp
  let u' : c.supp := ⟨u, huMem⟩
  have hoddK : ∀ x : c.supp, Odd (K.degree x) ↔ x = u' := by
    intro x
    have hdegree : K.degree x = H.degree x.1 :=
      degree_induce_connectedComponent_supp H c x
    rw [hdegree, hodd x]
    constructor
    · intro hx
      rcases hx with hxu | hxv
      · exact Subtype.ext hxu
      · exfalso
        apply hvNot
        simpa [hxv] using x.2
    · intro hx
      left
      exact congrArg Subtype.val hx
  have hset :
      ({x : c.supp | Odd (K.degree x)} : Finset c.supp) = {u'} := by
    ext x
    simp [hoddK x]
  have heven := K.even_card_odd_degree_vertices
  rw [hset] at heven
  norm_num at heven

/-- Walk form of the same theorem, ready for F₂ boundary telescoping. -/
theorem exists_walk_of_odd_degree_iff_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {u v : V}
    (hodd : ∀ x, Odd (H.degree x) ↔ x = u ∨ x = v) :
    ∃ p : H.Walk u v, f2WalkEdgeBoundary p = f2EndpointSwitch u v := by
  obtain ⟨p⟩ := reachable_of_odd_degree_iff_eq_two H hodd
  exact ⟨p, f2WalkEdgeBoundary_eq_endpointSwitch p⟩

end

end Erdos85

#print axioms Erdos85.reachable_of_odd_degree_iff_eq_two
#print axioms Erdos85.exists_walk_of_odd_degree_iff_eq_two
