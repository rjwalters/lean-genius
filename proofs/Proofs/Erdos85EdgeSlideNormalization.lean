import Proofs.Erdos85EdgeSlideCriterion

/-!
# Degree-square normalization by edge slides

Sliding an edge from a higher-degree vertex to a sufficiently lower-degree
vertex strictly decreases the sum of squared degrees.  A graph minimizing
this energy inside the fixed-order `C₄`-free minimum-degree class is
therefore saturated against every such slide by a three-edge walk.
-/

open SimpleGraph

namespace Erdos85

/-- The convex degree energy used to normalize a fixed-order witness. -/
noncomputable def degreeSquareEnergy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ v : V, G.degree v * G.degree v

/-- Exact energy bookkeeping for a genuine edge slide.  Adding the two old
local square terms to the new energy is the same as adding the two new local
square terms to the old energy. -/
theorem degreeSquareEnergy_edgeSlide_add_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : G.Adj x z) (hnot : ¬ G.Adj y z) :
    degreeSquareEnergy (edgeSlide G x y z) +
        G.degree x * G.degree x + G.degree y * G.degree y =
      degreeSquareEnergy G +
        (G.degree x - 1) * (G.degree x - 1) +
          (G.degree y + 1) * (G.degree y + 1) := by
  classical
  let oldCorrection : V → ℕ := fun v ↦
    if v = x then G.degree x * G.degree x
    else if v = y then G.degree y * G.degree y else 0
  let newCorrection : V → ℕ := fun v ↦
    if v = x then (G.degree x - 1) * (G.degree x - 1)
    else if v = y then (G.degree y + 1) * (G.degree y + 1) else 0
  have hpoint : ∀ v : V,
      (edgeSlide G x y z).degree v * (edgeSlide G x y z).degree v +
          oldCorrection v =
        G.degree v * G.degree v + newCorrection v := by
    intro v
    by_cases hvx : v = x
    · subst v
      rw [edgeSlide_degree_x G x y z hxy hxz]
      simp [oldCorrection, newCorrection, hxy, Nat.add_comm]
    by_cases hvy : v = y
    · subst v
      rw [edgeSlide_degree_y G x y z hxy hyz hnot]
      simp [oldCorrection, newCorrection, hvx, Nat.add_comm]
    by_cases hvz : v = z
    · subst v
      rw [edgeSlide_degree_z G x y z hxy hyz hxz hnot]
      simp [oldCorrection, newCorrection, hvx, hvy]
    · rw [← SimpleGraph.card_neighborFinset_eq_degree,
          edgeSlide_neighborFinset_of_ne G x y z v hvx hvy hvz,
          SimpleGraph.card_neighborFinset_eq_degree]
      simp [oldCorrection, newCorrection, hvx, hvy]
  have hsum :
      (∑ v : V, ((edgeSlide G x y z).degree v *
          (edgeSlide G x y z).degree v + oldCorrection v)) =
        ∑ v : V, (G.degree v * G.degree v + newCorrection v) := by
    apply Finset.sum_congr rfl
    intro v _
    exact hpoint v
  simp only [Finset.sum_add_distrib] at hsum
  have holdCorrection : (∑ v : V, oldCorrection v) =
      G.degree x * G.degree x + G.degree y * G.degree y := by
    have hsplit : ∀ v : V, oldCorrection v =
        (if v = x then G.degree x * G.degree x else 0) +
          (if v = y then G.degree y * G.degree y else 0) := by
      intro v
      by_cases hvx : v = x <;> by_cases hvy : v = y <;>
        simp [oldCorrection, hvx, hvy, hxy, hxy.symm]
    rw [Finset.sum_congr rfl fun v _ ↦ hsplit v,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
  have hnewCorrection : (∑ v : V, newCorrection v) =
      (G.degree x - 1) * (G.degree x - 1) +
        (G.degree y + 1) * (G.degree y + 1) := by
    have hsplit : ∀ v : V, newCorrection v =
        (if v = x then (G.degree x - 1) * (G.degree x - 1) else 0) +
          (if v = y then (G.degree y + 1) * (G.degree y + 1) else 0) := by
      intro v
      by_cases hvx : v = x <;> by_cases hvy : v = y <;>
        simp [newCorrection, hvx, hvy, hxy, hxy.symm]
    rw [Finset.sum_congr rfl fun v _ ↦ hsplit v,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp
  rw [holdCorrection, hnewCorrection] at hsum
  simpa only [degreeSquareEnergy, Nat.add_assoc] using hsum

/-- Moving an edge from `x` to `y` strictly lowers degree-square energy when
`deg(y)+1 < deg(x)`. -/
theorem degreeSquareEnergy_edgeSlide_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : G.Adj x z) (hnot : ¬ G.Adj y z)
    (hgap : G.degree y + 1 < G.degree x) :
    degreeSquareEnergy (edgeSlide G x y z) < degreeSquareEnergy G := by
  have henergy := degreeSquareEnergy_edgeSlide_add_local
    G x y z hxy hyz hxz hnot
  have hxpos : 0 < G.degree x := by
    exact Finset.card_pos.mpr ⟨z, (G.mem_neighborFinset x z).mpr hxz⟩
  have hxsub : G.degree x - 1 + 1 = G.degree x := by omega
  have hlocal :
      (G.degree x - 1) * (G.degree x - 1) +
          (G.degree y + 1) * (G.degree y + 1) <
        G.degree x * G.degree x + G.degree y * G.degree y := by
    nlinarith
  omega

/-- A fixed-order graph is degree-square minimal in the `C₄`-free
minimum-degree-`d` class. -/
def IsDegreeSquareMinimizer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ H : SimpleGraph V,
    ∀ [DecidableRel H.Adj], ¬ containsC4 V H → d ≤ H.minDegree →
      degreeSquareEnergy G ≤ degreeSquareEnergy H

/-- **Local saturation of an energy minimizer.**  Every genuine slide from
a higher-degree endpoint to a sufficiently lower-degree nonneighbor is
blocked by an old three-edge walk. -/
theorem hasThreeEdgeWalk_deleteEdge_of_degreeSquareMinimizer
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hfree : ¬ containsC4 V G) (hmin : d ≤ G.minDegree)
    (hminimal : IsDegreeSquareMinimizer G d)
    (x y z : V) (hyz : y ≠ z)
    (hxz : G.Adj x z) (hnot : ¬ G.Adj y z)
    (hgap : G.degree y + 1 < G.degree x) :
    HasThreeEdgeWalk (G.deleteEdges {s(x,z)}) y z := by
  have hxy : x ≠ y := by
    intro h
    subst y
    omega
  let S := edgeSlide G x y z
  letI : DecidableRel S.Adj := Classical.decRel _
  have hxabove : d < G.degree x := by
    have hymin := hmin.trans (G.minDegree_le_degree y)
    omega
  have hSmin : d ≤ S.minDegree :=
    le_minDegree_edgeSlide G x y z hmin hxabove hxy hyz hxz hnot
  have hlt : degreeSquareEnergy S < degreeSquareEnergy G :=
    degreeSquareEnergy_edgeSlide_lt G x y z hxy hyz hxz hnot hgap
  have hSc4 : containsC4 V S := by
    by_contra hSfree
    have hle : degreeSquareEnergy G ≤ degreeSquareEnergy S :=
      hminimal S hSfree hSmin
    omega
  have hbasefree : ¬ containsC4 V (G.deleteEdges {s(x,z)}) :=
    fun hc4 ↦ hfree (containsC4_mono (G.deleteEdges_le _) hc4)
  apply hasThreeEdgeWalk_of_containsC4_addEdge
    (G.deleteEdges {s(x,z)}) y z hbasefree
  simpa [S, edgeSlide] using hSc4

/-- Weaker graph-facing consequence of the deleted-edge saturation theorem. -/
theorem hasThreeEdgeWalk_of_degreeSquareMinimizer
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hfree : ¬ containsC4 V G) (hmin : d ≤ G.minDegree)
    (hminimal : IsDegreeSquareMinimizer G d)
    (x y z : V) (hyz : y ≠ z)
    (hxz : G.Adj x z) (hnot : ¬ G.Adj y z)
    (hgap : G.degree y + 1 < G.degree x) :
    HasThreeEdgeWalk G y z := by
  rcases hasThreeEdgeWalk_deleteEdge_of_degreeSquareMinimizer
      G hfree hmin hminimal x y z hyz hxz hnot hgap with
    ⟨a, b, hya, hab, hbz⟩
  exact ⟨a, b, G.deleteEdges_le _ hya, G.deleteEdges_le _ hab,
    G.deleteEdges_le _ hbz⟩

end Erdos85
