import Proofs.Erdos85Problem

/-!
# A local `C₄` criterion for adding or sliding one edge

Adding the nonedge `yz` to a `C₄`-free graph can create a four-cycle only
when the old graph already contains a three-edge walk from `y` to `z`.
Deleting edges before the addition only weakens that obstruction, giving the
same convenient sufficient criterion for an edge slide.
-/

open SimpleGraph

namespace Erdos85

/-- Add the single undirected edge `yz` to `G`. -/
def addEdge {V : Type*} (G : SimpleGraph V) (y z : V) : SimpleGraph V :=
  G ⊔ SimpleGraph.edge y z

theorem addEdge_adj_iff {V : Type*} (G : SimpleGraph V) (y z a b : V) :
    (addEdge G y z).Adj a b ↔
      G.Adj a b ∨ (((a = y ∧ b = z) ∨ (a = z ∧ b = y)) ∧ a ≠ b) := by
  simp [addEdge, SimpleGraph.edge_adj]

/-- There is a three-edge walk in `G` from `y` to `z`.  When `yz` is a
nonedge, irreflexivity forces the four vertices in such a witness to be
distinct in exactly the ways needed for a four-cycle. -/
def HasThreeEdgeWalk {V : Type*} (G : SimpleGraph V) (y z : V) : Prop :=
  ∃ a b, G.Adj y a ∧ G.Adj a b ∧ G.Adj b z

set_option maxHeartbeats 2000000

/-- If adding one edge to a `C₄`-free graph creates a `C₄`, its other
three rim edges were already present. -/
theorem hasThreeEdgeWalk_of_containsC4_addEdge
    {V : Type*} (G : SimpleGraph V) (y z : V)
    (hfree : ¬ containsC4 V G)
    (hc4 : containsC4 V (addEdge G y z)) :
    HasThreeEdgeWalk G y z := by
  obtain ⟨f, hinj, hadj⟩ := hc4
  let a := f 0
  let b := f 1
  let c := f 2
  let d := f 3
  have hab := (addEdge_adj_iff G y z a b).mp (hadj 0 1 (by decide))
  have hbc := (addEdge_adj_iff G y z b c).mp (hadj 1 2 (by decide))
  have hcd := (addEdge_adj_iff G y z c d).mp (hadj 2 3 (by decide))
  have hda := (addEdge_adj_iff G y z d a).mp (hadj 3 0 (by decide))
  have hac : a ≠ c := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (hinj (by simpa [a, c] using h))
  have hbd : b ≠ d := fun h =>
    (by decide : (1 : Fin 4) ≠ 3) (hinj (by simpa [b, d] using h))
  have hba : b ≠ a := fun h =>
    (by decide : (1 : Fin 4) ≠ 0) (hinj (by simpa [a, b] using h))
  have hbcne : b ≠ c := fun h =>
    (by decide : (1 : Fin 4) ≠ 2) (hinj (by simpa [b, c] using h))
  have hdane : d ≠ a := fun h =>
    (by decide : (3 : Fin 4) ≠ 0) (hinj (by simpa [a, d] using h))
  have hdc : d ≠ c := fun h =>
    (by decide : (3 : Fin 4) ≠ 2) (hinj (by simpa [c, d] using h))
  have habbc : s(a,b) ≠ s(b,c) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact (by decide : (0 : Fin 4) ≠ 1) (hinj (by simpa [a, b] using h))
    · exact (by decide : (0 : Fin 4) ≠ 2) (hinj (by simpa [a, c] using h))
  have habcd : s(a,b) ≠ s(c,d) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact (by decide : (0 : Fin 4) ≠ 2) (hinj (by simpa [a, c] using h))
    · exact (by decide : (0 : Fin 4) ≠ 3) (hinj (by simpa [a, d] using h))
  have habda : s(a,b) ≠ s(d,a) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
    · exact (by decide : (0 : Fin 4) ≠ 3) (hinj (by simpa [a, d] using h))
    · exact (by decide : (1 : Fin 4) ≠ 3) (hinj (by simpa [b, d] using h))
  have hbccd : s(b,c) ≠ s(c,d) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact (by decide : (1 : Fin 4) ≠ 2) (hinj (by simpa [b, c] using h))
    · exact (by decide : (1 : Fin 4) ≠ 3) (hinj (by simpa [b, d] using h))
  have hbcda : s(b,c) ≠ s(d,a) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact (by decide : (1 : Fin 4) ≠ 3) (hinj (by simpa [b, d] using h))
    · exact (by decide : (0 : Fin 4) ≠ 1) (hinj (by simpa [a, b] using h.symm))
  have hcdda : s(c,d) ≠ s(d,a) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact (by decide : (2 : Fin 4) ≠ 3) (hinj (by simpa [c, d] using h))
    · exact (by decide : (0 : Fin 4) ≠ 2) (hinj (by simpa [a, c] using h.symm))
  have special_eq {p q : V}
      (h : ((p = y ∧ q = z) ∨ (p = z ∧ q = y)) ∧ p ≠ q) :
      s(p,q) = s(y,z) := by
    rw [Sym2.eq_iff]
    tauto
  rcases hab with hab | hab
  · rcases hbc with hbc | hbc
    · rcases hcd with hcd | hcd
      · rcases hda with hda | hda
        · exact (hfree (containsC4_of_rim hab hbc hcd hda
            hac hbd hba hbcne hdane hdc)).elim
        · rcases hda.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨c, b, hcd.symm, hbc.symm, hab.symm⟩
          · exact ⟨b, c, hab, hbc, hcd⟩
      · have hscd : s(c,d) = s(y,z) := special_eq hcd
        rcases hda with hda | hda
        · rcases hcd.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨b, a, hbc.symm, hab.symm, hda.symm⟩
          · exact ⟨a, b, hda, hab, hbc⟩
        · exact (hcdda (hscd.trans (special_eq hda).symm)).elim
    · have : s(b,c) = s(y,z) := special_eq hbc
      rcases hcd with hcd | hcd
      · rcases hda with hda | hda
        · rcases hbc.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨a, d, hab.symm, hda.symm, hcd.symm⟩
          · exact ⟨d, a, hcd, hda, hab⟩
        · exact (hbcda (this.trans (special_eq hda).symm)).elim
      · exact (hbccd (this.trans (special_eq hcd).symm)).elim
  · have hsab : s(a,b) = s(y,z) := special_eq hab
    rcases hbc with hbc | hbc
    · rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hcd with hcd | hcd
        · rcases hda with hda | hda
          · exact ⟨d, c, hda.symm, hcd.symm, hbc.symm⟩
          · exact (habda (hsab.trans (special_eq hda).symm)).elim
        · exact (habcd (hsab.trans (special_eq hcd).symm)).elim
      · rcases hcd with hcd | hcd
        · rcases hda with hda | hda
          · exact ⟨c, d, hbc, hcd, hda⟩
          · exact (habda (hsab.trans (special_eq hda).symm)).elim
        · exact (habcd (hsab.trans (special_eq hcd).symm)).elim
    · exact (habbc (hsab.trans (special_eq hbc).symm)).elim

/-- Adding `yz` preserves `C₄`-freeness whenever the old graph has no
three-edge walk between the endpoints. -/
theorem addEdge_not_containsC4_of_no_threeEdgeWalk
    {V : Type*} (G : SimpleGraph V) (y z : V)
    (hfree : ¬ containsC4 V G)
    (hpath : ¬ HasThreeEdgeWalk G y z) :
    ¬ containsC4 V (addEdge G y z) := by
  exact fun hc4 => hpath (hasThreeEdgeWalk_of_containsC4_addEdge G y z hfree hc4)

/-- Delete `xz` and insert `yz`. -/
def edgeSlide {V : Type*} (G : SimpleGraph V) (x y z : V) : SimpleGraph V :=
  addEdge (G.deleteEdges {s(x,z)}) y z

/-- A simple graph remains `C₄`-free after sliding `xz` to `yz` provided
there was no old three-edge walk from `y` to `z`. -/
theorem edgeSlide_not_containsC4_of_no_threeEdgeWalk
    {V : Type*} (G : SimpleGraph V) (x y z : V)
    (hfree : ¬ containsC4 V G)
    (hpath : ¬ HasThreeEdgeWalk G y z) :
    ¬ containsC4 V (edgeSlide G x y z) := by
  apply addEdge_not_containsC4_of_no_threeEdgeWalk
  · exact fun hc4 => hfree (containsC4_mono (G.deleteEdges_le _) hc4)
  · intro hp
    apply hpath
    rcases hp with ⟨a, b, hya, hab, hbz⟩
    exact ⟨a, b, (G.deleteEdges_le _ hya), (G.deleteEdges_le _ hab),
      (G.deleteEdges_le _ hbz)⟩

/-! ## Degree bookkeeping for a genuine slide -/

theorem edgeSlide_neighborFinset_x
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hxz : x ≠ z) :
    (edgeSlide G x y z).neighborFinset x = (G.neighborFinset x).erase z := by
  ext v
  simp [edgeSlide, addEdge, SimpleGraph.deleteEdges_adj,
    SimpleGraph.edge_adj, Sym2.eq_iff, hxy, hxy.symm, hxz, hxz.symm] <;> aesop

theorem edgeSlide_neighborFinset_y
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hyz : y ≠ z) :
    (edgeSlide G x y z).neighborFinset y = insert z (G.neighborFinset y) := by
  ext v
  simp [edgeSlide, addEdge, SimpleGraph.deleteEdges_adj,
    SimpleGraph.edge_adj, Sym2.eq_iff, hxy, hxy.symm, hyz, hyz.symm] <;> aesop

theorem edgeSlide_neighborFinset_z
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (edgeSlide G x y z).neighborFinset z =
      insert y ((G.neighborFinset z).erase x) := by
  ext v
  simp [edgeSlide, addEdge, SimpleGraph.deleteEdges_adj,
    SimpleGraph.edge_adj, Sym2.eq_iff, hxy, hxy.symm, hxz, hxz.symm,
      hyz, hyz.symm] <;> aesop

theorem edgeSlide_neighborFinset_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z v : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hvx : v ≠ x) (hvy : v ≠ y) (hvz : v ≠ z) :
    (edgeSlide G x y z).neighborFinset v = G.neighborFinset v := by
  ext w
  simp [edgeSlide, addEdge, SimpleGraph.deleteEdges_adj,
    SimpleGraph.edge_adj, Sym2.eq_iff, hvx, hvy, hvz]

theorem edgeSlide_degree_x
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hxz : G.Adj x z) :
    (edgeSlide G x y z).degree x = G.degree x - 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    edgeSlide_neighborFinset_x G x y z hxy (G.ne_of_adj hxz),
    Finset.card_erase_of_mem]
  exact (G.mem_neighborFinset x z).mpr hxz

theorem edgeSlide_degree_y
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hyz : y ≠ z) (hnot : ¬ G.Adj y z) :
    (edgeSlide G x y z).degree y = G.degree y + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    edgeSlide_neighborFinset_y G x y z hxy hyz,
    Finset.card_insert_of_notMem]
  simpa only [SimpleGraph.mem_neighborFinset] using hnot

theorem edgeSlide_degree_z
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : G.Adj x z) (hnot : ¬ G.Adj y z) :
    (edgeSlide G x y z).degree z = G.degree z := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree,
    edgeSlide_neighborFinset_z G x y z hxy (G.ne_of_adj hxz) hyz,
    Finset.card_insert_of_notMem, Finset.card_erase_of_mem]
  · have hpos : 0 < (G.neighborFinset z).card :=
      Finset.card_pos.mpr ⟨x, (G.mem_neighborFinset z x).mpr hxz.symm⟩
    omega
  · simpa only [SimpleGraph.mem_neighborFinset] using hxz.symm
  · simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    exact fun h => hnot h.2.symm

/-- Moving one edge away from a vertex strictly above the degree floor does
not lower the minimum degree. -/
theorem le_minDegree_edgeSlide
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y z : V)
    [DecidableRel (edgeSlide G x y z).Adj]
    {d : ℕ} (hmin : d ≤ G.minDegree) (hx : d < G.degree x)
    (hxy : x ≠ y) (hyz : y ≠ z)
    (hxz : G.Adj x z) (hnot : ¬ G.Adj y z) :
    d ≤ (edgeSlide G x y z).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  by_cases hvx : v = x
  · subst v
    rw [edgeSlide_degree_x G x y z hxy hxz]
    omega
  by_cases hvy : v = y
  · subst v
    rw [edgeSlide_degree_y G x y z hxy hyz hnot]
    exact le_add_right (SimpleGraph.minDegree_le_degree G y |>.trans' hmin)
  by_cases hvz : v = z
  · subst v
    rw [edgeSlide_degree_z G x y z hxy hyz hxz hnot]
    exact hmin.trans (SimpleGraph.minDegree_le_degree G z)
  · rw [← SimpleGraph.card_neighborFinset_eq_degree,
      edgeSlide_neighborFinset_of_ne G x y z v hvx hvy hvz,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact hmin.trans (SimpleGraph.minDegree_le_degree G v)

end Erdos85
