import Proofs.Erdos85MuNegThreeOneTwoOwnerBridge
import Proofs.Erdos85SizeTwoMuNegThreeAlignedShoreSwitch
import Proofs.Erdos85SizeTwoOwnerVertexDictionary

/-!
# Graph realization of the `mu=-3`, `(k,r)=(1,2)` owner relations

This layer fixes the graph meaning of the two finite relations consumed by
`muNegThreeOneTwoFiniteSemantics_false`.  A defect bit is signed cross-defect
adjacency between the two cyclic shores.  An owner hit means that the two
active cross cells have a common exterior owner vertex.

Node: outline F.3, canonical negative switch endpoint `(-3,1,2)`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- The vertex pair named by cross-cell `a = 8i+j`. -/
def muNegThreeOwnerEndpoints (u v : ZMod 8 → c.supp) (a : Nat) : V × V :=
  ((u (muNegThreeCellRow a : ZMod 8)).1,
    (v (muNegThreeCellCol a : ZMod 8)).1)

/-- A graph vertex realizing a cross-cell owner. -/
def MuNegThreeOwnerVertex (u v : ZMod 8 → c.supp)
    (a : Nat) (z : V) : Prop :=
  z ∉ c.supp ∧
    G.Adj (muNegThreeOwnerEndpoints G c u v a).1 z ∧
    G.Adj (muNegThreeOwnerEndpoints G c u v a).2 z

/-- The signed cross-defect relation in cyclic coordinates. -/
def muNegThreeCrossDefectRel (s : V → ℤ)
    (u v : ZMod 8 → c.supp) (i j : Nat) : Bool :=
  decide (s (u (i : ZMod 8)).1 = s (v (j : ZMod 8)).1 ∧
    (secondOrderDefectGraph G).Adj
      (u (i : ZMod 8)).1 (v (j : ZMod 8)).1)

/-- Two cross-cell owners hit when their exterior owner vertices are
adjacent in the ambient graph. -/
noncomputable def muNegThreeOwnerHitRel (u v : ZMod 8 → c.supp)
    (a b : Nat) : Bool := by
  classical
  exact decide (∃ z w : V,
    MuNegThreeOwnerVertex G c u v a z ∧
    MuNegThreeOwnerVertex G c u v b w ∧ G.Adj z w)

@[simp] theorem muNegThreeCrossDefectRel_eq_true
    (s : V → ℤ) (u v : ZMod 8 → c.supp) (i j : Nat) :
    muNegThreeCrossDefectRel G c s u v i j = true ↔
      s (u (i : ZMod 8)).1 = s (v (j : ZMod 8)).1 ∧
        (secondOrderDefectGraph G).Adj
          (u (i : ZMod 8)).1 (v (j : ZMod 8)).1 := by
  simp [muNegThreeCrossDefectRel]

@[simp] theorem muNegThreeOwnerHitRel_eq_true
    (u v : ZMod 8 → c.supp) (a b : Nat) :
    muNegThreeOwnerHitRel G c u v a b = true ↔
      ∃ z w : V, MuNegThreeOwnerVertex G c u v a z ∧
        MuNegThreeOwnerVertex G c u v b w ∧ G.Adj z w := by
  classical
  simp [muNegThreeOwnerHitRel]

theorem muNegThreeOwnerEndpoints_row_col
    (u v : ZMod 8 → c.supp) {a : Nat} (ha : a < 64) :
    muNegThreeOwnerEndpoints G c u v a =
      ((u (muNegThreeCellRow a : ZMod 8)).1,
        (v (muNegThreeCellCol a : ZMod 8)).1) := by
  rfl

/-- In the induced valuation, a cross cell is active exactly when its
signed defect adjacency is absent. -/
theorem muNegThreeOwnerActive_graph_iff
    (s : V → ℤ) (u v : ZMod 8 → c.supp) (a : Nat) :
    muNegThreeOwnerActive (muNegThreeCrossDefectRel G c s u v) a = true ↔
      ¬ (s (u (muNegThreeCellRow a : ZMod 8)).1 =
          s (v (muNegThreeCellCol a : ZMod 8)).1 ∧
        (secondOrderDefectGraph G).Adj
          (u (muNegThreeCellRow a : ZMod 8)).1
          (v (muNegThreeCellCol a : ZMod 8)).1) := by
  simp [muNegThreeOwnerActive, muNegThreeCrossDefectRel]
  tauto

/-- Hit symmetry is inherited from sharing the same exterior vertex. -/
theorem muNegThreeOwnerHitRel_comm
    (u v : ZMod 8 → c.supp) (a b : Nat) :
    muNegThreeOwnerHitRel G c u v a b =
      muNegThreeOwnerHitRel G c u v b a := by
  apply Bool.eq_iff_iff.mpr
  simp only [muNegThreeOwnerHitRel_eq_true]
  constructor
  · rintro ⟨z, w, hz, hw, hzw⟩
    exact ⟨w, z, hw, hz, hzw.symm⟩
  · rintro ⟨w, z, hw, hz, hwz⟩
    exact ⟨z, w, hz, hw, hwz.symm⟩

/-- A true hit decodes to adjacent concrete exterior vertices realizing
the two cross-cell owners. -/
theorem muNegThreeOwnerHitRel_witness
    (u v : ZMod 8 → c.supp) {a b : Nat}
    (h : muNegThreeOwnerHitRel G c u v a b = true) :
    ∃ z w : V, z ∉ c.supp ∧ w ∉ c.supp ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v a).1 z ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v a).2 z ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v b).1 w ∧
      G.Adj (muNegThreeOwnerEndpoints G c u v b).2 w ∧ G.Adj z w := by
  obtain ⟨z, w, ha, hb, hzw⟩ :=
    (muNegThreeOwnerHitRel_eq_true G c u v a b).mp h
  exact ⟨z, w, ha.1, hb.1, ha.2.1, ha.2.2, hb.2.1, hb.2.2, hzw⟩

section StructuralFields

variable [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- Cross-cell endpoints lie on distinct internal components. -/
theorem muNegThreeOwnerEndpoints_ne
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (x : Nat) :
    (muNegThreeOwnerEndpoints G c u v x).1 ≠
      (muNegThreeOwnerEndpoints G c u v x).2 := by
  intro huv
  apply hab
  let i : ZMod 8 := muNegThreeCellRow x
  let j : ZMod 8 := muNegThreeCellCol x
  have hui : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hvj : v j ∈ b.supp := by
    rw [← hvrange]
    exact ⟨j, rfl⟩
  have huv' : u i = v j := Subtype.ext huv
  exact ConnectedComponent.eq_of_common_vertex (huv' ▸ hui) hvj

/-- A realized exterior owner rules out defect adjacency of its endpoint
pair, since it supplies a common neighbor. -/
theorem muNegThreeOwnerVertex_not_defect
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {x : Nat} {z : V} (hz : MuNegThreeOwnerVertex G c u v x z) :
    ¬ (secondOrderDefectGraph G).Adj
      (muNegThreeOwnerEndpoints G c u v x).1
      (muNegThreeOwnerEndpoints G c u v x).2 := by
  intro hD
  have hne := muNegThreeOwnerEndpoints_ne G c a b hab u v hurange hvrange x
  have hzero := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
    G hfree hne).mp hD
  have hzmem : z ∈
      G.neighborFinset (muNegThreeOwnerEndpoints G c u v x).1 ∩
        G.neighborFinset (muNegThreeOwnerEndpoints G c u v x).2 := by
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hz.2.1, hz.2.2⟩
  rw [Finset.card_eq_zero] at hzero
  rw [hzero] at hzmem
  exact Finset.notMem_empty z hzmem

/-- Each cross cell has at most one exterior owner vertex. -/
theorem muNegThreeOwnerVertex_unique
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (x : Nat) {z w : V}
    (hz : MuNegThreeOwnerVertex G c u v x z)
    (hw : MuNegThreeOwnerVertex G c u v x w) : z = w :=
  commonServer_unique G hfree
    (muNegThreeOwnerEndpoints_ne G c a b hab u v hurange hvrange x)
    hz.2.1 hz.2.2 hw.2.1 hw.2.2

/-- For size-two components, an exterior owner vertex determines its
cross-cell coordinate. -/
theorem muNegThreeOwnerVertex_inj
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {x y : Nat} (hx64 : x < 64) (hy64 : y < 64) {z : V}
    (hx : MuNegThreeOwnerVertex G c u v x z)
    (hy : MuNegThreeOwnerVertex G c u v y z) : x = y := by
  let ux := u (muNegThreeCellRow x : ZMod 8)
  let vx := v (muNegThreeCellCol x : ZMod 8)
  let uy := u (muNegThreeCellRow y : ZMod 8)
  let vy := v (muNegThreeCellCol y : ZMod 8)
  have hpair : ({ux.1, vx.1} : Finset V) = {uy.1, vy.1} :=
    ownerVertex_pair_eq G hfree (by omega) hreg hcard c hsize
      (muNegThreeOwnerEndpoints_ne G c a b hab u v hurange hvrange x)
      (muNegThreeOwnerEndpoints_ne G c a b hab u v hurange hvrange y)
      ux.2 vx.2 uy.2 vy.2 hx.2.1.symm hx.2.2.symm
      hy.2.1.symm hy.2.2.symm
  have cross_ne (i j : ZMod 8) : (u i).1 ≠ (v j).1 := by
    intro huv
    apply hab
    have hui : u i ∈ a.supp := by rw [← hurange]; exact ⟨i, rfl⟩
    have hvj : v j ∈ b.supp := by rw [← hvrange]; exact ⟨j, rfl⟩
    exact ConnectedComponent.eq_of_common_vertex
      (Subtype.ext huv ▸ hui) hvj
  have huxmem : ux.1 ∈ ({uy.1, vy.1} : Finset V) := by
    rw [← hpair]
    simp
  have hvxmem : vx.1 ∈ ({uy.1, vy.1} : Finset V) := by
    rw [← hpair]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at huxmem hvxmem
  have huu : ux = uy := by
    rcases huxmem with h | h
    · exact Subtype.ext h
    · exact False.elim (cross_ne _ _ h)
  have hvv : vx = vy := by
    rcases hvxmem with h | h
    · exact False.elim (cross_ne _ _ h.symm)
    · exact Subtype.ext h
  have hrowZ : (muNegThreeCellRow x : ZMod 8) =
      (muNegThreeCellRow y : ZMod 8) := huinj huu
  have hcolZ : (muNegThreeCellCol x : ZMod 8) =
      (muNegThreeCellCol y : ZMod 8) := hvinj hvv
  have hrowx : muNegThreeCellRow x < 8 := by
    unfold muNegThreeCellRow
    omega
  have hrowy : muNegThreeCellRow y < 8 := by
    unfold muNegThreeCellRow
    omega
  have hcolx : muNegThreeCellCol x < 8 := Nat.mod_lt _ (by norm_num)
  have hcoly : muNegThreeCellCol y < 8 := Nat.mod_lt _ (by norm_num)
  have hrow : muNegThreeCellRow x = muNegThreeCellRow y := by
    have hz := congrArg ZMod.val hrowZ
    simpa [ZMod.val_natCast_of_lt hrowx,
      ZMod.val_natCast_of_lt hrowy] using hz
  have hcol : muNegThreeCellCol x = muNegThreeCellCol y := by
    have hz := congrArg ZMod.val hcolZ
    simpa [ZMod.val_natCast_of_lt hcolx,
      ZMod.val_natCast_of_lt hcoly] using hz
  have hxid : muNegThreeCellRow x * 8 + muNegThreeCellCol x = x := by
    simpa [muNegThreeCellRow, muNegThreeCellCol, Nat.mul_comm] using
      Nat.div_add_mod x 8
  have hyid : muNegThreeCellRow y * 8 + muNegThreeCellCol y = y := by
    simpa [muNegThreeCellRow, muNegThreeCellCol, Nat.mul_comm] using
      Nat.div_add_mod y 8
  omega

/-- The graph hit relation satisfies the finite socket's hit-activity
field. -/
theorem muNegThreeGraph_hit_active
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (s : V → ℤ) (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ x y, (x, y) ∈ muNegThreeHitPairs →
      muNegThreeOwnerHitRel G c u v x y = true →
      muNegThreeOwnerActive (muNegThreeCrossDefectRel G c s u v) x = true ∧
        muNegThreeOwnerActive (muNegThreeCrossDefectRel G c s u v) y = true := by
  intro x y _hkey hX
  obtain ⟨z, w, hx, hy, _hzw⟩ :=
    (muNegThreeOwnerHitRel_eq_true G c u v x y).mp hX
  constructor
  · rw [muNegThreeOwnerActive_graph_iff]
    intro hD
    exact muNegThreeOwnerVertex_not_defect G c hfree a b hab u v
      hurange hvrange hx hD.2
  · rw [muNegThreeOwnerActive_graph_iff]
    intro hD
    exact muNegThreeOwnerVertex_not_defect G c hfree a b hab u v
      hurange hvrange hy hD.2

/-- Intersecting cross cells cannot share a common adjacent owner. -/
theorem muNegThreeGraph_c4_intersecting
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp) :
    ∀ a b g, a < b → b < 64 → g < 64 →
      g ≠ a → g ≠ b →
      (muNegThreeCellRow a = muNegThreeCellRow b ∨
        muNegThreeCellCol a = muNegThreeCellCol b) →
      (min a g, max a g) ∈ muNegThreeHitPairs →
      (min b g, max b g) ∈ muNegThreeHitPairs →
      muNegThreeOwnerHitRel G c u v (min a g) (max a g) = true →
      muNegThreeOwnerHitRel G c u v (min b g) (max b g) = true → False := by
  intro a b g hab hb64 hg64 _hga _hgb hcoord _hkag _hkbg hXag hXbg
  have hit_decode {x y : Nat}
      (hX : muNegThreeOwnerHitRel G c u v (min x y) (max x y) = true) :
      ∃ tx ty, MuNegThreeOwnerVertex G c u v x tx ∧
        MuNegThreeOwnerVertex G c u v y ty ∧ G.Adj tx ty := by
    obtain ⟨z, w, hz, hw, hzw⟩ :=
      (muNegThreeOwnerHitRel_eq_true G c u v (min x y) (max x y)).mp hX
    rcases le_total x y with hxy | hyx
    · have hz' : MuNegThreeOwnerVertex G c u v x z := by
        rwa [Nat.min_eq_left hxy] at hz
      have hw' : MuNegThreeOwnerVertex G c u v y w := by
        rwa [Nat.max_eq_right hxy] at hw
      exact ⟨z, w, hz', hw', hzw⟩
    · have hw' : MuNegThreeOwnerVertex G c u v x w := by
        rwa [Nat.max_eq_left hyx] at hw
      have hz' : MuNegThreeOwnerVertex G c u v y z := by
        rwa [Nat.min_eq_right hyx] at hz
      exact ⟨w, z, hw', hz', hzw.symm⟩
  obtain ⟨za, zg, ha, hg, hazg⟩ := hit_decode hXag
  obtain ⟨zb, zg', hb, hg', hbzg⟩ := hit_decode hXbg
  have hzgeq : zg = zg' := muNegThreeOwnerVertex_unique G c hfree ca cb
    hcab u v hurange hvrange g hg hg'
  subst zg'
  have hzab : za ≠ zb := by
    intro hz
    have := muNegThreeOwnerVertex_inj G c hfree hreg hcard hsize ca cb
      hcab u v huinj hvinj hurange hvrange (by omega) hb64 ha (hz ▸ hb)
    omega
  rcases hcoord with hrow | hcol
  · let q := (muNegThreeOwnerEndpoints G c u v a).1
    have hqb : q = (muNegThreeOwnerEndpoints G c u v b).1 := by
      simp [q, muNegThreeOwnerEndpoints, hrow]
    have hzbq : G.Adj zb q := by rw [hqb]; exact hb.2.1.symm
    have heq := commonServer_unique G hfree hzab
      ha.2.1.symm hzbq hazg hbzg
    have hqmem : q ∈ c.supp := by
      exact (u (muNegThreeCellRow a : ZMod 8)).2
    exact hg.1 (heq ▸ hqmem)
  · let q := (muNegThreeOwnerEndpoints G c u v a).2
    have hqb : q = (muNegThreeOwnerEndpoints G c u v b).2 := by
      simp [q, muNegThreeOwnerEndpoints, hcol]
    have hzbq : G.Adj zb q := by rw [hqb]; exact hb.2.2.symm
    have heq := commonServer_unique G hfree hzab
      ha.2.2.symm hzbq hazg hbzg
    have hqmem : q ∈ c.supp := by
      exact (v (muNegThreeCellCol a : ZMod 8)).2
    exact hg.1 (heq ▸ hqmem)

/-- Two disjoint cross cells cannot have two distinct common adjacent
owners. -/
theorem muNegThreeGraph_c4_no_two
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp) :
    ∀ a b g h, a < b → b < 64 → g < 64 → h < 64 →
      g ≠ h → g ≠ a → g ≠ b → h ≠ a → h ≠ b →
      muNegThreeCellRow a ≠ muNegThreeCellRow b →
      muNegThreeCellCol a ≠ muNegThreeCellCol b →
      (min a g, max a g) ∈ muNegThreeHitPairs →
      (min b g, max b g) ∈ muNegThreeHitPairs →
      (min a h, max a h) ∈ muNegThreeHitPairs →
      (min b h, max b h) ∈ muNegThreeHitPairs →
      muNegThreeOwnerHitRel G c u v (min a g) (max a g) = true →
      muNegThreeOwnerHitRel G c u v (min b g) (max b g) = true →
      muNegThreeOwnerHitRel G c u v (min a h) (max a h) = true →
      muNegThreeOwnerHitRel G c u v (min b h) (max b h) = true → False := by
  intro a b g h hab hb64 hg64 hh64 hgh _ _ _ _ _ _ _ _ _ _
    hXag hXbg hXah hXbh
  have hit_decode {x y : Nat}
      (hX : muNegThreeOwnerHitRel G c u v (min x y) (max x y) = true) :
      ∃ tx ty, MuNegThreeOwnerVertex G c u v x tx ∧
        MuNegThreeOwnerVertex G c u v y ty ∧ G.Adj tx ty := by
    obtain ⟨z, w, hz, hw, hzw⟩ :=
      (muNegThreeOwnerHitRel_eq_true G c u v (min x y) (max x y)).mp hX
    rcases le_total x y with hxy | hyx
    · have hz' : MuNegThreeOwnerVertex G c u v x z := by
        rwa [Nat.min_eq_left hxy] at hz
      have hw' : MuNegThreeOwnerVertex G c u v y w := by
        rwa [Nat.max_eq_right hxy] at hw
      exact ⟨z, w, hz', hw', hzw⟩
    · have hw' : MuNegThreeOwnerVertex G c u v x w := by
        rwa [Nat.max_eq_left hyx] at hw
      have hz' : MuNegThreeOwnerVertex G c u v y z := by
        rwa [Nat.min_eq_right hyx] at hz
      exact ⟨w, z, hw', hz', hzw.symm⟩
  obtain ⟨ta, tg, ha, hg, hag⟩ := hit_decode hXag
  obtain ⟨tb, tg', hb, hg', hbg⟩ := hit_decode hXbg
  obtain ⟨ta', th, ha', hh, hah⟩ := hit_decode hXah
  obtain ⟨tb', th', hb', hh', hbh⟩ := hit_decode hXbh
  have hta : ta = ta' := muNegThreeOwnerVertex_unique G c hfree ca cb
    hcab u v hurange hvrange a ha ha'
  have htb : tb = tb' := muNegThreeOwnerVertex_unique G c hfree ca cb
    hcab u v hurange hvrange b hb hb'
  have htg : tg = tg' := muNegThreeOwnerVertex_unique G c hfree ca cb
    hcab u v hurange hvrange g hg hg'
  have hth : th = th' := muNegThreeOwnerVertex_unique G c hfree ca cb
    hcab u v hurange hvrange h hh hh'
  subst ta'
  subst tb'
  subst tg'
  subst th'
  have htab : ta ≠ tb := by
    intro heq
    have hab' := muNegThreeOwnerVertex_inj G c hfree hreg hcard hsize ca cb
      hcab u v huinj hvinj hurange hvrange (by omega) hb64 ha (heq ▸ hb)
    omega
  have htgh : tg = th := commonServer_unique G hfree htab hag hbg hah hbh
  have hgh' := muNegThreeOwnerVertex_inj G c hfree hreg hcard hsize ca cb
    hcab u v huinj hvinj hurange hvrange hg64 hh64 hg (htgh ▸ hh)
  exact hgh hgh'

/-- The exact residual after the graph-generic owner geometry is removed:
four defect-algebra fields and the two service fields. -/
structure MuNegThreeOneTwoGraphResidualSemantics
    (fwd : Bool) (phase : Nat) (D X : Nat → Nat → Bool) : Prop where
  fixed : ∀ i j, i < 8 → j < 8 → i % 2 == j % 2 →
    D i j = (j == muNegThreePhi fwd phase i)
  opposite_rows : ∀ i, i < 8 →
    (((List.range 8).filter fun j => !(i % 2 == j % 2)).countP
      fun j => D i j) = 1
  opposite_columns : ∀ j, j < 8 →
    (((List.range 8).filter fun i => !(i % 2 == j % 2)).countP
      fun i => D i j) = 1
  intertwine : ∀ i j, i < 8 → j < 8 →
    (cond (D ((i + 7) % 8) j) 1 0) +
        (cond (D ((i + 1) % 8) j) 1 0) =
      (cond (D i ((j + 1) % 8)) 1 0) +
        (cond (D i ((j + 7) % 8)) 1 0)
  service_exists : ∀ a, a < 64 → muNegThreeOwnerActive D a = true →
    ∀ (onRow : Bool) t,
      (if onRow then muNegThreeOffsetOne (muNegThreeCellRow a) t
        else muNegThreeOffsetOne (muNegThreeCellCol a) t) = false →
      ∃ b, b < 64 ∧ b ≠ a ∧
        (if onRow then muNegThreeCellRow b = t
          else muNegThreeCellCol b = t) ∧
        (min a b, max a b) ∈ muNegThreeHitPairs ∧
        X (min a b) (max a b) = true
  service_unique : ∀ a, a < 64 → muNegThreeOwnerActive D a = true →
    ∀ (onRow : Bool) t,
      (if onRow then muNegThreeOffsetOne (muNegThreeCellRow a) t
        else muNegThreeOffsetOne (muNegThreeCellCol a) t) = false →
      ∀ b d, b < 64 → b ≠ a →
        (if onRow then muNegThreeCellRow b = t
          else muNegThreeCellCol b = t) →
        (min a b, max a b) ∈ muNegThreeHitPairs →
        X (min a b) (max a b) = true →
        d < 64 → d ≠ a →
        (if onRow then muNegThreeCellRow d = t
          else muNegThreeCellCol d = t) →
        (min a d, max a d) ∈ muNegThreeHitPairs →
        X (min a d) (max a d) = true → b = d

/-- Assemble the complete finite semantics from the exact algebra/service
residual and the graph-generic owner geometry proved above. -/
theorem muNegThreeGraph_finiteSemantics
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (s : V → ℤ) (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp)
    {fwd : Bool} {phase : Nat}
    (hres : MuNegThreeOneTwoGraphResidualSemantics fwd phase
      (muNegThreeCrossDefectRel G c s u v)
      (muNegThreeOwnerHitRel G c u v)) :
    MuNegThreeOneTwoFiniteSemantics fwd phase
      (muNegThreeCrossDefectRel G c s u v)
      (muNegThreeOwnerHitRel G c u v) where
  fixed := hres.fixed
  opposite_rows := hres.opposite_rows
  opposite_columns := hres.opposite_columns
  intertwine := hres.intertwine
  hit_active := muNegThreeGraph_hit_active G c hfree ca cb hcab s u v
    hurange hvrange
  service_exists := hres.service_exists
  service_unique := hres.service_unique
  c4_intersecting := muNegThreeGraph_c4_intersecting G c hfree hreg hcard
    hsize ca cb hcab u v huinj hvinj hurange hvrange
  c4_no_two := muNegThreeGraph_c4_no_two G c hfree hreg hcard hsize ca cb
    hcab u v huinj hvinj hurange hvrange

/-- Graph-facing h312 contradiction, reduced to the explicit six-field
residual above. -/
theorem muNegThreeGraph_false_of_residual
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (s : V → ℤ) (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp)
    {fwd : Bool} {phase : Nat}
    (hphase : phase = 0 ∨ phase = 2 ∨ phase = 4 ∨ phase = 6)
    (hres : MuNegThreeOneTwoGraphResidualSemantics fwd phase
      (muNegThreeCrossDefectRel G c s u v)
      (muNegThreeOwnerHitRel G c u v)) : False :=
  muNegThreeOneTwoFiniteSemantics_false hphase
    (muNegThreeGraph_finiteSemantics G c hfree hreg hcard hsize ca cb hcab
      s u v huinj hvinj hurange hvrange hres)

end StructuralFields

end

end Erdos85

#print axioms Erdos85.muNegThreeOwnerActive_graph_iff
#print axioms Erdos85.muNegThreeOwnerHitRel_comm
#print axioms Erdos85.muNegThreeOwnerHitRel_witness
#print axioms Erdos85.muNegThreeGraph_hit_active
#print axioms Erdos85.muNegThreeGraph_c4_intersecting
#print axioms Erdos85.muNegThreeGraph_c4_no_two
#print axioms Erdos85.muNegThreeGraph_false_of_residual
