import Proofs.Erdos85OneHighSameMissParity
import Proofs.Erdos85AdjacentBranchNonadjacency

/-! # The structural hexagon forced by a mate-pair miss edge -/

namespace Erdos85

open SimpleGraph

noncomputable section

structure OneHighMateMissHexagon
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) where
  source : {z : V // z ∈ G.neighborSet v}
  u : {z : V // z ∈ G.neighborSet v}
  w : {z : V // z ∈ G.neighborSet v}
  source_ne_u : source ≠ u
  source_ne_w : source ≠ w
  root_edge : G.Adj u.1 w.1
  x : V
  y : V
  a : V
  b : V
  x_mem : x ∈ secondLayerBranch G v source
  y_mem : y ∈ secondLayerBranch G v source
  a_mem : a ∈ secondLayerBranch G v u
  b_mem : b ∈ secondLayerBranch G v w
  xy_edge : G.Adj x y
  ya_edge : G.Adj y a
  au_edge : G.Adj a u.1
  wb_edge : G.Adj w.1 b
  bx_edge : G.Adj b x
  x_not_adj_a : ¬ G.Adj x a
  y_not_adj_b : ¬ G.Adj y b
  a_not_adj_b : ¬ G.Adj a b

/-- Complementary misses at the two endpoints of an internal edge, when the
two missed root branches are adjacent (in particular, are root mates), force
the rim `x-y-a-u-w-b-x` together with its three key nonedges. -/
theorem exists_oneHighMateMissHexagon
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s u w : {z : V // z ∈ G.neighborSet v})
    (hsu : s ≠ u) (hsw : s ≠ w) (huw : G.Adj u.1 w.1)
    {x y : V}
    (hxs : x ∈ secondLayerBranch G v s)
    (hys : y ∈ secondLayerBranch G v s)
    (hxy : G.Adj x y)
    (hxMissU : (G.neighborFinset x ∩
      secondLayerBranch G v u).card = 0)
    (hyMissW : (G.neighborFinset y ∩
      secondLayerBranch G v w).card = 0)
    (hySeesU : (G.neighborFinset y ∩
      secondLayerBranch G v u).card ≠ 0)
    (hxSeesW : (G.neighborFinset x ∩
      secondLayerBranch G v w).card ≠ 0) :
    Nonempty (OneHighMateMissHexagon G v) := by
  obtain ⟨a, ha, b, hb, hya, hxb, hab⟩ :=
    exists_nonadjacent_cross_witnesses_of_different_misses
      G hfree hsu hsw hxs hys hxy hySeesU hxSeesW
  have hau : G.Adj a u.1 :=
    ((G.mem_neighborFinset u.1 a).mp (Finset.mem_sdiff.mp ha).1).symm
  have hwb : G.Adj w.1 b :=
    (G.mem_neighborFinset w.1 b).mp (Finset.mem_sdiff.mp hb).1
  have hxa : ¬ G.Adj x a := by
    intro h
    have hamem : a ∈ G.neighborFinset x ∩
        secondLayerBranch G v u := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x a).mpr h, ha⟩
    have hempty : G.neighborFinset x ∩ secondLayerBranch G v u = ∅ :=
      Finset.card_eq_zero.mp hxMissU
    have hnot : a ∉ G.neighborFinset x ∩ secondLayerBranch G v u := by
      rw [hempty]
      simp
    exact hnot hamem
  have hyb : ¬ G.Adj y b := by
    intro h
    have hbmem : b ∈ G.neighborFinset y ∩
        secondLayerBranch G v w := by
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y b).mpr h, hb⟩
    have hempty : G.neighborFinset y ∩ secondLayerBranch G v w = ∅ :=
      Finset.card_eq_zero.mp hyMissW
    have hnot : b ∉ G.neighborFinset y ∩ secondLayerBranch G v w := by
      rw [hempty]
      simp
    exact hnot hbmem
  exact ⟨⟨s, u, w, hsu, hsw, huw, x, y, a, b,
    hxs, hys, ha, hb, hxy, hya, hau, hwb, hxb.symm,
    hxa, hyb, hab⟩⟩

end

end Erdos85
