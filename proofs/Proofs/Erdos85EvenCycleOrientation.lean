import Proofs.Erdos85BinaryCycleIntertwiner
import Proofs.Erdos85SecondOrderEvenDefect

/-!
# C4-free rigidity of the two checkerboard orientations on an even cycle

For an even cyclic self-block, the d'Alembert coordinates split into two
parity classes.  On same-parity pairs the block is circulant; on
opposite-parity pairs it is reverse-circulant.  The two sectors cannot both
carry an edge in a `C4`-free graph: an internal edge and a cross-parity edge
translate to the opposite sides of a four-cycle.

This file isolates that geometric argument.  The remaining input needed for
the full even-cycle orientation theorem is the checkerboard invariance itself.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- On an even cyclic group, the image of doubling is exactly the kernel of
reduction modulo two. -/
theorem zmod_mem_range_two_mul_iff_castHom_eq_zero
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r) (z : ZMod r) :
    z ∈ Set.range (fun t : ZMod r ↦ 2 * t) ↔
      ZMod.castHom h2r (ZMod 2) z = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [map_mul]
    have htwo : ZMod.castHom h2r (ZMod 2) (2 : ZMod r) = 0 := by
      rw [map_ofNat]
      exact ZMod.natCast_self 2
    rw [htwo, zero_mul]
  · intro hz
    have hzval : ((z.val : ℕ) : ZMod 2) = 0 := by
      simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hz
    obtain ⟨k, hk⟩ := ZMod.natCast_eq_zero_iff_even.mp hzval
    refine ⟨(k : ZMod r), ?_⟩
    rw [← ZMod.natCast_zmod_val z, hk]
    push_cast
    ring

/-- **Mixed checkerboard orientations force a four-cycle.**  Suppose the
same-parity part of a cyclic adjacency block depends only on coordinate
difference, while the opposite-parity part depends only on coordinate sum.
In a `C4`-free graph, at most one of those two parts can contain an edge. -/
theorem no_edges_in_one_checkerboard_sector
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r] (h2r : 2 ∣ r)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod r → V) (hu : Function.Injective u)
    (hcirc : ∀ {x y x' y' : ZMod r},
      ZMod.castHom h2r (ZMod 2) (y - x) = 0 →
      y - x = y' - x' →
      (G.Adj (u x) (u y) ↔ G.Adj (u x') (u y')))
    (hrev : ∀ {x y x' y' : ZMod r},
      ZMod.castHom h2r (ZMod 2) (y - x) ≠ 0 →
      y + x = y' + x' →
      (G.Adj (u x) (u y) ↔ G.Adj (u x') (u y'))) :
    (∀ x y : ZMod r,
        ZMod.castHom h2r (ZMod 2) (y - x) = 0 →
        ¬ G.Adj (u x) (u y)) ∨
      (∀ x y : ZMod r,
        ZMod.castHom h2r (ZMod 2) (y - x) ≠ 0 →
        ¬ G.Adj (u x) (u y)) := by
  classical
  let φ : ZMod r →+* ZMod 2 := ZMod.castHom h2r (ZMod 2)
  by_contra hnot
  push Not at hnot
  obtain ⟨⟨x, y, hxy0, hxy⟩, ⟨a, b, hab0, hab⟩⟩ := hnot
  let s : ZMod r := a + b
  let c : ZMod r := s - y
  let e : ZMod r := s - x
  have hφxy : φ y = φ x := by
    have h := hxy0
    simp only [map_sub] at h
    linear_combination h
  have hφab : φ a + φ b ≠ 0 := by
    intro hz
    apply hab0
    simp only [map_sub]
    change φ b - φ a = 0
    have hneg (z : ZMod 2) : -z = z := by
      fin_cases z <;> decide
    rw [sub_eq_add_neg, hneg]
    simpa [add_comm] using hz
  have hxe0 : φ (e - x) ≠ 0 := by
    dsimp only [e, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ x)
  have hyc0 : φ (c - y) ≠ 0 := by
    dsimp only [c, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ y)
  have hce0 : φ (e - c) = 0 := by
    dsimp only [e, c]
    have hdiff : e - c = y - x := by ring
    rw [hdiff]
    exact hxy0
  have hcx0 : φ (c - x) ≠ 0 := by
    dsimp only [c, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ x) + hφxy
  have hey0 : φ (e - y) ≠ 0 := by
    dsimp only [e, s]
    simp only [map_sub, map_add]
    intro hz
    apply hφab
    have htwo (z : ZMod 2) : z + z = 0 := by
      fin_cases z <;> decide
    linear_combination hz + htwo (φ y) - hφxy
  have hxe : G.Adj (u x) (u e) := by
    apply (hrev hab0 (by dsimp [e, s]; ring)).mp hab
  have hyc : G.Adj (u y) (u c) := by
    apply (hrev hab0 (by dsimp [c, s]; ring)).mp hab
  have hce : G.Adj (u c) (u e) := by
    apply (hcirc hxy0 (by dsimp [c, e]; ring)).mp hxy
  have hxc : x ≠ c := by
    intro h
    apply hcx0
    rw [← h, sub_self, map_zero]
  have hye : y ≠ e := by
    intro h
    apply hey0
    rw [← h, sub_self, map_zero]
  have hucx : u c ≠ u x := fun h ↦ hxc (hu h).symm
  have huyue : u y ≠ u e := fun h ↦ hye (hu h)
  have hy_mem : u y ∈ G.neighborFinset (u x) ∩
      G.neighborFinset (u c) := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxy, hyc.symm⟩
  have he_mem : u e ∈ G.neighborFinset (u x) ∩
      G.neighborFinset (u c) := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxe, hce⟩
  have htwo : 2 ≤ (G.neighborFinset (u x) ∩
      G.neighborFinset (u c)).card := by
    have hsub : ({u y, u e} : Finset V) ⊆
        G.neighborFinset (u x) ∩ G.neighborFinset (u c) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hy_mem
      · exact he_mem
    have hcard : ({u y, u e} : Finset V).card = 2 := by
      simp [huyue]
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hone := common_le_one_of_not_containsC4 hfree (u x) (u c) hucx.symm
  omega

end

end Erdos85
