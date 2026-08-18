import Proofs.Erdos85BinarySquareSizeTwoSelfSourceLayer

/-! # A bipartition obstruction for self-source two-factors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Suppose `D` contains every cross-part pair except at most one per vertex,
`A` is a two-factor edge-disjoint from `D`, and the distinct-common-neighbor
graph of `A` has no cross-part edge.  Then `A` itself has no cross-part edge.

This isolates the first elementary step in excluding the synchronized
`K_{8,8}`-minus-matching model: a two-factor square root cannot use the sparse
missing cross matching. -/
theorem twoRegular_no_cross_adj_of_commonNeighbor_no_cross
    {W : Type*} [Fintype W] [DecidableEq W]
    (A D : SimpleGraph W) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (side : W → Bool)
    (hdeg : ∀ x, A.degree x = 2)
    (hdisjoint : ∀ {x y}, A.Adj x y → ¬ D.Adj x y)
    (hcrossUnique : ∀ {x y z}, side x ≠ side y → side x ≠ side z →
      ¬ D.Adj x y → ¬ D.Adj x z → y = z)
    (hcommonSame : ∀ {x y}, (distinctCommonNeighborGraph A).Adj x y →
      side x = side y)
    {x y : W} (hxy : A.Adj x y) :
    side x = side y := by
  by_contra hxySide
  have hyMem : y ∈ A.neighborFinset x := (A.mem_neighborFinset x y).mpr hxy
  have hcard : (A.neighborFinset x).card = 2 := by
    rw [A.card_neighborFinset_eq_degree, hdeg]
  have herase : ((A.neighborFinset x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hyMem, hcard]
  have herasePos : 0 < ((A.neighborFinset x).erase y).card := by omega
  obtain ⟨z, hzErase⟩ := Finset.card_pos.mp herasePos
  have hzData := Finset.mem_erase.mp hzErase
  have hxz : A.Adj x z := (A.mem_neighborFinset x z).mp hzData.2
  have hzy : z ≠ y := hzData.1
  have hzSide : side z = side x := by
    by_contra hxzSide
    have hyz := hcrossUnique hxySide (fun h => hxzSide h.symm)
      (hdisjoint hxy) (hdisjoint hxz)
    exact hzy hyz.symm
  have hyzCommon : (distinctCommonNeighborGraph A).Adj y z := by
    exact ⟨hzy.symm, x, hxy, hxz⟩
  have hyzSide : side y = side z := hcommonSame hyzCommon
  exact hxySide (hyzSide.trans hzSide).symm

/-- The distinct-common-neighbor graph of the standard eight-cycle is not
connected: every one of its edges preserves the parity of the cyclic label,
so vertices `0` and `1` lie in different components. -/
theorem not_connected_distinctCommonNeighborGraph_cycleGraph_eight :
    ¬ (distinctCommonNeighborGraph (cycleGraph 8)).Connected := by
  intro hconn
  letI : DecidableRel (distinctCommonNeighborGraph (cycleGraph 8)).Adj :=
    fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ∃ x : Fin 8,
      (cycleGraph 8).Adj x i ∧ (cycleGraph 8).Adj x j))
  have hedge : ∀ {i j : Fin 8},
      (distinctCommonNeighborGraph (cycleGraph 8)).Adj i j →
        i.val % 2 = j.val % 2 := by decide
  have hreach := hconn.preconnected (0 : Fin 8) (1 : Fin 8)
  have hwalk : Relation.ReflTransGen
      (distinctCommonNeighborGraph (cycleGraph 8)).Adj (0 : Fin 8) (1 : Fin 8) :=
    ((distinctCommonNeighborGraph (cycleGraph 8)).reachable_iff_reflTransGen
      (0 : Fin 8) (1 : Fin 8)).mp hreach
  have hparity : Relation.ReflTransGen (fun a b : ℕ => a = b) 0 1 :=
    hwalk.lift (fun i : Fin 8 => i.val % 2) (fun _ _ h => hedge h)
  have : (0 : ℕ) = 1 := by
    simpa only [Relation.reflTransGen_eq_self] using hparity
  omega

end

end Erdos85
