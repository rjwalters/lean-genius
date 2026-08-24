import Proofs.Erdos85DyadicStoppingSupportGlobalSqueeze

/-!
# Shore balance from divisible occupancies

If all line occupancies of a nonempty shore are divisible by `a`, then the
`q` neighbor blocks through a shore point each contain at least `a-1` other
shore points.  C4-freeness makes those blocks disjoint, forcing the sharp
Moore-type lower bound `q(a-1)+1 ≤ |S|`.  Applying the same argument to the
complement gives a strong location theorem at the final dyadic scale.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Divisible positive occupancies force a large shore. -/
theorem c4Free_regular_shore_card_ge_of_occupancy_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (ha : 0 < a) (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (hS : S.Nonempty)
    (hdiv : ∀ v, a ∣ (G.neighborFinset v ∩ S).card) :
    q * (a - 1) + 1 ≤ S.card := by
  obtain ⟨x, hxS⟩ := hS
  have hxNot : x ∉ S.erase x := by simp
  have hsum := c4Free_sum_neighbor_block_cards_eq_common_targets
    G hfree x (S.erase x) hxNot
  dsimp only at hsum
  have hrow : ∀ w ∈ G.neighborFinset x,
      a - 1 ≤ (G.neighborFinset w ∩ S.erase x).card := by
    intro w hw
    have hxw : x ∈ G.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hw
    have hxInter : x ∈ G.neighborFinset w ∩ S :=
      Finset.mem_inter.mpr ⟨hxw, hxS⟩
    have hpos : 0 < (G.neighborFinset w ∩ S).card :=
      Finset.card_pos.mpr ⟨x, hxInter⟩
    obtain ⟨t, ht⟩ := hdiv w
    have htpos : 0 < t := by
      rw [ht] at hpos
      exact Nat.pos_of_mul_pos_left hpos
    have hale : a ≤ (G.neighborFinset w ∩ S).card := by
      rw [ht]
      calc
        a = a * 1 := by simp
        _ ≤ a * t := Nat.mul_le_mul_left a htpos
    rw [Finset.inter_erase, Finset.card_erase_of_mem hxInter]
    omega
  have hblocks : q * (a - 1) ≤
      ∑ w ∈ G.neighborFinset x,
        (G.neighborFinset w ∩ S.erase x).card := by
    calc
      q * (a - 1) = ∑ _w ∈ G.neighborFinset x, (a - 1) := by
        simp [G.card_neighborFinset_eq_degree, hreg]
      _ ≤ ∑ w ∈ G.neighborFinset x,
          (G.neighborFinset w ∩ S.erase x).card := by
        apply Finset.sum_le_sum
        intro w hw
        exact hrow w hw
  have hfilterLe :
      ((S.erase x).filter fun y =>
        (G.neighborFinset x ∩ G.neighborFinset y).Nonempty).card ≤
        (S.erase x).card := Finset.card_filter_le _ _
  have hprodLe : q * (a - 1) ≤ (S.erase x).card := by
    calc
      q * (a - 1) ≤ ∑ w ∈ G.neighborFinset x,
          (G.neighborFinset w ∩ S.erase x).card := hblocks
      _ = ((S.erase x).filter fun y =>
          (G.neighborFinset x ∩ G.neighborFinset y).Nonempty).card := hsum
      _ ≤ (S.erase x).card := hfilterLe
  rw [Finset.card_erase_of_mem hxS] at hprodLe
  exact (Nat.le_sub_iff_add_le (Finset.card_pos.mpr ⟨x, hxS⟩)).mp hprodLe

/-- A shore and its complement both satisfy the divisible-occupancy lower
bound whenever `a` divides the regular degree. -/
theorem c4Free_regular_shore_compl_card_ge_of_occupancy_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (ha : 0 < a) (hqa : a ∣ q) (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (hdiv : ∀ v, a ∣ (G.neighborFinset v ∩ S).card) :
    q * (a - 1) + 1 ≤ S.card ∧
      q * (a - 1) + 1 ≤ (Sᶜ : Finset V).card := by
  constructor
  · exact c4Free_regular_shore_card_ge_of_occupancy_dvd
      G hfree ha hreg S hS hdiv
  · exact c4Free_regular_shore_card_ge_of_occupancy_dvd
      G hfree ha hreg (Sᶜ : Finset V) hSc
        (dvd_complement_occupancy G hreg S ha hqa hdiv)

/-- At the final dyadic scale `a=q/2`, every nontrivial divisible shore is
confined to a width-`2q-2` band around half of the square-order vertex set. -/
theorem c4Free_binarySquare_finalDivisible_shore_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (ha : 0 < a) (hqa : q = 2 * a) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (hdiv : ∀ v, a ∣ (G.neighborFinset v ∩ S).card) :
    q * (a - 1) + 1 ≤ S.card ∧
      S.card ≤ q * q - (q * (a - 1) + 1) := by
  have hqaDvd : a ∣ q := ⟨2, by rw [hqa]; ring⟩
  have hb := c4Free_regular_shore_compl_card_ge_of_occupancy_dvd
    G hfree ha hqaDvd hreg S hS hSc hdiv
  refine ⟨hb.1, ?_⟩
  rw [Finset.card_compl, hcard] at hb
  omega

end

end Erdos85

#print axioms Erdos85.c4Free_regular_shore_card_ge_of_occupancy_dvd
#print axioms Erdos85.c4Free_binarySquare_finalDivisible_shore_balance
