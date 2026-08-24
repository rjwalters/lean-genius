import Proofs.Erdos85DyadicStoppingSupport

/-!
# Pointwise packing forced by a dyadic stopping support

A marked level-`j` line through a shore point contains at least `2^j`
shore points, while an unmarked line contains at least `2^(j+1)`.  The
C4-free disjoint neighbor blocks turn these local minima into the exact
pointwise service inequality behind the dyadic Baer audit.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A positive multiple of `a` has size at least `a`; if its quotient is
not odd, it is in fact at least `2a`. -/
theorem dyadic_occupancy_marked_or_double
    {a n : ℕ} (ha : 0 < a) (hn : 0 < n) (hdiv : a ∣ n) :
    (Odd (n / a) ∧ a ≤ n) ∨ (¬Odd (n / a) ∧ 2 * a ≤ n) := by
  obtain ⟨t, ht⟩ := hdiv
  have htpos : 0 < t := by
    by_contra h
    have ht0 : t = 0 := by omega
    simp [ht, ht0] at hn
  have hquot : n / a = t := by
    rw [ht]
    exact Nat.mul_div_cancel_left t ha
  by_cases htOdd : Odd t
  · left
    refine ⟨by simpa [hquot], ?_⟩
    rw [ht]
    nlinarith
  · right
    have htEven : Even t := Nat.not_odd_iff_even.mp htOdd
    obtain ⟨u, hu⟩ := htEven
    refine ⟨by rwa [hquot], ?_⟩
    rw [ht, hu]
    simpa [Nat.mul_comm] using
      (Nat.mul_le_mul_left a (show 2 ≤ u + u by omega))

/-- **Dyadic stopping-support service inequality (audit (45)).**  Put
`a=2^j` and let `B` be the level-`j` marked-line support.  For every shore
point `p`, C4-freeness forces

`(2a-1)q + 1 ≤ |S| + a |N(p)∩B|`.

This is the subtraction-safe form of
`|S| ≥ (2a-1)q+1-a|N(p)∩B|`. -/
theorem c4Free_dyadicStoppingSupport_pointwise_service
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (p : V) (hpS : p ∈ S) :
    (2 * 2 ^ j - 1) * q + 1 ≤
      S.card + 2 ^ j *
        (G.neighborFinset p ∩ dyadicOccupancySupport G S j).card := by
  let a := 2 ^ j
  let B := dyadicOccupancySupport G S j
  have ha : 0 < a := by simp [a]
  have hpNot : p ∉ S.erase p := by simp
  have hblocks := c4Free_sum_neighbor_block_cards_eq_common_targets
    G hfree p (S.erase p) hpNot
  dsimp only at hblocks
  have hrow (w : V) (hw : w ∈ G.neighborFinset p) :
      (2 * a - 1) ≤
        (G.neighborFinset w ∩ S.erase p).card +
          a * (if w ∈ B then 1 else 0) := by
    have hpw : p ∈ G.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hw
    have hpInter : p ∈ G.neighborFinset w ∩ S :=
      Finset.mem_inter.mpr ⟨hpw, hpS⟩
    have hnpos : 0 < (G.neighborFinset w ∩ S).card :=
      Finset.card_pos.mpr ⟨p, hpInter⟩
    have herase : (G.neighborFinset w ∩ S.erase p).card =
        (G.neighborFinset w ∩ S).card - 1 := by
      rw [Finset.inter_erase, Finset.card_erase_of_mem hpInter]
    rcases dyadic_occupancy_marked_or_double ha hnpos (hdiv w) with
        ⟨hodd, halower⟩ | ⟨hnotOdd, hdouble⟩
    · have hwB : w ∈ B := by
        simp [B, dyadicOccupancySupport, a, hodd]
      rw [herase, if_pos hwB]
      have ha1 : 1 ≤ a := by omega
      omega
    · have hwNotB : w ∉ B := by
        simp [B, dyadicOccupancySupport, a, hnotOdd]
      rw [herase, if_neg hwNotB]
      omega
  have hsumLower :
      (G.neighborFinset p).card * (2 * a - 1) ≤
        (∑ w ∈ G.neighborFinset p,
          (G.neighborFinset w ∩ S.erase p).card) +
        a * (G.neighborFinset p ∩ B).card := by
    calc
      (G.neighborFinset p).card * (2 * a - 1) =
          ∑ w ∈ G.neighborFinset p, (2 * a - 1) := by simp
      _ ≤ ∑ w ∈ G.neighborFinset p,
          ((G.neighborFinset w ∩ S.erase p).card +
            a * (if w ∈ B then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro w hw
        exact hrow w hw
      _ = (∑ w ∈ G.neighborFinset p,
          (G.neighborFinset w ∩ S.erase p).card) +
          a * (G.neighborFinset p ∩ B).card := by
        rw [Finset.sum_add_distrib]
        congr 1
        calc
          (∑ w ∈ G.neighborFinset p,
              a * (if w ∈ B then 1 else 0)) =
              a * ∑ w ∈ G.neighborFinset p,
                (if w ∈ B then 1 else 0) := by
                  rw [Finset.mul_sum]
          _ = a * (G.neighborFinset p ∩ B).card := by
            congr 1
            rw [← Finset.card_filter]
            apply congrArg Finset.card
            ext w
            simp [and_comm]
  have hblockLe :
      (∑ w ∈ G.neighborFinset p,
        (G.neighborFinset w ∩ S.erase p).card) ≤ S.card - 1 := by
    rw [hblocks]
    calc
      ((S.erase p).filter fun y =>
          (G.neighborFinset p ∩ G.neighborFinset y).Nonempty).card ≤
          (S.erase p).card := Finset.card_filter_le _ _
      _ = S.card - 1 := Finset.card_erase_of_mem hpS
  dsimp [a, B] at hsumLower ⊢
  rw [hreg p] at hsumLower
  have hsumLower' :
      (2 * 2 ^ j - 1) * q ≤
        (∑ w ∈ G.neighborFinset p,
          (G.neighborFinset w ∩ S.erase p).card) +
        2 ^ j *
          (G.neighborFinset p ∩ dyadicOccupancySupport G S j).card := by
    simpa [Nat.mul_comm] using hsumLower
  have hpCard : 1 ≤ S.card := Finset.card_pos.mpr ⟨p, hpS⟩
  omega

end

end Erdos85

#print axioms Erdos85.dyadic_occupancy_marked_or_double
#print axioms Erdos85.c4Free_dyadicStoppingSupport_pointwise_service
