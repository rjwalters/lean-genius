import Proofs.Erdos85DyadicStoppingSupportPacking
import Proofs.Erdos85BranchDeficitSymmetry

/-!
# Global two-shore squeeze for a dyadic stopping support

Summing the pointwise service law over a shore and its complement, then
using exact incidence balance into their common marked support, produces a
single global inequality.  This is the integrated form of the packing
constraints in the dyadic Baer audit.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Summed form of the pointwise stopping-support service inequality. -/
theorem c4Free_dyadicStoppingSupport_shore_service_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    ((2 * 2 ^ j - 1) * q + 1) * S.card ≤
      S.card * S.card + 2 ^ j *
        (∑ p ∈ S,
          (G.neighborFinset p ∩ dyadicOccupancySupport G S j).card) := by
  calc
    ((2 * 2 ^ j - 1) * q + 1) * S.card =
        ∑ _p ∈ S, ((2 * 2 ^ j - 1) * q + 1) := by
      simp [Nat.mul_comm]
    _ ≤ ∑ p ∈ S, (S.card + 2 ^ j *
        (G.neighborFinset p ∩ dyadicOccupancySupport G S j).card) := by
      apply Finset.sum_le_sum
      intro p hp
      exact c4Free_dyadicStoppingSupport_pointwise_service
        G hfree hreg S j hdiv p hp
    _ = S.card * S.card + 2 ^ j *
        (∑ p ∈ S,
          (G.neighborFinset p ∩ dyadicOccupancySupport G S j).card) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp

/-- Divisibility of shore occupancies transfers to the complementary shore
when the divisor also divides the regular degree. -/
theorem dvd_complement_occupancy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q a : ℕ} (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (ha : 0 < a) (hqa : a ∣ q)
    (hdiv : ∀ v, a ∣ (G.neighborFinset v ∩ S).card) :
    ∀ v, a ∣ (G.neighborFinset v ∩ (Sᶜ : Finset V)).card := by
  intro v
  have hpartition :
      (G.neighborFinset v ∩ S).card +
        (G.neighborFinset v ∩ (Sᶜ : Finset V)).card = q := by
    rw [← Finset.card_union_of_disjoint]
    · rw [← Finset.inter_union_distrib_left, Finset.union_compl,
        Finset.inter_univ, G.card_neighborFinset_eq_degree, hreg]
    · exact Finset.disjoint_left.mpr fun x hxS hxSc =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hxSc).2)
          (Finset.mem_inter.mp hxS).2
  obtain ⟨Q, hQ⟩ := hqa
  obtain ⟨t, ht⟩ := hdiv v
  have htQ : t ≤ Q := by
    rw [ht, hQ] at hpartition
    have : a * t ≤ a * Q := by omega
    exact Nat.le_of_mul_le_mul_left this ha
  refine ⟨Q - t, ?_⟩
  calc
    (G.neighborFinset v ∩ (Sᶜ : Finset V)).card =
        q - (G.neighborFinset v ∩ S).card := by omega
    _ = a * Q - a * t := by rw [hQ, ht]
    _ = a * (Q - t) := (Nat.mul_sub_left_distrib a Q t).symm

/-- Total incidence from a shore and its complement into a fixed line set
is exactly `q|B|`. -/
theorem regular_shore_compl_incidence_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q)
    (S B : Finset V) :
    (∑ p ∈ S, (G.neighborFinset p ∩ B).card) +
      (∑ p ∈ (Sᶜ : Finset V), (G.neighborFinset p ∩ B).card) =
      q * B.card := by
  rw [sum_card_neighbor_inter_comm G S B,
    sum_card_neighbor_inter_comm G (Sᶜ : Finset V) B,
    ← Finset.sum_add_distrib]
  calc
    (∑ b ∈ B, ((G.neighborFinset b ∩ S).card +
        (G.neighborFinset b ∩ (Sᶜ : Finset V)).card)) =
        ∑ _b ∈ B, q := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [← Finset.card_union_of_disjoint]
      · rw [← Finset.inter_union_distrib_left, Finset.union_compl,
          Finset.inter_univ, G.card_neighborFinset_eq_degree, hreg]
      · exact Finset.disjoint_left.mpr fun x hxS hxSc =>
          (Finset.mem_compl.mp (Finset.mem_inter.mp hxSc).2)
            (Finset.mem_inter.mp hxS).2
    _ = q * B.card := by simp [Nat.mul_comm]

/-- **Global dyadic stopping-support squeeze (audit (48)--(49)).**  For a
square-order regular graph, the common marked support of a shore and its
complement satisfies

`C q² ≤ |S|² + |Sᶜ|² + 2^j q |B|`,

where `C=(2·2^j-1)q+1`. -/
theorem c4Free_binarySquare_dyadicStoppingSupport_global_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    ((2 * 2 ^ j - 1) * q + 1) * (q * q) ≤
      S.card * S.card + (Sᶜ : Finset V).card * (Sᶜ : Finset V).card +
        2 ^ j * q * (dyadicOccupancySupport G S j).card := by
  let B := dyadicOccupancySupport G S j
  have hajq : 2 ^ j ∣ q := by
    obtain ⟨u, hu⟩ := hqdiv
    refine ⟨2 * u, ?_⟩
    rw [hu, pow_succ]
    ring
  have hdivc : ∀ v, 2 ^ j ∣
      (G.neighborFinset v ∩ (Sᶜ : Finset V)).card :=
    dvd_complement_occupancy G hreg S (by positivity) hajq hdiv
  have hBcompl : dyadicOccupancySupport G (Sᶜ : Finset V) j = B := by
    exact dyadicOccupancySupport_compl G hreg S j hdiv hqdiv
  have hSsum := c4Free_dyadicStoppingSupport_shore_service_sum
    G hfree hreg S j hdiv
  have hCsum := c4Free_dyadicStoppingSupport_shore_service_sum
    G hfree hreg (Sᶜ : Finset V) j hdivc
  rw [hBcompl] at hCsum
  have hInc := regular_shore_compl_incidence_sum G hreg S B
  have hcardSum : S.card + (Sᶜ : Finset V).card = q * q := by
    rw [Finset.card_compl]
    calc
      S.card + (Fintype.card V - S.card) = Fintype.card V :=
        Nat.add_sub_of_le (Finset.card_le_univ S)
      _ = q * q := hcard
  dsimp [B] at hInc hSsum hCsum ⊢
  calc
    ((2 * 2 ^ j - 1) * q + 1) * (q * q) =
        ((2 * 2 ^ j - 1) * q + 1) * S.card +
          ((2 * 2 ^ j - 1) * q + 1) * (Sᶜ : Finset V).card := by
      rw [← Nat.mul_add, hcardSum]
    _ ≤ (S.card * S.card + 2 ^ j *
          (∑ p ∈ S, (G.neighborFinset p ∩
            dyadicOccupancySupport G S j).card)) +
        ((Sᶜ : Finset V).card * (Sᶜ : Finset V).card + 2 ^ j *
          (∑ p ∈ (Sᶜ : Finset V), (G.neighborFinset p ∩
            dyadicOccupancySupport G S j).card)) :=
      Nat.add_le_add hSsum hCsum
    _ = S.card * S.card + (Sᶜ : Finset V).card * (Sᶜ : Finset V).card +
        2 ^ j * q * (dyadicOccupancySupport G S j).card := by
      calc
        S.card * S.card + 2 ^ j *
              (∑ p ∈ S, (G.neighborFinset p ∩
                dyadicOccupancySupport G S j).card) +
            ((Sᶜ : Finset V).card * (Sᶜ : Finset V).card + 2 ^ j *
              (∑ p ∈ (Sᶜ : Finset V), (G.neighborFinset p ∩
                dyadicOccupancySupport G S j).card)) =
            S.card * S.card +
              (Sᶜ : Finset V).card * (Sᶜ : Finset V).card +
              2 ^ j * ((∑ p ∈ S, (G.neighborFinset p ∩
                dyadicOccupancySupport G S j).card) +
                (∑ p ∈ (Sᶜ : Finset V), (G.neighborFinset p ∩
                  dyadicOccupancySupport G S j).card)) := by ring
        _ = S.card * S.card +
              (Sᶜ : Finset V).card * (Sᶜ : Finset V).card +
              2 ^ j * (q * (dyadicOccupancySupport G S j).card) := by
            rw [hInc]
        _ = S.card * S.card +
              (Sᶜ : Finset V).card * (Sᶜ : Finset V).card +
              2 ^ j * q * (dyadicOccupancySupport G S j).card := by ring

end

end Erdos85

#print axioms Erdos85.c4Free_dyadicStoppingSupport_shore_service_sum
#print axioms Erdos85.regular_shore_compl_incidence_sum
#print axioms Erdos85.c4Free_binarySquare_dyadicStoppingSupport_global_squeeze
