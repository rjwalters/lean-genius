import Proofs.Erdos85DyadicOccupancyStopping
import Proofs.Erdos85GadgetCounting

/-!
# The marked support at a dyadic occupancy stopping level

The first nonzero dyadic digit is packaged as an actual finset of marked
lines.  Its cardinality is even and it is invariant under replacing the
shore by its complement, exactly as required by the Baer stopping argument.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Lines whose shore occupancy has odd quotient after division by `2^j`. -/
def dyadicOccupancySupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (j : ℕ) : Finset V :=
  Finset.univ.filter fun v =>
    Odd ((G.neighborFinset v ∩ S).card / 2 ^ j)

/-- A failure of divisibility at the next digit marks a line. -/
theorem mem_dyadicOccupancySupport_of_dvd_not_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (j : ℕ) (v : V)
    (hdiv : 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hnext : ¬2 ^ (j + 1) ∣ (G.neighborFinset v ∩ S).card) :
    v ∈ dyadicOccupancySupport G S j := by
  rw [dyadicOccupancySupport, Finset.mem_filter]
  refine ⟨Finset.mem_univ v, ?_⟩
  obtain ⟨t, ht⟩ := hdiv
  have hpow : 2 ^ (j + 1) = 2 ^ j * 2 := by ring
  have htOdd : Odd t := by
    apply Nat.not_even_iff_odd.mp
    intro htEven
    obtain ⟨u, hu⟩ := htEven
    apply hnext
    refine ⟨u, ?_⟩
    rw [hpow, ht, hu]
    ring
  have hquot : (G.neighborFinset v ∩ S).card / 2 ^ j = t := by
    rw [ht]
    exact Nat.mul_div_cancel_left t (pow_pos (by omega) _)
  rwa [hquot]

/-- At a stopping level the marked-line support is nonempty. -/
theorem dyadicOccupancySupport_nonempty_of_stopping
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hnext : ∃ v, ¬2 ^ (j + 1) ∣
      (G.neighborFinset v ∩ S).card) :
    (dyadicOccupancySupport G S j).Nonempty := by
  obtain ⟨v, hv⟩ := hnext
  exact ⟨v, mem_dyadicOccupancySupport_of_dvd_not_dvd
    G S j v (hdiv v) hv⟩

/-- The marked support has even size whenever the degree has one more
factor of two than the current occupancy divisor. -/
theorem even_card_dyadicOccupancySupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    Even (dyadicOccupancySupport G S j).card := by
  let a := 2 ^ j
  let f : V → ℕ := fun v => (G.neighborFinset v ∩ S).card / a
  have ha : 0 < a := by simp [a]
  have hfactor : a * (∑ v : V, f v) = q * S.card := by
    calc
      a * (∑ v : V, f v) = ∑ v : V, a * f v := by
        rw [Finset.mul_sum]
      _ = ∑ v : V, (G.neighborFinset v ∩ S).card := by
        apply Finset.sum_congr rfl
        intro v _
        exact Nat.mul_div_cancel' (hdiv v)
      _ = ∑ v ∈ S, G.degree v :=
        sum_card_neighbor_inter_eq_sum_degree G S
      _ = q * S.card := by simp [hreg, Nat.mul_comm]
  obtain ⟨u, hu⟩ := hqdiv
  have hpow : 2 ^ (j + 1) = a * 2 := by simp [a, pow_succ, Nat.mul_comm]
  have hq : q = a * (2 * u) := by rw [hu, hpow]; ring
  have hsum : (∑ v : V, f v) = 2 * (u * S.card) := by
    apply Nat.eq_of_mul_eq_mul_left ha
    rw [hfactor, hq]
    ring
  rw [dyadicOccupancySupport]
  exact (Finset.even_sum_iff_even_card_odd f).mp
    ⟨u * S.card, by rw [hsum]; ring⟩

/-- Arithmetic complement law for a dyadic digit. -/
theorem odd_div_sub_iff_odd_div
    {a q n : ℕ} (ha : 0 < a) (hn : n ≤ q)
    (hdiv : a ∣ n) (hqdiv : 2 * a ∣ q) :
    Odd ((q - n) / a) ↔ Odd (n / a) := by
  obtain ⟨t, ht⟩ := hdiv
  obtain ⟨u, hu⟩ := hqdiv
  have htu : t ≤ 2 * u := by
    rw [ht, hu] at hn
    apply Nat.le_of_mul_le_mul_left (c := a) (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn) ha
  have hleft : (q - n) / a = 2 * u - t := by
    rw [hu, ht]
    conv_lhs =>
      rw [show 2 * a * u = a * (2 * u) by ring,
        ← Nat.mul_sub_left_distrib]
    exact Nat.mul_div_cancel_left (2 * u - t) ha
  have hright : n / a = t := by rw [ht, Nat.mul_div_cancel_left t ha]
  rw [hleft, hright]
  constructor <;> intro hodd
  · obtain ⟨r, hr⟩ := hodd
    refine ⟨u - r - 1, ?_⟩
    omega
  · obtain ⟨r, hr⟩ := hodd
    refine ⟨u - r - 1, ?_⟩
    omega

/-- If `2^(j+1)` divides the regular degree and every shore occupancy is
divisible by `2^j`, the marked support is unchanged by complementing the
shore. -/
theorem dyadicOccupancySupport_compl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    dyadicOccupancySupport G (Sᶜ : Finset V) j =
      dyadicOccupancySupport G S j := by
  ext v
  simp only [dyadicOccupancySupport, Finset.mem_filter, Finset.mem_univ,
    true_and]
  have hpartition :
      (G.neighborFinset v ∩ S).card +
        (G.neighborFinset v ∩ (Sᶜ : Finset V)).card = q := by
    rw [← Finset.card_union_of_disjoint]
    · rw [← Finset.inter_union_distrib_left, Finset.union_compl,
        Finset.inter_univ, G.card_neighborFinset_eq_degree, hreg]
    · exact Finset.disjoint_left.mpr fun x hxS hxSc =>
        (Finset.mem_compl.mp (Finset.mem_inter.mp hxSc).2)
          (Finset.mem_inter.mp hxS).2
  have hcomp : (G.neighborFinset v ∩ (Sᶜ : Finset V)).card =
      q - (G.neighborFinset v ∩ S).card := by omega
  rw [hcomp]
  apply odd_div_sub_iff_odd_div (by positivity)
  · calc
      (G.neighborFinset v ∩ S).card ≤ (G.neighborFinset v).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  · exact hdiv v
  · simpa [pow_succ, Nat.mul_comm] using hqdiv

/-- Capstone package: the finite stopping theorem produces an actual
nonempty even marked-line support, canonically shared by a shore and its
complement. -/
theorem c4Free_binarySquare_exists_dyadic_stoppingSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hk : 2 ≤ k)
    (hq : q = 2 ^ k) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (heven : ∀ v, 2 ∣ (G.neighborFinset v ∩ S).card) :
    ∃ j B, 1 ≤ j ∧ j < k ∧
      B = dyadicOccupancySupport G S j ∧ B.Nonempty ∧ Even B.card ∧
      B = dyadicOccupancySupport G (Sᶜ : Finset V) j := by
  obtain ⟨j, hj1, hjk, hdiv, hnext⟩ :=
    c4Free_binarySquare_exists_dyadic_occupancy_stopping_level
      G hfree hk hq hreg hcard S hS hSc heven
  have hqdiv : 2 ^ (j + 1) ∣ q := by
    refine ⟨2 ^ (k - (j + 1)), ?_⟩
    rw [hq, ← pow_add]
    congr 1
    omega
  let B := dyadicOccupancySupport G S j
  refine ⟨j, B, hj1, hjk, rfl, ?_, ?_, ?_⟩
  · exact dyadicOccupancySupport_nonempty_of_stopping G S j hdiv hnext
  · exact even_card_dyadicOccupancySupport G hreg S j hdiv hqdiv
  · exact (dyadicOccupancySupport_compl G hreg S j hdiv hqdiv).symm

end

end Erdos85

#print axioms Erdos85.dyadicOccupancySupport_nonempty_of_stopping
#print axioms Erdos85.even_card_dyadicOccupancySupport
#print axioms Erdos85.dyadicOccupancySupport_compl
#print axioms Erdos85.c4Free_binarySquare_exists_dyadic_stoppingSupport
