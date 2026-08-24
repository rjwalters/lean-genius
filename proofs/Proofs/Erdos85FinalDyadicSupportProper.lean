import Proofs.Erdos85DyadicStoppingSupportCherrySqueeze
import Proofs.Erdos85BinarySquareDyadicSignedTerminal

/-!
# Properness of the final dyadic stopping support

At the last dyadic level `a=q/2`, a full marked support would force every
line to meet the shore in exactly `a` points.  C4-free neighbor blocks then
show that the shore is closed under the second-order defect graph, contrary
to defect connectivity for a nontrivial shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the final scale `q=2a`, full marked support forces constant line
occupancy `a`. -/
theorem finalDyadic_fullSupport_occupancy_eq_half
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q a : ℕ} (ha : 0 < a) (hqa : q = 2 * a)
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hdiv : ∀ v, a ∣ (G.neighborFinset v ∩ S).card)
    (hfull : Finset.univ.filter (fun v =>
      Odd ((G.neighborFinset v ∩ S).card / a)) = Finset.univ) :
    ∀ v, (G.neighborFinset v ∩ S).card = a := by
  intro v
  have hodd : Odd ((G.neighborFinset v ∩ S).card / a) := by
    have hv : v ∈ Finset.univ.filter (fun z =>
        Odd ((G.neighborFinset z ∩ S).card / a)) := by
      rw [hfull]
      exact Finset.mem_univ v
    exact (Finset.mem_filter.mp hv).2
  obtain ⟨t, ht⟩ := hdiv v
  have hquot : (G.neighborFinset v ∩ S).card / a = t := by
    rw [ht]
    exact Nat.mul_div_cancel_left t ha
  have htOdd : Odd t := by simpa [hquot] using hodd
  have hle : (G.neighborFinset v ∩ S).card ≤ q := by
    calc
      (G.neighborFinset v ∩ S).card ≤ (G.neighborFinset v).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  have ht2 : t ≤ 2 := by
    rw [ht, hqa] at hle
    exact Nat.le_of_mul_le_mul_left (by simpa [Nat.mul_comm] using hle) ha
  obtain ⟨u, hu⟩ := htOdd
  have ht1 : t = 1 := by omega
  simpa [ht1] using ht

/-- Constant half occupancy at square order fixes the shore size to `qa`. -/
theorem card_eq_degree_mul_half_of_constant_occupancy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q a : ℕ} (hq : 0 < q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hocc : ∀ v, (G.neighborFinset v ∩ S).card = a) :
    S.card = q * a := by
  have hinc := sum_card_neighbor_inter_eq_sum_degree G S
  have hleft : (∑ v : V, (G.neighborFinset v ∩ S).card) =
      (q * q) * a := by simp [hocc, hcard]
  have hright : (∑ v ∈ S, G.degree v) = q * S.card := by
    simp [hreg, Nat.mul_comm]
  rw [hleft, hright] at hinc
  apply Nat.eq_of_mul_eq_mul_left hq
  calc
    q * S.card = (q * q) * a := hinc.symm
    _ = q * (q * a) := by ring

/-- Constant half occupancy makes every shore point's entire defect
neighborhood stay inside the shore. -/
theorem c4Free_binarySquare_halfOccupancy_defect_neighbor_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (hq : 0 < q) (hq3 : 3 ≤ q) (ha : 0 < a) (hqa : q = 2 * a)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hocc : ∀ v, (G.neighborFinset v ∩ S).card = a) :
    ∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ⊆ S := by
  have hScard : S.card = q * a :=
    card_eq_degree_mul_half_of_constant_occupancy G hq hreg hcard S hocc
  have hDdeg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1 :=
    binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq3 hreg hcard
  intro x hxS
  have hxNot : x ∉ S.erase x := by simp
  have hblocks := c4Free_sum_neighbor_block_cards_eq_defect_complement
    G hfree x (S.erase x) hxNot
  dsimp only at hblocks
  have hrow : ∀ w ∈ G.neighborFinset x,
      (G.neighborFinset w ∩ S.erase x).card = a - 1 := by
    intro w hw
    have hxw : x ∈ G.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hw
    rw [Finset.inter_erase, Finset.card_erase_of_mem
      (Finset.mem_inter.mpr ⟨hxw, hxS⟩), hocc]
  have hnonD :
      ((S.erase x) \ (secondOrderDefectGraph G).neighborFinset x).card =
        q * (a - 1) := by
    rw [← hblocks]
    calc
      (∑ w ∈ G.neighborFinset x,
          (G.neighborFinset w ∩ S.erase x).card) =
          ∑ _w ∈ G.neighborFinset x, (a - 1) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact hrow w hw
      _ = q * (a - 1) := by
        simp [G.card_neighborFinset_eq_degree, hreg]
  have hinterCard :
      ((S.erase x) ∩ (secondOrderDefectGraph G).neighborFinset x).card =
        q - 1 := by
    have hpartition := Finset.card_sdiff_add_card_inter
      (S.erase x) ((secondOrderDefectGraph G).neighborFinset x)
    rw [hnonD, Finset.card_erase_of_mem hxS, hScard] at hpartition
    have hmul : q * (a - 1) = q * a - q := by
      simpa using Nat.mul_sub_left_distrib q a 1
    rw [hmul] at hpartition
    have hq_le : q ≤ q * a := Nat.le_mul_of_pos_right q ha
    omega
  have hsubset :
      (S.erase x) ∩ (secondOrderDefectGraph G).neighborFinset x ⊆
        (secondOrderDefectGraph G).neighborFinset x := Finset.inter_subset_right
  have heq :
      (S.erase x) ∩ (secondOrderDefectGraph G).neighborFinset x =
        (secondOrderDefectGraph G).neighborFinset x := by
    apply Finset.eq_of_subset_of_card_le hsubset
    rw [hinterCard, (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      hDdeg]
  intro y hy
  have hyInter : y ∈ (S.erase x) ∩
      (secondOrderDefectGraph G).neighborFinset x := by
    rw [heq]
    exact hy
  exact (Finset.mem_erase.mp (Finset.mem_inter.mp hyInter).1).2

/-- **Final stopping support is proper.**  In a connected second-order
defect graph, a nontrivial shore cannot have every line marked at the final
dyadic scale. -/
theorem c4Free_binarySquare_finalDyadicSupport_ne_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (hq : 0 < q) (hq3 : 3 ≤ q) (ha : 0 < a) (hqa : q = 2 * a)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (hdiv : ∀ v, a ∣ (G.neighborFinset v ∩ S).card) :
    Finset.univ.filter (fun v =>
      Odd ((G.neighborFinset v ∩ S).card / a)) ≠ Finset.univ := by
  intro hfull
  have hocc := finalDyadic_fullSupport_occupancy_eq_half
    G ha hqa hreg S hdiv hfull
  have hclosed := c4Free_binarySquare_halfOccupancy_defect_neighbor_closed
    G hfree hq hq3 ha hqa hreg hcard S hocc
  obtain ⟨x, hxS⟩ := hS
  obtain ⟨y, hySc⟩ := hSc
  have hreach := hconn x y
  have walk_end_mem : ∀ {u v : V}
      (p : (secondOrderDefectGraph G).Walk u v), u ∈ S → v ∈ S := by
    intro u v p
    induction p with
    | nil => exact fun hu => hu
    | @cons u w v huw p ih =>
        intro hu
        exact ih (hclosed u hu (by
          simpa [SimpleGraph.mem_neighborFinset] using huw))
  have hyS := hreach.elim fun p => walk_end_mem p hxS
  exact (Finset.mem_compl.mp hySc) hyS

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_halfOccupancy_defect_neighbor_closed
#print axioms Erdos85.c4Free_binarySquare_finalDyadicSupport_ne_univ
