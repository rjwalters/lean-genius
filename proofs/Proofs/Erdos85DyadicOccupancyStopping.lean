import Proofs.Erdos85C4FreeNeighborBlockPartition

/-!
# Finite dyadic stopping for adjacency-kernel shores

For a nontrivial shore in a square-order regular C4-free graph, its line
occupancies cannot all be divisible by the full degree.  Combined with the
even-occupancy condition supplied by the binary adjacency kernel, this
forces a first nonzero dyadic occupancy digit strictly before the `q` scale.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If every line meeting a nonempty shore lies wholly in that shore, the
C4-free neighbor blocks through any shore point give the Moore-type lower
bound `q(q-1)+1`. -/
theorem shore_card_ge_of_full_or_empty_occupancies
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hS : S.Nonempty)
    (hfull : ∀ v, (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = q) :
    q * (q - 1) + 1 ≤ S.card := by
  obtain ⟨x, hxS⟩ := hS
  have hxNot : x ∉ S.erase x := by simp
  have hsum := c4Free_sum_neighbor_block_cards_eq_common_targets
    G hfree x (S.erase x) hxNot
  dsimp only at hsum
  have hrow : ∀ w ∈ G.neighborFinset x,
      (G.neighborFinset w ∩ S.erase x).card = q - 1 := by
    intro w hw
    have hxw : x ∈ G.neighborFinset w := by
      simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using hw
    have hpos : 0 < (G.neighborFinset w ∩ S).card := by
      rw [Finset.card_pos]
      exact ⟨x, Finset.mem_inter.mpr ⟨hxw, hxS⟩⟩
    have hcard : (G.neighborFinset w ∩ S).card = q :=
      (hfull w).resolve_left (by omega)
    rw [Finset.inter_erase, Finset.card_erase_of_mem
      (Finset.mem_inter.mpr ⟨hxw, hxS⟩), hcard]
  have hleft : (∑ w ∈ G.neighborFinset x,
      (G.neighborFinset w ∩ S.erase x).card) = q * (q - 1) := by
    calc
      (∑ w ∈ G.neighborFinset x,
          (G.neighborFinset w ∩ S.erase x).card) =
          ∑ _w ∈ G.neighborFinset x, (q - 1) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact hrow w hw
      _ = q * (q - 1) := by
        simp [G.card_neighborFinset_eq_degree, hreg]
  have hfilterLe :
      ((S.erase x).filter fun y =>
        (G.neighborFinset x ∩ G.neighborFinset y).Nonempty).card ≤
        (S.erase x).card := Finset.card_filter_le _ _
  have hprodLe : q * (q - 1) ≤ (S.erase x).card := by
    calc
      q * (q - 1) = ∑ w ∈ G.neighborFinset x,
          (G.neighborFinset w ∩ S.erase x).card := hleft.symm
      _ = ((S.erase x).filter fun y =>
          (G.neighborFinset x ∩ G.neighborFinset y).Nonempty).card := hsum
      _ ≤ (S.erase x).card := hfilterLe
  rw [Finset.card_erase_of_mem hxS] at hprodLe
  exact (Nat.le_sub_iff_add_le (Finset.card_pos.mpr ⟨x, hxS⟩)).mp hprodLe

/-- At square order and degree at least three, a nontrivial shore cannot
have every line occupancy divisible by the full degree. -/
theorem exists_line_occupancy_not_dvd_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty) :
    ∃ v, ¬q ∣ (G.neighborFinset v ∩ S).card := by
  by_contra h
  push Not at h
  have hfull : ∀ v, (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = q := by
    intro v
    have hle : (G.neighborFinset v ∩ S).card ≤ q := by
      calc
        (G.neighborFinset v ∩ S).card ≤ (G.neighborFinset v).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
    rcases h v with ⟨a, ha⟩
    rw [ha] at hle
    have hqa : q * a ≤ q * 1 := by simpa using hle
    have hale : a ≤ 1 := Nat.le_of_mul_le_mul_left hqa (by omega)
    by_cases ha0 : a = 0
    · left
      simpa [ha0] using ha
    · right
      have : a = 1 := by omega
      simpa [this] using ha
  have hfullc : ∀ v, (G.neighborFinset v ∩ (Sᶜ : Finset V)).card = 0 ∨
      (G.neighborFinset v ∩ (Sᶜ : Finset V)).card = q := by
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
    rcases hfull v with hzero | hqv
    · right; omega
    · left; omega
  have hSlow := shore_card_ge_of_full_or_empty_occupancies
    G hfree hreg S hS hfull
  have hSclow := shore_card_ge_of_full_or_empty_occupancies
    G hfree hreg (Sᶜ : Finset V) hSc hfullc
  have hsum : S.card + (Sᶜ : Finset V).card = q * q := by
    rw [Finset.card_compl]
    calc
      S.card + (Fintype.card V - S.card) = Fintype.card V :=
        Nat.add_sub_of_le (Finset.card_le_univ S)
      _ = q * q := hcard
  have htwo : 2 * (q * (q - 1) + 1) ≤ q * q := by
    calc
      2 * (q * (q - 1) + 1) =
          (q * (q - 1) + 1) + (q * (q - 1) + 1) := by ring
      _ ≤ S.card + (Sᶜ : Finset V).card := Nat.add_le_add hSlow hSclow
      _ = q * q := hsum
  have hqsplit : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  nlinarith

/-- Pure arithmetic extraction of the first nonzero dyadic digit. -/
theorem exists_dyadic_stopping_level
    {ι : Type*} (b : ι → ℕ) {k : ℕ} (_hk : 2 ≤ k)
    (heven : ∀ i, 2 ∣ b i) (hstop : ∃ i, ¬2 ^ k ∣ b i) :
    ∃ j, 1 ≤ j ∧ j < k ∧ (∀ i, 2 ^ j ∣ b i) ∧
      ∃ i, ¬2 ^ (j + 1) ∣ b i := by
  classical
  let P : ℕ → Prop := fun m => ∃ i, ¬2 ^ m ∣ b i
  have hP : ∃ m, P m := ⟨k, hstop⟩
  let m := Nat.find hP
  have hmP : P m := Nat.find_spec hP
  have hmle : m ≤ k := Nat.find_min' hP hstop
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := by omega
    rcases hmP with ⟨i, hi⟩
    simp [hm0] at hi
  have hmne1 : m ≠ 1 := by
    intro hm1
    rcases hmP with ⟨i, hi⟩
    exact hi (by simpa [hm1] using (heven i))
  let j := m - 1
  have hj1 : 1 ≤ j := by dsimp [j]; omega
  have hjk : j < k := by dsimp [j]; omega
  have hjall : ∀ i, 2 ^ j ∣ b i := by
    intro i
    by_contra hi
    have hPj : P j := ⟨i, hi⟩
    have hjfind : j < Nat.find hP := by simpa [m] using
      (show j < m by dsimp [j]; omega)
    exact (Nat.find_min hP hjfind) hPj
  have hjnext : ∃ i, ¬2 ^ (j + 1) ∣ b i := by
    have hjm : j + 1 = m := by dsimp [j]; omega
    simpa [hjm] using hmP
  exact ⟨j, hj1, hjk, hjall, hjnext⟩

/-- Graph-facing finite dyadic stopping theorem.  An even-occupancy
nontrivial shore at degree `q=2^k` emits a nonzero digit at some level
`1 ≤ j < k`; the hierarchy cannot remain zero through the `q` scale. -/
theorem c4Free_binarySquare_exists_dyadic_occupancy_stopping_level
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hk : 2 ≤ k)
    (hq : q = 2 ^ k) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hS : S.Nonempty) (hSc : (Sᶜ : Finset V).Nonempty)
    (heven : ∀ v, 2 ∣ (G.neighborFinset v ∩ S).card) :
    ∃ j, 1 ≤ j ∧ j < k ∧
      (∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) ∧
      ∃ v, ¬2 ^ (j + 1) ∣ (G.neighborFinset v ∩ S).card := by
  have hq3 : 3 ≤ q := by
    rw [hq]
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    norm_num at this ⊢
    omega
  apply exists_dyadic_stopping_level
  · exact hk
  · exact heven
  · rw [← hq]
    exact exists_line_occupancy_not_dvd_degree
      G hfree hq3 hreg hcard S hS hSc

end

end Erdos85

#print axioms Erdos85.shore_card_ge_of_full_or_empty_occupancies
#print axioms Erdos85.exists_line_occupancy_not_dvd_degree
#print axioms Erdos85.c4Free_binarySquare_exists_dyadic_occupancy_stopping_level
