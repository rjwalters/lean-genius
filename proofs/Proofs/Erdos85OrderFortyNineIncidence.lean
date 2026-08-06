import Proofs.Erdos85OrderFortyNineStratification

/-!
# High-sector incidence moments at order 49

This file develops the generic second-moment double count needed to turn the
pairwise-design core of the order-49 laboratory into a Cauchy bound.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Squared incidences into a selected vertex set count ordered selected pairs
with a common neighbor. -/
theorem sum_neighbor_inter_sq_eq_sum_sum_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ x : V, ((G.neighborFinset x ∩ S).card) ^ 2) =
      ∑ a ∈ S, ∑ b ∈ S,
        (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  have hcard : ∀ x : V,
      (G.neighborFinset x ∩ S).card =
        ∑ a ∈ S, if G.Adj x a then 1 else 0 := by
    intro x
    calc
      (G.neighborFinset x ∩ S).card =
          (S.filter fun a => G.Adj x a).card := by
        congr 1
        ext a
        simp [SimpleGraph.mem_neighborFinset, and_comm]
      _ = ∑ a ∈ S, if G.Adj x a then 1 else 0 := by
        rw [Finset.card_filter]
  have hcommon : ∀ a b : V,
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        ∑ x : V, (if G.Adj x a then 1 else 0) *
          (if G.Adj x b then 1 else 0) := by
    intro a b
    calc
      (G.neighborFinset a ∩ G.neighborFinset b).card =
          ∑ x : V, if G.Adj a x ∧ G.Adj b x then 1 else 0 := by
        rw [Finset.card_eq_sum_ones]
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext x
          simp [SimpleGraph.mem_neighborFinset]
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          simp
      _ = ∑ x : V, (if G.Adj x a then 1 else 0) *
          (if G.Adj x b then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [G.adj_comm]
        by_cases hax : G.Adj a x <;> by_cases hbx : G.Adj b x <;>
          simp [hax, hbx]
  simp_rw [hcard, pow_two, Finset.sum_mul_sum, hcommon]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/-- The degree-eight sector. -/
def orderFortyNineHighVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun x => G.degree x = 8

/-- Every high vertex contributes its eight incidences, giving first moment
`8h`. -/
theorem orderFortyNine_sum_highNeighborCount_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ x : V,
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) =
      8 * (orderFortyNineHighVertices G).card := by
  rw [sum_card_neighbor_inter_eq_sum_degree]
  calc
    (∑ a ∈ orderFortyNineHighVertices G, G.degree a) =
        ∑ _a ∈ orderFortyNineHighVertices G, 8 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    _ = 8 * (orderFortyNineHighVertices G).card := by
      simp [Nat.mul_comm]

/-- The high-incidence square moment is `h(h+7)`: diagonal high pairs
contribute degree eight and distinct high pairs contribute their unique common
neighbor. -/
theorem orderFortyNine_sum_highNeighborCount_sq_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (∑ x : V,
      ((G.neighborFinset x ∩ orderFortyNineHighVertices G).card) ^ 2) =
      (orderFortyNineHighVertices G).card *
        ((orderFortyNineHighVertices G).card + 7) := by
  rw [sum_neighbor_inter_sq_eq_sum_sum_common]
  have hterm : ∀ a ∈ orderFortyNineHighVertices G,
      ∀ b ∈ orderFortyNineHighVertices G,
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        if a = b then 8 else 1 := by
    intro a ha b hb
    have ha8 : G.degree a = 8 := (Finset.mem_filter.mp ha).2
    have hb8 : G.degree b = 8 := (Finset.mem_filter.mp hb).2
    by_cases hab : a = b
    · subst b
      rw [if_pos rfl, Finset.inter_self,
        G.card_neighborFinset_eq_degree, ha8]
    · rw [if_neg hab]
      exact orderFortyNine_card_common_degreeEight_eq_one
        G hfree hmin hcard ha8 hb8 hab
  calc
    (∑ a ∈ orderFortyNineHighVertices G, ∑ b ∈ orderFortyNineHighVertices G,
        (G.neighborFinset a ∩ G.neighborFinset b).card) =
        ∑ a ∈ orderFortyNineHighVertices G,
          ∑ b ∈ orderFortyNineHighVertices G, if a = b then 8 else 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hterm a ha b hb
    _ = (orderFortyNineHighVertices G).card *
        ((orderFortyNineHighVertices G).card + 7) := by
      have hinner : ∀ a ∈ orderFortyNineHighVertices G,
          (∑ b ∈ orderFortyNineHighVertices G, if a = b then 8 else 1) =
            (orderFortyNineHighVertices G).card + 7 := by
        intro a ha
        calc
          (∑ b ∈ orderFortyNineHighVertices G,
              if a = b then 8 else 1) =
              (∑ b ∈ (orderFortyNineHighVertices G).erase a,
                if a = b then 8 else 1) + 8 := by
            rw [← Finset.sum_erase_add _ _ ha]
            simp
          _ = (∑ _b ∈ (orderFortyNineHighVertices G).erase a, 1) + 8 := by
            congr 1
            apply Finset.sum_congr rfl
            intro b hb
            have hba : b ≠ a := (Finset.mem_erase.mp hb).1
            simp [hba.symm]
          _ = (orderFortyNineHighVertices G).card + 7 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem ha]
            change ((orderFortyNineHighVertices G).card - 1) * 1 + 8 =
              (orderFortyNineHighVertices G).card + 7
            rw [Nat.mul_one]
            have hpos : 0 < (orderFortyNineHighVertices G).card :=
              Finset.card_pos.mpr ⟨a, ha⟩
            have hpred : (orderFortyNineHighVertices G).card - 1 + 1 =
                (orderFortyNineHighVertices G).card :=
              Nat.sub_add_cancel hpos
            omega
      rw [Finset.sum_congr rfl hinner, Finset.sum_const]
      simp

/-- A high vertex has no high neighbors.  Thus the high-to-all incidence
moments are supported entirely on the low sector. -/
theorem orderFortyNine_highNeighborCount_eq_zero_of_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V}
    (hx : x ∈ orderFortyNineHighVertices G) :
    (G.neighborFinset x ∩ orderFortyNineHighVertices G).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hxy : G.Adj x y := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hy).1
  have hx8 : G.degree x = 8 := (Finset.mem_filter.mp hx).2
  have hy8 : G.degree y = 8 :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  exact orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin hcard hx8 hy8 hxy

/-- First incidence moment restricted to the low vertices. -/
theorem orderFortyNine_sum_low_highNeighborCount_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (∑ x ∈ (Finset.univ : Finset V) \ orderFortyNineHighVertices G,
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) =
      8 * (orderFortyNineHighVertices G).card := by
  have hsplit := Finset.sum_sdiff
    (show orderFortyNineHighVertices G ⊆ (Finset.univ : Finset V) by simp)
    (f := fun x =>
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card)
  have hhigh : (∑ x ∈ orderFortyNineHighVertices G,
      (G.neighborFinset x ∩ orderFortyNineHighVertices G).card) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin hcard hx
  rw [hhigh, add_zero] at hsplit
  rw [hsplit, orderFortyNine_sum_highNeighborCount_eq]

/-- Second incidence moment restricted to the low vertices. -/
theorem orderFortyNine_sum_low_highNeighborCount_sq_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (∑ x ∈ (Finset.univ : Finset V) \ orderFortyNineHighVertices G,
      ((G.neighborFinset x ∩ orderFortyNineHighVertices G).card) ^ 2) =
      (orderFortyNineHighVertices G).card *
        ((orderFortyNineHighVertices G).card + 7) := by
  have hsplit := Finset.sum_sdiff
    (show orderFortyNineHighVertices G ⊆ (Finset.univ : Finset V) by simp)
    (f := fun x =>
      ((G.neighborFinset x ∩ orderFortyNineHighVertices G).card) ^ 2)
  have hhigh : (∑ x ∈ orderFortyNineHighVertices G,
      ((G.neighborFinset x ∩ orderFortyNineHighVertices G).card) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [orderFortyNine_highNeighborCount_eq_zero_of_high
      G hfree hmin hcard hx]
    norm_num
  rw [hhigh, add_zero] at hsplit
  rw [hsplit, orderFortyNine_sum_highNeighborCount_sq_eq G hfree hmin hcard]

/-- Cauchy--Schwarz on the low-side blocks of the high-vertex pair design
forces at most ten high vertices. -/
theorem orderFortyNine_card_high_le_ten
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (orderFortyNineHighVertices G).card ≤ 10 := by
  let H := orderFortyNineHighVertices G
  let L := (Finset.univ : Finset V) \ H
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ H).card
  have hfirst : (∑ x ∈ L, k x) = 8 * H.card := by
    simpa [H, L, k] using
      orderFortyNine_sum_low_highNeighborCount_eq G hfree hmin hcard
  have hsecond : (∑ x ∈ L, k x * k x) = H.card * (H.card + 7) := by
    simpa [H, L, k, pow_two] using
      orderFortyNine_sum_low_highNeighborCount_sq_eq G hfree hmin hcard
  have hz := sq_sum_le_card_mul_sum_sq
    (s := L) (f := fun x => (k x : ℤ))
  have hcs : (∑ x ∈ L, k x) * (∑ x ∈ L, k x) ≤
      L.card * ∑ x ∈ L, k x * k x := by
    norm_num [pow_two] at hz
    exact_mod_cast hz
  have hLcard : L.card = 49 - H.card := by
    dsimp [L]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp
  have hHle : H.card ≤ 49 := by
    have := Finset.card_le_card
      (show H ⊆ (Finset.univ : Finset V) by simp)
    simpa [hcard] using this
  have hHpos : 0 < H.card := by
    rcases orderFortyNine_exists_degreeEight G hfree hmin hcard with ⟨x, hx⟩
    exact Finset.card_pos.mpr ⟨x, by simp [H, orderFortyNineHighVertices, hx]⟩
  rw [hfirst, hsecond, hLcard] at hcs
  have hcomplement : 49 - H.card + H.card = 49 :=
    Nat.sub_add_cancel hHle
  change H.card ≤ 10
  nlinarith [hcs, hcomplement]

/-- The handshake parity sharpens the Cauchy bound to `h ≤ 9`. -/
theorem orderFortyNine_card_high_le_nine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (orderFortyNineHighVertices G).card ≤ 9 := by
  have hle := orderFortyNine_card_high_le_ten G hfree hmin hcard
  have hodd := orderFortyNine_card_degreeEight_odd G hfree hmin hcard
  change Odd (orderFortyNineHighVertices G).card at hodd
  rcases hodd with ⟨m, hm⟩
  omega

end

end Erdos85
