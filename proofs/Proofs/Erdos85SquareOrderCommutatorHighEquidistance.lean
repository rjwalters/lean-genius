import Proofs.Erdos85SquareOrderCommutatorHighGram

/-!
# Equidistance of high commutator rows

Distinct high vertices have neighbor sets of size `d+1` meeting in exactly
one point. Their union therefore occupies `2d+1` low vertices. This removes
the truncated subtraction in the high Gram formula and shows that all high
commutator rows are pairwise at squared distance `2d`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_two_mul_add_one_add_card_high_le_of_two_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a b : V}
    (ha : a ∈ squareOrderHighVertices G d)
    (hb : b ∈ squareOrderHighVertices G d) (hab : a ≠ b) :
    2 * d + 1 + (squareOrderHighVertices G d).card ≤ d * d := by
  classical
  let H := squareOrderHighVertices G d
  let L : Finset V := Finset.univ \ H
  let Na : Finset V := G.neighborFinset a
  let Nb : Finset V := G.neighborFinset b
  have haDegree : G.degree a = d + 1 := (Finset.mem_filter.mp ha).2
  have hbDegree : G.degree b = d + 1 := (Finset.mem_filter.mp hb).2
  have haSub : Na ⊆ L := by
    intro y hy
    refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
    intro hyH
    exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
      haDegree (Finset.mem_filter.mp hyH).2
      ((G.mem_neighborFinset a y).mp hy)
  have hbSub : Nb ⊆ L := by
    intro y hy
    refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
    intro hyH
    exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
      hbDegree (Finset.mem_filter.mp hyH).2
      ((G.mem_neighborFinset b y).mp hy)
  have hunionSub : Na ∪ Nb ⊆ L := Finset.union_subset haSub hbSub
  have hinter : (Na ∩ Nb).card = 1 := by
    simpa [Na, Nb] using
      squareOrder_card_common_degree_succ_eq_one
        G hfree hd hmin hcover hcard haDegree hbDegree hab
  have hNa : Na.card = d + 1 := by
    simpa [Na, G.card_neighborFinset_eq_degree] using haDegree
  have hNb : Nb.card = d + 1 := by
    simpa [Nb, G.card_neighborFinset_eq_degree] using hbDegree
  have hunion : (Na ∪ Nb).card = 2 * d + 1 := by
    have hcount := Finset.card_union_add_card_inter Na Nb
    omega
  have hLcard : L.card = d * d - H.card := by
    dsimp [L]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp
  have hbound := Finset.card_le_card hunionSub
  rw [hunion, hLcard] at hbound
  change 2 * d + 1 + H.card ≤ d * d
  omega

theorem squareOrder_sum_commutator_high_row_sub_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a b : V}
    (ha : a ∈ squareOrderHighVertices G d)
    (hb : b ∈ squareOrderHighVertices G d) (hab : a ≠ b) :
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    (∑ y : V, (C a y - C b y) * (C a y - C b y)) = 2 * d := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  dsimp only
  have hrowa : (∑ y : V, C a y * C a y) =
      ((d * d - H.card - (d + 1) : Nat) : ℤ) := by
    have h := squareOrder_sum_commutator_entry_sq_row
      G hfree hd hmin hcover hcard a
    simpa [C, H, ha] using h
  have hrowb : (∑ y : V, C b y * C b y) =
      ((d * d - H.card - (d + 1) : Nat) : ℤ) := by
    have h := squareOrder_sum_commutator_entry_sq_row
      G hfree hd hmin hcover hcard b
    simpa [C, H, hb] using h
  have hcross : (∑ y : V, C a y * C b y) =
      ((d * d - H.card - (2 * d + 1) : Nat) : ℤ) := by
    have h := squareOrder_sum_commutator_row_mul_of_high
      G hfree hd hmin hcover hcard ha hb
    simpa [C, H, hab] using h
  have hcapacity : 2 * d + 1 + H.card ≤ d * d := by
    simpa [H] using
      squareOrder_two_mul_add_one_add_card_high_le_of_two_high
        G hfree hd hmin hcover hcard ha hb hab
  calc
    (∑ y : V, (C a y - C b y) * (C a y - C b y)) =
        ∑ y : V, (C a y * C a y + C b y * C b y -
          2 * (C a y * C b y)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      ring
    _ =
        (∑ y : V, C a y * C a y) +
          (∑ y : V, C b y * C b y) -
            2 * (∑ y : V, C a y * C b y) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    _ = 2 * d := by
      rw [hrowa, hrowb, hcross]
      have hcap₁ : H.card ≤ d * d := by omega
      have hcap₂ : d + 1 ≤ d * d - H.card := by omega
      have hcap₃ : 2 * d + 1 ≤ d * d - H.card := by omega
      rw [Nat.cast_sub hcap₂, Nat.cast_sub hcap₃,
        Nat.cast_sub hcap₁]
      push_cast
      ring

end

end Erdos85
