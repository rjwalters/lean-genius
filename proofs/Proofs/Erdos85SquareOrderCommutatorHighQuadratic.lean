import Proofs.Erdos85SquareOrderCommutatorHighEquidistance

/-!
# The zero-sum high-sector quadratic form

On the high sector the commutator-row Gram matrix has constant off-diagonal
entry and diagonal increment `d`. Consequently its restriction to
coefficient vectors of sum zero is exactly `d` times the standard quadratic
form. This is the positive-definite spectral statement behind the simplex
geometry of the high rows.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_high_commutator_gram_quadratic_of_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hHtwo : 2 ≤ (squareOrderHighVertices G d).card)
    (z : V → ℤ)
    (hz : ∑ a ∈ squareOrderHighVertices G d, z a = 0) :
    let H := squareOrderHighVertices G d
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    (∑ a ∈ H, ∑ b ∈ H,
      z a * z b * (∑ y : V, C a y * C b y)) =
        (d : ℤ) * ∑ a ∈ H, z a * z a := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  let s : ℤ := (d : ℤ) * d - H.card - (2 * (d : ℤ) + 1)
  dsimp only
  have hHtwo' : 2 ≤ H.card := by simpa [H] using hHtwo
  obtain ⟨u, hu, v, hv, huv⟩ :=
    Finset.one_lt_card.mp (show 1 < H.card by omega)
  have hcapacity : 2 * d + 1 + H.card ≤ d * d := by
    simpa [H] using
      squareOrder_two_mul_add_one_add_card_high_le_of_two_high
        G hfree hd hmin hcover hcard hu hv huv
  have hHle : H.card ≤ d * d := by omega
  have hcapOne : d + 1 ≤ d * d - H.card := by omega
  have hcapTwo : 2 * d + 1 ≤ d * d - H.card := by omega
  have hgram : ∀ a ∈ H, ∀ b ∈ H,
      (∑ y : V, C a y * C b y) =
        (if a = b then (d : ℤ) else 0) + s := by
    intro a ha b hb
    have h := squareOrder_sum_commutator_row_mul_of_high
      G hfree hd hmin hcover hcard ha hb
    by_cases hab : a = b
    · rw [if_pos hab]
      rw [show (∑ y : V, C a y * C b y) =
          ((d * d - H.card - (d + 1) : Nat) : ℤ) by
        simpa [C, H, hab] using h]
      rw [Nat.cast_sub hcapOne, Nat.cast_sub hHle]
      push_cast
      dsimp [s]
      ring
    · rw [if_neg hab]
      rw [show (∑ y : V, C a y * C b y) =
          ((d * d - H.card - (2 * d + 1) : Nat) : ℤ) by
        simpa [C, H, hab] using h]
      rw [Nat.cast_sub hcapTwo, Nat.cast_sub hHle]
      push_cast
      simp [s]
  calc
    (∑ a ∈ H, ∑ b ∈ H,
        z a * z b * (∑ y : V, C a y * C b y)) =
        ∑ a ∈ H, ∑ b ∈ H,
          z a * z b * ((if a = b then (d : ℤ) else 0) + s) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [hgram a ha b hb]
    _ = ∑ a ∈ H,
        ((d : ℤ) * z a * z a + s * z a * (∑ b ∈ H, z b)) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ b ∈ H, z a * z b *
            ((if a = b then (d : ℤ) else 0) + s)) =
            (∑ b ∈ H, if a = b then (d : ℤ) * z a * z a else 0) +
              ∑ b ∈ H, s * z a * z b := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro b _hb
          split_ifs with hab
          · subst b
            ring
          · ring
        _ = (d : ℤ) * z a * z a + s * z a * (∑ b ∈ H, z b) := by
          simp [ha, Finset.mul_sum]
    _ = (d : ℤ) * ∑ a ∈ H, z a * z a := by
      rw [show (∑ b ∈ H, z b) = 0 by simpa [H] using hz]
      simp only [mul_zero, add_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring

end

end Erdos85
