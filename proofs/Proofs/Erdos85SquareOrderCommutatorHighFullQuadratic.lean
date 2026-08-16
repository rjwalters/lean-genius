import Proofs.Erdos85SquareOrderCommutatorHighQuadratic

/-!
# Full positive-definite high commutator form

The high-row Gram matrix is `d I + s J`, where
`s = d² - |H| - (2d+1)`.  The two-high capacity theorem makes `s` an
honest nonnegative integer.  This gives the full quadratic form and genuine
linear independence, without a zero-sum hypothesis.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_high_commutator_gram_full_quadratic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hHtwo : 2 ≤ (squareOrderHighVertices G d).card)
    (z : V → ℤ) :
    let H := squareOrderHighVertices G d
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    let s := d * d - H.card - (2 * d + 1)
    (∑ a ∈ H, ∑ b ∈ H,
      z a * z b * (∑ y : V, C a y * C b y)) =
        (d : ℤ) * ∑ a ∈ H, z a * z a +
          (s : ℤ) * (∑ a ∈ H, z a) * (∑ a ∈ H, z a) := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  let s := d * d - H.card - (2 * d + 1)
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
        (if a = b then (d : ℤ) else 0) + (s : ℤ) := by
    intro a ha b hb
    have h := squareOrder_sum_commutator_row_mul_of_high
      G hfree hd hmin hcover hcard ha hb
    by_cases hab : a = b
    · rw [if_pos hab]
      rw [show (∑ y : V, C a y * C b y) =
          ((d * d - H.card - (d + 1) : Nat) : ℤ) by
        simpa [C, H, hab] using h]
      rw [Nat.cast_sub hcapOne, Nat.cast_sub hHle,
        show s = d * d - H.card - (2 * d + 1) by rfl,
        Nat.cast_sub hcapTwo, Nat.cast_sub hHle]
      push_cast
      ring
    · rw [if_neg hab]
      simpa [C, H, s, hab] using h
  calc
    (∑ a ∈ H, ∑ b ∈ H,
        z a * z b * (∑ y : V, C a y * C b y)) =
        ∑ a ∈ H, ∑ b ∈ H,
          z a * z b * ((if a = b then (d : ℤ) else 0) + (s : ℤ)) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [hgram a ha b hb]
    _ = ∑ a ∈ H,
        ((d : ℤ) * z a * z a + (s : ℤ) * z a * (∑ b ∈ H, z b)) := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ b ∈ H, z a * z b *
            ((if a = b then (d : ℤ) else 0) + (s : ℤ))) =
            (∑ b ∈ H, if a = b then (d : ℤ) * z a * z a else 0) +
              ∑ b ∈ H, (s : ℤ) * z a * z b := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro b _hb
          split_ifs with hab
          · subst b
            ring
          · ring
        _ = (d : ℤ) * z a * z a +
            (s : ℤ) * z a * (∑ b ∈ H, z b) := by
          simp [ha, Finset.mul_sum]
    _ = (d : ℤ) * ∑ a ∈ H, z a * z a +
        (s : ℤ) * (∑ a ∈ H, z a) * (∑ a ∈ H, z a) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro a _ha
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _ha
        ring

theorem squareOrder_high_commutator_rows_int_linearIndependent
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
    (hlin : ∀ y : V,
      ∑ a ∈ squareOrderHighVertices G d,
        z a *
          (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
            (secondOrderDefectGraph G).adjMatrix ℤ *
              G.adjMatrix ℤ) a y = 0) :
    ∀ a ∈ squareOrderHighVertices G d, z a = 0 := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  let s := d * d - H.card - (2 * d + 1)
  have hlin' : ∀ y : V, ∑ a ∈ H, z a * C a y = 0 := by
    intro y
    simpa [H, C] using hlin y
  have hinner : ∀ a ∈ H,
      (∑ b ∈ H, z a * z b * (∑ y : V, C a y * C b y)) = 0 := by
    intro a ha
    calc
      (∑ b ∈ H, z a * z b * (∑ y : V, C a y * C b y)) =
          ∑ b ∈ H, ∑ y : V, z a * z b * (C a y * C b y) := by
        apply Finset.sum_congr rfl
        intro b _hb
        rw [Finset.mul_sum]
      _ = ∑ y : V, ∑ b ∈ H, z a * z b * (C a y * C b y) := by
        rw [Finset.sum_comm]
      _ = ∑ y : V, z a * C a y * (∑ b ∈ H, z b * C b y) := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro y _hy
        rw [hlin' y]
        ring
  have hquad := squareOrder_high_commutator_gram_full_quadratic
    G hfree hd hmin hcover hcard hHtwo z
  change (∑ a ∈ H, ∑ b ∈ H,
      z a * z b * (∑ y : V, C a y * C b y)) =
        (d : ℤ) * ∑ a ∈ H, z a * z a +
          (s : ℤ) * (∑ a ∈ H, z a) * (∑ a ∈ H, z a) at hquad
  have hleft : (∑ a ∈ H, ∑ b ∈ H,
      z a * z b * (∑ y : V, C a y * C b y)) = 0 :=
    Finset.sum_eq_zero hinner
  rw [hleft] at hquad
  have hsumsq_nonneg : (0 : ℤ) ≤ ∑ a ∈ H, z a * z a := by
    exact Finset.sum_nonneg fun a _ha => mul_self_nonneg (z a)
  have hsum_nonneg : (0 : ℤ) ≤ (∑ a ∈ H, z a) * (∑ a ∈ H, z a) :=
    mul_self_nonneg _
  have hs_nonneg : (0 : ℤ) ≤ s := by exact_mod_cast (Nat.zero_le s)
  have hd_pos : (0 : ℤ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsumsq : (∑ a ∈ H, z a * z a) = 0 := by
    nlinarith
  intro a ha
  have haSq : z a * z a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _hx => mul_self_nonneg (z x))).mp hsumsq a ha
  exact mul_self_eq_zero.mp haSq

end

end Erdos85
