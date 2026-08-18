import Proofs.Erdos85SquareOrderCommutatorHighQuadratic

/-!
# Affine independence of high commutator rows

The positive zero-sum quadratic form rules out every nontrivial integral
affine dependence among the high commutator rows.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_high_commutator_rows_int_affineIndependent
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
    (hz : ∑ a ∈ squareOrderHighVertices G d, z a = 0)
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
  have hquad := squareOrder_high_commutator_gram_quadratic_of_sum_zero
    G hfree hd hmin hcover hcard hHtwo z hz
  change (∑ a ∈ H, ∑ b ∈ H,
      z a * z b * (∑ y : V, C a y * C b y)) =
        (d : ℤ) * ∑ a ∈ H, z a * z a at hquad
  have hleft : (∑ a ∈ H, ∑ b ∈ H,
      z a * z b * (∑ y : V, C a y * C b y)) = 0 := by
    exact Finset.sum_eq_zero hinner
  rw [hleft] at hquad
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hsumsq : (∑ a ∈ H, z a * z a) = 0 := by
    exact (mul_eq_zero.mp hquad.symm).resolve_left hdne
  intro a ha
  have haSq : z a * z a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _hx => mul_self_nonneg (z x))).mp hsumsq a ha
  exact (mul_self_eq_zero.mp haSq)

end

end Erdos85
