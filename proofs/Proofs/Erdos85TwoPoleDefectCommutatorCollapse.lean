import Proofs.Erdos85CrossNeighborhoodFlipDefectExpansion

/-!
# Two-pole collapse of the defect commutator

This file formalizes `(73rnz_cjibkzb)`.  The hypotheses `hAline` and
`hLineSupport` are respectively the coordinate forms of `A h = 1_L` and
`L ∩ supp(b) = {p₁,p₂}`; `hDpoles` is the coordinate form of `D h = h`.
-/

open SimpleGraph

namespace Erdos85

/-- The non-star `D`-commutator summed over two poles is supported at the
two exceptional points.  This is the algebraic core of `(73rnz_cjibkzb)`.
-/
theorem twoPole_defectCommutator_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (M D : Matrix V V (ZMod 2)) (b line : V → ZMod 2)
    {E₁ E₂ G p₁ p₂ : V} (a₁ a₂ : ZMod 2)
    (hp : p₁ ≠ p₂)
    (hAline : ∀ z, M E₁ z + M E₂ z = line z)
    (hDpoles : ∀ z, D E₁ z + D E₂ z =
      if z = E₁ ∨ z = E₂ then 1 else 0)
    (hbE₁ : b E₁ = 0) (hbE₂ : b E₂ = 0)
    (hLineSupport : ∀ z, line z * b z =
      if z = p₁ then a₁ else if z = p₂ then a₂ else 0) :
    (M * Matrix.diagonal b * D + D * Matrix.diagonal b * M) E₁ G +
        (M * Matrix.diagonal b * D + D * Matrix.diagonal b * M) E₂ G =
      a₁ * D p₁ G + a₂ * D p₂ G := by
  simp only [Matrix.add_apply]
  simp_rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero]
  simp
  simp_rw [← Finset.sum_add_distrib]
  calc
    (∑ x : V, ((M E₁ x * b x * D x G + D E₁ x * b x * M x G) +
        (M E₂ x * b x * D x G + D E₂ x * b x * M x G))) =
        (∑ x : V, (M E₁ x + M E₂ x) * b x * D x G) +
          ∑ x : V, (D E₁ x + D E₂ x) * b x * M x G := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = (∑ x, line x * b x * D x G) := by
      rw [show (∑ x, (D E₁ x + D E₂ x) * b x * M x G) = 0 by
        apply Finset.sum_eq_zero
        intro x _
        rw [hDpoles]
        split_ifs with hx
        · rcases hx with rfl | rfl <;> simp [hbE₁, hbE₂]
        · simp]
      simp_rw [hAline]
      simp
    _ = a₁ * D p₁ G + a₂ * D p₂ G := by
      simp_rw [hLineSupport]
      simp only [ite_mul, zero_mul]
      have hsplit : ∀ x : V,
          (if x = p₁ then a₁ * D x G else if x = p₂ then a₂ * D x G else 0) =
            (if x = p₁ then a₁ * D x G else 0) +
              (if x = p₂ then a₂ * D x G else 0) := by
        intro x
        by_cases hx₁ : x = p₁
        · subst x
          simp [hp]
        · by_cases hx₂ : x = p₂
          · subst x
            simp [hx₁]
          · simp [hx₁, hx₂]
      rw [show
        (∑ x : V, if x = p₁ then a₁ * D x G else if x = p₂ then a₂ * D x G else 0) =
          ∑ x : V, ((if x = p₁ then a₁ * D x G else 0) +
            (if x = p₂ then a₂ * D x G else 0)) by
              apply Finset.sum_congr rfl
              intro x _
              exact hsplit x]
      rw [Finset.sum_add_distrib]
      simp

/-- Graph specialization: after the square expansion `(73rnz_cjibkza)`,
the paired flip commutator is exactly the two exceptional atoms claimed in
`(73rnz_cjibkzb)`. -/
theorem twoPole_crossNeighborhood_flipMatrix_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (D J : Matrix V V (ZMod 2)) (b line : V → ZMod 2)
    {E₁ E₂ G p₁ p₂ : V} (a₁ a₂ : ZMod 2)
    (hp : p₁ ≠ p₂)
    (hJ : ∀ i j, J i j = 1)
    (hSquare : A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) = D + J + 1)
    (hE₁G : ¬ A.Adj E₁ G) (hE₂G : ¬ A.Adj E₂ G)
    (hAline : ∀ z, A.adjMatrix (ZMod 2) E₁ z +
      A.adjMatrix (ZMod 2) E₂ z = line z)
    (hDpoles : ∀ z, D E₁ z + D E₂ z =
      if z = E₁ ∨ z = E₂ then 1 else 0)
    (hbE₁ : b E₁ = 0) (hbE₂ : b E₂ = 0)
    (hLineSupport : ∀ z, line z * b z =
      if z = p₁ then a₁ else if z = p₂ then a₂ else 0)
    (hStarE₁ : ∑ x, A.adjMatrix (ZMod 2) E₁ x * b x = a₁)
    (hStarE₂ : ∑ x, A.adjMatrix (ZMod 2) E₂ x * b x = a₂) :
    let M := A.adjMatrix (ZMod 2)
    (M * Matrix.diagonal b * (M * M) + (M * M) * Matrix.diagonal b * M) E₁ G +
        (M * Matrix.diagonal b * (M * M) + (M * M) * Matrix.diagonal b * M) E₂ G =
      a₁ * (1 + D p₁ G) + a₂ * (1 + D p₂ G) := by
  dsimp only
  rw [crossNeighborhood_flipMatrix_eq_starSums_add_defectCommutator
      A D J b hJ hSquare hE₁G,
    crossNeighborhood_flipMatrix_eq_starSums_add_defectCommutator
      A D J b hJ hSquare hE₂G]
  rw [hStarE₁, hStarE₂]
  have hD := twoPole_defectCommutator_sum_eq
    (G := G) (A.adjMatrix (ZMod 2)) D b line a₁ a₂
      hp hAline hDpoles hbE₁ hbE₂ hLineSupport
  let C := A.adjMatrix (ZMod 2) * Matrix.diagonal b * D +
    D * Matrix.diagonal b * A.adjMatrix (ZMod 2)
  change a₁ + (∑ x, b x * A.adjMatrix (ZMod 2) x G) + C E₁ G +
      (a₂ + (∑ x, b x * A.adjMatrix (ZMod 2) x G) + C E₂ G) = _
  change C E₁ G + C E₂ G = _ at hD
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [show
    a₁ + (∑ x, b x * A.adjMatrix (ZMod 2) x G) + C E₁ G +
        (a₂ + (∑ x, b x * A.adjMatrix (ZMod 2) x G) + C E₂ G) =
      a₁ + a₂ + (C E₁ G + C E₂ G) by
        ring_nf
        simp [htwo], hD]
  ring

end Erdos85

#print axioms Erdos85.twoPole_defectCommutator_sum_eq
#print axioms Erdos85.twoPole_crossNeighborhood_flipMatrix_sum_eq
