import Proofs.Erdos85ColorSectorIncidence

/-!
# A weighted positivity obstruction for the color-sector quotient

Detailed balance symmetrizes the complementary two-step matrix.  In degree
six, the independent diagonal-two sector would have transverse eigenvalue
`-1`.  The theorem below proves the resulting impossibility without square
roots: an explicit weighted sum of integer squares would have to be negative.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Two vertices cannot satisfy the degree-six complementary incidence
identities together with detailed balance.  This is the two-coordinate,
denominator-free form of positive semidefiniteness. -/
theorem false_of_degreeSix_complementary_incidence_pair
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (T : Finset C)
    (c e : C) (hcpos : 0 < size c) (hepos : 0 < size e)
    (hbal : ∀ i j, size i * Q i j = size j * Q j i)
    (hcc : (∑ j ∈ T, Q c j * Q j c) + 1 = size c)
    (hee : (∑ j ∈ T, Q e j * Q j e) + 1 = size e)
    (hce : (∑ j ∈ T, Q c j * Q j e) = size e)
    (hec : (∑ j ∈ T, Q e j * Q j c) = size c) : False := by
  let L : ℤ := ∑ j ∈ T, (size j : ℤ) *
    ((Q j c : ℤ) * (size e : ℤ) - (Q j e : ℤ) * (size c : ℤ)) ^ 2
  have hLnonneg : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro j hj
    positivity
  have hbalc (j : C) :
      (size j : ℤ) * (Q j c : ℤ) = (size c : ℤ) * (Q c j : ℤ) := by
    exact_mod_cast hbal j c
  have hbale (j : C) :
      (size j : ℤ) * (Q j e : ℤ) = (size e : ℤ) * (Q e j : ℤ) := by
    exact_mod_cast hbal j e
  have hLexpand : L =
      (size e : ℤ) ^ 2 * (size c : ℤ) *
          (∑ j ∈ T, (Q c j : ℤ) * (Q j c : ℤ)) -
        2 * (size e : ℤ) * (size c : ℤ) ^ 2 *
          (∑ j ∈ T, (Q c j : ℤ) * (Q j e : ℤ)) +
        (size c : ℤ) ^ 2 * (size e : ℤ) *
          (∑ j ∈ T, (Q e j : ℤ) * (Q j e : ℤ)) := by
    unfold L
    calc
      (∑ j ∈ T, (size j : ℤ) *
          ((Q j c : ℤ) * (size e : ℤ) -
            (Q j e : ℤ) * (size c : ℤ)) ^ 2) =
          ∑ j ∈ T,
            ((size e : ℤ) ^ 2 * (size c : ℤ) *
                ((Q c j : ℤ) * (Q j c : ℤ)) -
              2 * (size e : ℤ) * (size c : ℤ) ^ 2 *
                ((Q c j : ℤ) * (Q j e : ℤ)) +
              (size c : ℤ) ^ 2 * (size e : ℤ) *
                ((Q e j : ℤ) * (Q j e : ℤ))) := by
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (size j : ℤ) *
              ((Q j c : ℤ) * (size e : ℤ) -
                (Q j e : ℤ) * (size c : ℤ)) ^ 2 =
              ((size j : ℤ) * (Q j c : ℤ)) * (Q j c : ℤ) *
                  (size e : ℤ) ^ 2 -
                2 * (size e : ℤ) * (size c : ℤ) *
                  ((size j : ℤ) * (Q j c : ℤ)) * (Q j e : ℤ) +
                ((size j : ℤ) * (Q j e : ℤ)) * (Q j e : ℤ) *
                  (size c : ℤ) ^ 2 := by ring
          _ = _ := by rw [hbalc j, hbale j]; ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
  have hccZ :
      (∑ j ∈ T, (Q c j : ℤ) * (Q j c : ℤ)) + 1 = (size c : ℤ) := by
    exact_mod_cast hcc
  have heeZ :
      (∑ j ∈ T, (Q e j : ℤ) * (Q j e : ℤ)) + 1 = (size e : ℤ) := by
    exact_mod_cast hee
  have hceZ :
      (∑ j ∈ T, (Q c j : ℤ) * (Q j e : ℤ)) = (size e : ℤ) := by
    exact_mod_cast hce
  rw [hLexpand, hceZ] at hLnonneg
  have hcZ : (0 : ℤ) < size c := by exact_mod_cast hcpos
  have heZ : (0 : ℤ) < size e := by exact_mod_cast hepos
  have hccZ' : (∑ j ∈ T, (Q c j : ℤ) * (Q j c : ℤ)) =
      (size c : ℤ) - 1 := by omega
  have heeZ' : (∑ j ∈ T, (Q e j : ℤ) * (Q j e : ℤ)) =
      (size e : ℤ) - 1 := by omega
  rw [hccZ', heeZ'] at hLnonneg
  have hnegative :
      (size e : ℤ) ^ 2 * (size c : ℤ) * ((size c : ℤ) - 1) -
          2 * (size e : ℤ) * (size c : ℤ) ^ 2 * (size e : ℤ) +
          (size c : ℤ) ^ 2 * (size e : ℤ) * ((size e : ℤ) - 1) =
        -((size c : ℤ) * (size e : ℤ) *
          ((size c : ℤ) + (size e : ℤ))) := by ring
  rw [hnegative] at hLnonneg
  have hprod : 0 < (size c : ℤ) * (size e : ℤ) *
      ((size c : ℤ) + (size e : ℤ)) := by positivity
  omega

/-- In a degree-six Moore quotient, an independent diagonal-two sector has at
most one element.  Detailed balance is what turns the nonsymmetric quotient
factorization into the weighted sum-of-squares obstruction above. -/
theorem independent_diagonal_two_sector_card_le_one_of_degreeSix
    {C : Type*} [Fintype C] [DecidableEq C]
    (Q : Matrix C C ℕ) (size : C → ℕ) (S : Finset C)
    (hsize : ∀ c, 0 < size c)
    (hsq : ∀ c e, (Q * Q) c e =
      3 * (if c = e then 1 else 0) + size e)
    (hdiag : ∀ c ∈ S, Q c c = 2)
    (hoff : ∀ c ∈ S, ∀ e ∈ S, c ≠ e → Q c e = 0)
    (hbal : ∀ c e, size c * Q c e = size e * Q e c) :
    S.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c hc e he
  by_contra hce
  let T := Finset.univ.filter (fun j : C ↦ j ∉ S)
  have hcc0 :=
    sum_complementary_products_self_of_independent_diagonal_two_sector
      Q size 3 S hsq hdiag hoff hc
  have hee0 :=
    sum_complementary_products_self_of_independent_diagonal_two_sector
      Q size 3 S hsq hdiag hoff he
  have hce0 :=
    sum_complementary_products_eq_of_independent_diagonal_two_sector
      Q size 3 S hsq hoff hc he hce
  have hec0 :=
    sum_complementary_products_eq_of_independent_diagonal_two_sector
      Q size 3 S hsq hoff he hc (fun h ↦ hce h.symm)
  have hcc : (∑ j ∈ T, Q c j * Q j c) + 1 = size c := by
    dsimp [T]
    omega
  have hee : (∑ j ∈ T, Q e j * Q j e) + 1 = size e := by
    dsimp [T]
    omega
  exact false_of_degreeSix_complementary_incidence_pair Q size T c e
    (hsize c) (hsize e) hbal hcc hee hce0 hec0

/-- **Degree-six color-sector rigidity.**  At the exact Moore boundary, a
degree-six graph has at most one triangle-free-colored second-order defect
component. -/
theorem degreeSix_triangleFreeCycleSector_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 6 * (6 - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hr : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard) :
    (triangleFreeCycleSector G u).card ≤ 1 := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let size : D.ConnectedComponent → ℕ := fun c ↦ c.supp.ncard
  apply independent_diagonal_two_sector_card_le_one_of_degreeSix
    Q size (triangleFreeCycleSector G u)
  · intro c
    exact lt_of_lt_of_le (by norm_num) (hr c)
  · intro c e
    have hs := secondOrder_componentQuotientMatrix_sq_apply G hfree
      (d := 6) (by norm_num) (by norm_num) hmin hcard c e
    simpa [Q, size, D] using hs
  · intro c hc
    exact triangleFreeCycleSector_diagonalQuotient_eq_two G hfree
      (d := 6) (by norm_num) (by norm_num) hmin hcard u hu huRange huD hr hc
  · intro c hc e he hce
    exact triangleFreeCycleSector_offDiagonalQuotient_eq_zero G hfree
      (d := 6) (by norm_num) (by norm_num) hmin hcard u hu huRange huD hr
      hc he hce
  · intro c e
    exact secondOrder_componentQuotientMatrix_balance G hfree
      (d := 6) (by norm_num) (by norm_num) hmin hcard c e

end

end Erdos85
