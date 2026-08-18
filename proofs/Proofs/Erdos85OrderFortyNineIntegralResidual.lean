import Proofs.Erdos85OrderFortyNineResidualCoefficients
import Proofs.Erdos85FrequencyPairTransport
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Integral residual characteristic factor at order forty-nine

Gauss's lemma upgrades the rational high-sector quotient to a monic integer
polynomial.  This makes the exact residual coefficients available for modular
arguments, rather than merely as rational identities.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

theorem exists_monic_integral_orderFortyNineSeven_residualCharpoly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 7 ∨ G.degree v = 7)
    (hcard : Fintype.card V = 49)
    {a : V} (ha : a ∈ squareOrderHighVertices G 7) :
    ∃ R : ℤ[X],
      R.Monic ∧
      (G.adjMatrix ℤ).charpoly =
        (X ^ 2 - C 7) ^ ((squareOrderHighVertices G 7).card - 1) * R ∧
      R.natDegree = 49 - 2 * ((squareOrderHighVertices G 7).card - 1) ∧
      R.nextCoeff = 0 ∧
      2 * R.coeff (R.natDegree - 2) =
        -(357 - 13 * ((squareOrderHighVertices G 7).card : ℤ)) ∧
      8 * R.coeff (R.natDegree - 4) =
        169 * ((squareOrderHighVertices G 7).card : ℤ) ^ 2 -
          9144 * ((squareOrderHighVertices G 7).card : ℤ) + 118335 := by
  obtain ⟨Q, hQmonic, hfactorQ, hdegreeQ, hnextQ, hc₂Q, hc₄Q⟩ :=
    exists_orderFortyNineSeven_residualCharpoly_coefficients
      G hfree hmin hcover hcard ha
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  let P : ℤ[X] := (G.adjMatrix ℤ).charpoly
  let F : ℤ[X] :=
    (X ^ 2 - C 7) ^ ((squareOrderHighVertices G 7).card - 1)
  have hPmonic : P.Monic := (G.adjMatrix ℤ).charpoly_monic
  have hf : Function.Injective f := by
    exact Int.cast_injective
  have hFbase : (X ^ 2 - C (7 : ℤ)).Monic :=
    ((isMonicOfDegree_X_pow ℤ 2).sub (by simp)).monic
  have hFmonic : F.Monic := hFbase.pow _
  have hadjMap : (G.adjMatrix ℤ).map f = G.adjMatrix ℚ := by
    exact adjMatrix_map_intCast G
  have hPmap : P.map f = (G.adjMatrix ℚ).charpoly := by
    dsimp [P]
    rw [← Matrix.charpoly_map, hadjMap]
  have hFmap : F.map f =
      (X ^ 2 - C (7 : ℚ)) ^
        ((squareOrderHighVertices G 7).card - 1) := by
    have hb : (X ^ 2 - C (7 : ℤ)).map f =
        (X ^ 2 - C (7 : ℚ)) := by
      simp only [Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
      rfl
    simpa [F, map_pow] using congrArg
      (fun p : ℚ[X] => p ^ ((squareOrderHighVertices G 7).card - 1)) hb
  have hdivQ : F.map f ∣ P.map f := by
    refine ⟨Q, ?_⟩
    rw [hPmap, hFmap]
    exact hfactorQ
  have hdivZ : F ∣ P :=
    (hPmonic.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ) hFmonic).mp hdivQ
  obtain ⟨R, hR⟩ := hdivZ
  have hRmonic : R.Monic := by
    apply hFmonic.of_mul_monic_left
    rw [← hR]
    exact hPmonic
  have hRmap : R.map f = Q := by
    have hmapped := congrArg (Polynomial.map f) hR
    rw [Polynomial.map_mul, hPmap, hFmap] at hmapped
    have heq :
        (X ^ 2 - C (7 : ℚ)) ^
              ((squareOrderHighVertices G 7).card - 1) * R.map f =
          (X ^ 2 - C (7 : ℚ)) ^
              ((squareOrderHighVertices G 7).card - 1) * Q := by
      rw [← hmapped, ← hfactorQ]
    exact mul_left_cancel₀
      (pow_ne_zero _ (X_pow_sub_C_ne_zero (by norm_num) (7 : ℚ))) heq
  have hdegreeR : R.natDegree = Q.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective hf R, hRmap]
  have hnextR : R.nextCoeff = 0 := by
    have hm := congrArg Polynomial.nextCoeff hRmap
    rw [Polynomial.nextCoeff_map hf, hnextQ] at hm
    exact hf (by simpa using hm)
  have hc₂R :
      2 * R.coeff (R.natDegree - 2) =
        -(357 - 13 * ((squareOrderHighVertices G 7).card : ℤ)) := by
    have hc := hc₂Q
    rw [← hRmap] at hc
    simp only [coeff_map, Polynomial.natDegree_map_eq_of_injective hf] at hc
    apply Int.cast_injective (α := ℚ)
    push_cast
    simpa [f] using hc
  have hc₄R :
      8 * R.coeff (R.natDegree - 4) =
        169 * ((squareOrderHighVertices G 7).card : ℤ) ^ 2 -
          9144 * ((squareOrderHighVertices G 7).card : ℤ) + 118335 := by
    have hc := hc₄Q
    rw [← hRmap] at hc
    simp only [coeff_map, Polynomial.natDegree_map_eq_of_injective hf] at hc
    apply Int.cast_injective (α := ℚ)
    push_cast
    simpa [f] using hc
  refine ⟨R, hRmonic, ?_, ?_, hnextR, hc₂R, hc₄R⟩
  · exact hR
  · rw [hdegreeR, hdegreeQ]

end

end Erdos85
