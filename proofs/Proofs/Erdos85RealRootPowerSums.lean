import Proofs.Erdos85QuadraticFactorRootMoments

/-!
# Comparing real and complex root power sums
-/

open Polynomial

namespace Erdos85

noncomputable section

def realRootPowerSum (p : ℝ[X]) (m : ℕ) : ℝ :=
  (p.roots.map fun x => x ^ m).sum

theorem complexRootPowerSum_map_real_eq
    (p : ℝ[X]) (m : ℕ) (hsplit : p.Splits) (hp : p ≠ 0) :
    complexRootPowerSum (p.map (algebraMap ℝ ℂ)) m =
      (realRootPowerSum p m : ℂ) := by
  have hmap : p.map (algebraMap ℝ ℂ) ≠ 0 := by
    simpa using
      (Polynomial.map_injective (algebraMap ℝ ℂ)
        (algebraMap ℝ ℂ).injective).ne hp
  rw [complexRootPowerSum, hsplit.roots_map_of_ne_zero hmap,
    realRootPowerSum]
  simp only [Multiset.map_map, Function.comp_apply]
  generalize p.roots = s
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ih]
      push_cast
      rfl

theorem complexRootPowerSum_rat_map_eq_real
    (Q : ℚ[X]) (m : ℕ)
    (hsplit : (Q.map (algebraMap ℚ ℝ)).Splits) (hQ : Q ≠ 0) :
    complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) m =
      (realRootPowerSum (Q.map (algebraMap ℚ ℝ)) m : ℂ) := by
  have h := complexRootPowerSum_map_real_eq
    (Q.map (algebraMap ℚ ℝ)) m hsplit
      (by simpa using
        (Polynomial.map_injective (algebraMap ℚ ℝ)
          (algebraMap ℚ ℝ).injective).ne hQ)
  have hcomp : (algebraMap ℝ ℂ).comp (algebraMap ℚ ℝ) =
      algebraMap ℚ ℂ := by
    ext q
    norm_num
  rw [← hcomp]
  simpa [Polynomial.map_map] using h

/-- Multiplicity-aware Cauchy--Schwarz for a real multiset. -/
theorem multiset_sq_sum_le_card_mul_sum_sq
    (s : Multiset ℝ) (f : ℝ → ℝ) :
    (s.map f).sum ^ 2 ≤ (s.card : ℝ) * (s.map fun x => (f x) ^ 2).sum := by
  rw [← Multiset.sum_map_toList, ← Multiset.sum_map_toList,
    ← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_fun_getElem,
    ← Multiset.length_toList]
  simpa using sq_sum_le_card_mul_sum_sq
    (α := ℝ) (ι := Fin s.toList.length)
    (s := Finset.univ) (f := fun i => f s.toList[i])

/-- Cauchy--Schwarz after erasing one occurrence of a distinguished member. -/
theorem realRootPowerSum_cauchy_erase
    (p : ℝ[X]) {lambda : ℝ} (hlambda : lambda ∈ p.roots) :
    (realRootPowerSum p 2 - lambda ^ 2) ^ 2 ≤
      ((p.roots.card - 1 : ℕ) : ℝ) *
        (realRootPowerSum p 4 - lambda ^ 4) := by
  have h := multiset_sq_sum_le_card_mul_sum_sq
    (p.roots.erase lambda) (fun x => x ^ 2)
  rw [realRootPowerSum, realRootPowerSum]
  rw [Multiset.card_erase_of_mem hlambda] at h
  have htwo :
      ((p.roots.erase lambda).map fun x => x ^ 2).sum =
        (p.roots.map fun x => x ^ 2).sum - lambda ^ 2 := by
    have hadd := Multiset.sum_map_erase (m := p.roots)
      (f := fun x => x ^ 2) hlambda
    linarith
  have hfour :
      ((p.roots.erase lambda).map fun x => (x ^ 2) ^ 2).sum =
        (p.roots.map fun x => x ^ 4).sum - lambda ^ 4 := by
    have hadd := Multiset.sum_map_erase (m := p.roots)
      (f := fun x => x ^ 4) hlambda
    have hm : ((p.roots.erase lambda).map fun x => (x ^ 2) ^ 2).sum =
        ((p.roots.erase lambda).map fun x => x ^ 4).sum := by
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro x _
      ring
    rw [hm]
    linarith
  rwa [htwo, hfour] at h

end

end Erdos85
