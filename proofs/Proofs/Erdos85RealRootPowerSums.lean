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

end

end Erdos85
