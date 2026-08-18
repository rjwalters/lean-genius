import Mathlib

open Polynomial

namespace Erdos85

noncomputable section

/-- Sum of the `m`-th powers of the complex roots of a complex polynomial,
with multiplicity. -/
def complexRootPowerSum (p : ℂ[X]) (m : ℕ) : ℂ :=
  (p.roots.map fun z => z ^ m).sum

theorem complexRootPowerSum_mul {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    (m : ℕ) :
    complexRootPowerSum (p * q) m =
      complexRootPowerSum p m + complexRootPowerSum q m := by
  rw [complexRootPowerSum, complexRootPowerSum, complexRootPowerSum,
    roots_mul (mul_ne_zero hp hq)]
  simp

theorem complexRootPowerSum_quadratic_two (d : ℂ) :
    complexRootPowerSum (X ^ 2 - C d) 2 = 2 * d := by
  rw [complexRootPowerSum]
  let r := (X ^ 2 - C d).roots
  have hr : r.card = 2 := by
    dsimp [r]
    have hs : Polynomial.Splits (X ^ 2 - C d) := IsAlgClosed.splits _
    rw [← hs.natDegree_eq_card_roots]
    exact ((isMonicOfDegree_X_pow ℂ 2).sub (by simp)).natDegree_eq
  have hroot : ∀ z ∈ r, z ^ 2 = d := by
    intro z hz
    have hz0 := (mem_roots (X_pow_sub_C_ne_zero (R := ℂ) (by norm_num) d)).mp hz
    exact sub_eq_zero.mp (by simpa [IsRoot.def] using hz0)
  change (r.map fun z => z ^ 2).sum = _
  have hmap : r.map (fun z => z ^ 2) = r.map (fun _z => d) := by
    exact Multiset.map_congr rfl hroot
  rw [hmap]
  simp [hr]
  ring

theorem complexRootPowerSum_quadratic_four (d : ℂ) :
    complexRootPowerSum (X ^ 2 - C d) 4 = 2 * d ^ 2 := by
  rw [complexRootPowerSum]
  let r := (X ^ 2 - C d).roots
  have hr : r.card = 2 := by
    dsimp [r]
    have hs : Polynomial.Splits (X ^ 2 - C d) := IsAlgClosed.splits _
    rw [← hs.natDegree_eq_card_roots]
    exact ((isMonicOfDegree_X_pow ℂ 2).sub (by simp)).natDegree_eq
  have hroot : ∀ z ∈ r, z ^ 4 = d ^ 2 := by
    intro z hz
    have hz0 := (mem_roots (X_pow_sub_C_ne_zero (R := ℂ) (by norm_num) d)).mp hz
    have hz2 : z ^ 2 = d := sub_eq_zero.mp (by simpa [IsRoot.def] using hz0)
    rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, hz2]
  change (r.map fun z => z ^ 4).sum = _
  have hmap : r.map (fun z => z ^ 4) = r.map (fun _z => d ^ 2) :=
    Multiset.map_congr rfl hroot
  rw [hmap]
  simp [hr]
  ring

theorem complexRootPowerSum_pow (p : ℂ[X]) (k m : ℕ) :
    complexRootPowerSum (p ^ k) m = k * complexRootPowerSum p m := by
  rw [complexRootPowerSum, roots_pow, complexRootPowerSum]
  induction k with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul, Multiset.map_add, Multiset.sum_add, ih]
      push_cast
      ring

/-- Root-multiset form of the quadratic-sector moment decomposition. -/
theorem complexRootPowerSum_quadratic_pow_mul
    (d : ℂ) (k : ℕ) {Q : ℂ[X]} (hQ : Q ≠ 0) :
    complexRootPowerSum ((X ^ 2 - C d) ^ k * Q) 2 =
        2 * k * d + complexRootPowerSum Q 2 ∧
    complexRootPowerSum ((X ^ 2 - C d) ^ k * Q) 4 =
        2 * k * d ^ 2 + complexRootPowerSum Q 4 := by
  have hbase : (X ^ 2 - C d : ℂ[X]) ≠ 0 :=
    X_pow_sub_C_ne_zero (by norm_num) d
  have hpow : (X ^ 2 - C d : ℂ[X]) ^ k ≠ 0 := pow_ne_zero _ hbase
  constructor
  · rw [complexRootPowerSum_mul hpow hQ,
      complexRootPowerSum_pow, complexRootPowerSum_quadratic_two]
    ring
  · rw [complexRootPowerSum_mul hpow hQ,
      complexRootPowerSum_pow, complexRootPowerSum_quadratic_four]
    ring

/-- A rational polynomial factorization by `(X²-d)^k` gives the exact
second and fourth complex-root power-sum decomposition after base change. -/
theorem rational_quadratic_factor_complexRootPowerSums
    {P Q : ℚ[X]} (d : ℚ) (k : ℕ)
    (hfactor : P = (X ^ 2 - C d) ^ k * Q) (hQ : Q ≠ 0) :
    complexRootPowerSum (P.map (algebraMap ℚ ℂ)) 2 =
        2 * k * (d : ℂ) +
          complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 2 ∧
    complexRootPowerSum (P.map (algebraMap ℚ ℂ)) 4 =
        2 * k * (d : ℂ) ^ 2 +
          complexRootPowerSum (Q.map (algebraMap ℚ ℂ)) 4 := by
  have hQmap : Q.map (algebraMap ℚ ℂ) ≠ 0 :=
    by simpa using
      (Polynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective).ne hQ
  subst P
  simpa using complexRootPowerSum_quadratic_pow_mul (d : ℂ) k hQmap

end

end Erdos85
