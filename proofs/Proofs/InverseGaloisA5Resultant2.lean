/-
  Helper module: Sylvester matrix rows 5-8 for the resultant computation.
  See InverseGaloisA5Resultant.lean for the main proof.
-/
import Mathlib

open Polynomial Matrix

namespace InverseGaloisA5Resultant

noncomputable def q : ℚ[X] :=
  X ^ 5 - C 5 * X ^ 4 + C 10 * X ^ 3 - C 10 * X ^ 2 + C 25 * X - C 5

theorem q_natDegree : q.natDegree = 5 := by
  unfold q; compute_degree!

theorem q_derivative_natDegree : (derivative q).natDegree = 4 := by
  unfold q; simp only [derivative_sub, derivative_add, derivative_C_mul, derivative_pow,
    derivative_X, derivative_C]
  compute_degree!

def sylvM : Matrix (Fin 9) (Fin 9) ℚ :=
  of ![
    ![25,   0,   0,   0,   0, -5,   0,   0,  0],
    ![-20, 25,   0,   0,   0, 25,  -5,   0,  0],
    ![30, -20,  25,   0,   0, -10, 25,  -5,  0],
    ![-20, 30, -20,  25,   0, 10, -10,  25, -5],
    ![5,  -20,  30, -20,  25, -5,  10, -10, 25],
    ![0,    5, -20,  30, -20,  1,  -5,  10, -10],
    ![0,    0,   5, -20,  30,  0,   1,  -5, 10],
    ![0,    0,   0,   5, -20,  0,   0,   1, -5],
    ![0,    0,   0,   0,   5,  0,   0,   0,  1]
  ]

theorem r5 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 5 j = sylvM 5 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

theorem r6 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 6 j = sylvM 6 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

theorem r7 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 7 j = sylvM 7 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

theorem r8 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 8 j = sylvM 8 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

end InverseGaloisA5Resultant
