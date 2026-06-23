/-
  Main resultant computation file.
  Combines row proofs from Resultant2 (rows 5-8) and this file (rows 0-4),
  then computes the determinant.
-/
import Proofs.InverseGaloisA5Resultant2

open Polynomial Matrix InverseGaloisA5Resultant

namespace InverseGaloisA5Resultant

-- Rows 0-4
theorem r0 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 0 j = sylvM 0 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

theorem r1 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 1 j = sylvM 1 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

theorem r2 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 2 j = sylvM 2 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

theorem r3 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 3 j = sylvM 3 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

theorem r4 : ∀ j : Fin 9, (sylvester q (derivative q) 5 4) 4 j = sylvM 4 j := by
  intro j; unfold sylvM sylvester q
  simp only [of_apply, Fin.addCases, Set.mem_Icc, Fin.val,
    cons_val', cons_val_zero, cons_val_one, empty_val']
  fin_cases j <;> simp [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
    derivative_sub, derivative_add, derivative_C_mul, derivative_pow, derivative_X,
    derivative_C] <;> norm_num

end InverseGaloisA5Resultant
