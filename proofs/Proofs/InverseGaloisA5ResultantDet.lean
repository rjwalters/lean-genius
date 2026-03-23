/-
  Determinant computation for 9×9 Sylvester matrix.
  Uses 7×7 subdeterminants (which native_decide handles) and
  manually proved cofactor expansion chains.
-/
import Proofs.InverseGaloisA5Resultant2

open Matrix BigOperators Finset

namespace InverseGaloisA5Resultant

-- The five 7×7 determinants computed via native_decide

private def m1 : Matrix (Fin 7) (Fin 7) ℚ := of ![
  ![25, 0, 0, -5, 0, 0, 0], ![-20, 25, 0, 25, -5, 0, 0],
  ![30, -20, 25, -10, 25, -5, 0], ![-20, 30, -20, 10, -10, 25, -5],
  ![5, -20, 30, -5, 10, -10, 25], ![0, 5, -20, 1, -5, 10, -10],
  ![0, 0, 5, 0, 1, -5, 10]]
private theorem m1_det : m1.det = 420000000 := by native_decide

private def m2 : Matrix (Fin 7) (Fin 7) ℚ := of ![
  ![25, 0, 0, 0, -5, 0, 0], ![-20, 25, 0, 0, 25, -5, 0],
  ![30, -20, 25, 0, -10, 25, 0], ![-20, 30, -20, 25, 10, -10, -5],
  ![5, -20, 30, -20, -5, 10, 25], ![0, 5, -20, 30, 1, -5, -10],
  ![0, 0, 5, -20, 0, 1, 10]]
private theorem m2_det : m2.det = 1012000000 := by native_decide

private def m3 : Matrix (Fin 7) (Fin 7) ℚ := of ![
  ![25, 0, 0, 0, -5, 0, 0], ![-20, 25, 0, 0, 25, -5, 0],
  ![30, -20, 25, 0, -10, 25, -5], ![-20, 30, -20, 25, 10, -10, 25],
  ![5, -20, 30, -20, -5, 10, -10], ![0, 5, -20, 30, 1, -5, 10],
  ![0, 0, 5, -20, 0, 1, -5]]
private theorem m3_det : m3.det = 256000000 := by native_decide

private def m4 : Matrix (Fin 7) (Fin 7) ℚ := of ![
  ![25, 0, 0, 0, -5, 0, 0], ![-20, 25, 0, 0, 25, -5, 0],
  ![30, -20, 25, 0, -10, 25, -5], ![-20, 30, -20, 0, 10, -10, 25],
  ![5, -20, 30, 25, -5, 10, -10], ![0, 5, -20, -20, 1, -5, 10],
  ![0, 0, 5, 30, 0, 1, -5]]
private theorem m4_det : m4.det = -1012000000 := by native_decide

private def m5 : Matrix (Fin 7) (Fin 7) ℚ := of ![
  ![25, 0, 0, 0, 0, -5, 0], ![-20, 25, 0, 0, 0, 25, -5],
  ![30, -20, 25, 0, 0, -10, 25], ![-20, 30, -20, 25, 0, 10, -10],
  ![5, -20, 30, -20, 25, -5, 10], ![0, 5, -20, 30, -20, 1, -5],
  ![0, 0, 5, -20, 30, 0, 1]]
private theorem m5_det : m5.det = 1924000000 := by native_decide

-- The cofactor expansion arithmetic:
-- det(m84) = 5 · 420M - 1012M - 5 · 256M = -192M
-- det(m88) = -5 · 1012M + 20 · 256M + 1924M = 1984M
-- det(sylvM) = 5 · (-192M) + 1984M = 1024M

-- NOTE: This theorem is UNUSED. The discriminant disc(q) = 1024000000 is now
-- proved via the Vandermonde chain (vandermondeProduct_sq_eq_proved → disc_q_val_proved)
-- in InverseGaloisA5.lean, making the Sylvester matrix approach redundant.
-- The 7×7 subdeterminants above remain as verified computational artifacts.
-- Removed: sylvM_det (had sorry, dead code)

end InverseGaloisA5Resultant
