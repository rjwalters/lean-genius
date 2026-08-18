import Proofs.Erdos85FiniteFieldNonsquare
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! Coordinate calculation excluding absolute cross-edge endpoints. -/

namespace Erdos85

open Matrix

universe u

def switchNormalizedA {K : Type u} [Field K] (A B X : Fin 3 → K) : Fin 3 → K :=
  (-(X ⬝ᵥ X) / (2 * (A ⬝ᵥ B))) • A

def polaritySwitchVector {K : Type u} [Field K]
    (A B X : Fin 3 → K) (t : K) : Fin 3 → K :=
  X + t • (B - switchNormalizedA A B X)

theorem dot_switchVector_left {K : Type u} [Field K]
    (A B X : Fin 3 → K) (t : K)
    (hAA : A ⬝ᵥ A = 0) (hXA : X ⬝ᵥ A = 0) :
    A ⬝ᵥ polaritySwitchVector A B X t = t * (A ⬝ᵥ B) := by
  have hAX : A ⬝ᵥ X = 0 := by rw [dotProduct_comm]; exact hXA
  simp [polaritySwitchVector, switchNormalizedA, dotProduct_add,
    dotProduct_smul, dotProduct_sub, hAX, hAA]

theorem dot_switchVector_common {K : Type u} [Field K]
    (A B X : Fin 3 → K) (t : K)
    (hXA : X ⬝ᵥ A = 0) (hXB : X ⬝ᵥ B = 0) :
    X ⬝ᵥ polaritySwitchVector A B X t = X ⬝ᵥ X := by
  simp [polaritySwitchVector, switchNormalizedA, dotProduct_add,
    dotProduct_smul, dotProduct_sub, hXA, hXB]

theorem dot_switchVector_right {K : Type u} [Field K]
    (h2 : (2 : K) ≠ 0) (A B X : Fin 3 → K) (t : K)
    (hBB : B ⬝ᵥ B = 0) (hXB : X ⬝ᵥ B = 0) (hAB : A ⬝ᵥ B ≠ 0) :
    B ⬝ᵥ polaritySwitchVector A B X t = t * (X ⬝ᵥ X) / 2 := by
  have hBX : B ⬝ᵥ X = 0 := by rw [dotProduct_comm]; exact hXB
  have hBA : B ⬝ᵥ A = A ⬝ᵥ B := dotProduct_comm B A
  simp only [polaritySwitchVector, switchNormalizedA, dotProduct_add,
    dotProduct_smul, dotProduct_sub, smul_eq_mul, hBX, zero_add, hBB,
    zero_sub, hBA]
  field_simp [h2, hAB]

theorem polaritySwitchVector_ne_zero {K : Type u} [Field K]
    (A B X : Fin 3 → K) (t : K)
    (hXA : X ⬝ᵥ A = 0) (hXB : X ⬝ᵥ B = 0) (hXX : X ⬝ᵥ X ≠ 0) :
    polaritySwitchVector A B X t ≠ 0 := by
  intro hz
  have h := dot_switchVector_common A B X t hXA hXB
  rw [hz, dotProduct_zero] at h
  exact hXX h.symm

/-- Normalize one isotropic representative so its pairing with the other is
`-X²/2`.  For the resulting switch pencil, every explicitly parametrized
opposite cross-edge endpoint is nonisotropic when `1+t²` is a nonsquare. -/
theorem switch_opposite_vector_not_isotropic {K : Type u} [Field K]
    (h2 : (2 : K) ≠ 0) (A B X : Fin 3 → K)
    (hAA : A ⬝ᵥ A = 0) (hBB : B ⬝ᵥ B = 0)
    (hAB : A ⬝ᵥ B ≠ 0) (hXA : X ⬝ᵥ A = 0)
    (hXB : X ⬝ᵥ B = 0) (hXX : X ⬝ᵥ X ≠ 0)
    {t : K} (ht : ¬ IsSquare (1 + t ^ 2)) (z : K) :
    let A' := (-(X ⬝ᵥ X) / (2 * (A ⬝ᵥ B))) • A
    let V := (-z) • A' + B + (-(t * (z + 1) / 2)) • X
    V ⬝ᵥ V ≠ 0 := by
  dsimp
  have hBA : B ⬝ᵥ A = A ⬝ᵥ B := dotProduct_comm B A
  have hAX : A ⬝ᵥ X = 0 := by rw [dotProduct_comm]; exact hXA
  have hBX : B ⬝ᵥ X = 0 := by rw [dotProduct_comm]; exact hXB
  have hq := switch_quadratic_ne_zero h2 ht z
  intro hv
  apply hq
  simp only [add_dotProduct, dotProduct_add, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hAA, hBB, hXA, hXB, hAX, hBX,
    hBA] at hv
  field_simp [h2, hAB, hXX] at hv
  ring_nf at hv
  have hp : (X ⬝ᵥ X) * (A ⬝ᵥ B) ^ 2 *
      (t ^ 2 * (z + 1) ^ 2 + 4 * z) = 0 := by
    calc
      _ = z * (X ⬝ᵥ X) * (A ⬝ᵥ B) ^ 2 * 4 +
          z * (X ⬝ᵥ X) * (A ⬝ᵥ B) ^ 2 * t ^ 2 * 2 +
          z ^ 2 * (X ⬝ᵥ X) * (A ⬝ᵥ B) ^ 2 * t ^ 2 +
          (X ⬝ᵥ X) * (A ⬝ᵥ B) ^ 2 * t ^ 2 := by ring
      _ = 0 := hv
  exact (mul_eq_zero.mp hp).resolve_left
    (mul_ne_zero hXX (pow_ne_zero 2 hAB))

end Erdos85
