/-
  Symmetries of the commutant dimension: similarity and transpose invariance
  (cayley-hamilton-cyclic-vector-all-fields-oq-02-oq-02)

  The sibling files pin the Frobenius commutant range `n ≤ dim_K C(M) ≤ n²`:

    * `...OQ02OQ02`       — `dim_K C(M) = n` exactly for nonderogatory `M` (lower end);
    * `...OQ02OQ02Scalar` — `dim_K C(c • I) = n²` for a scalar matrix (upper end);
    * `...OQ02OQ02Range`  — the two-sided bound `n ≤ dim_K C(M) ≤ n²` for every `M`.

  A structural fact left implicit throughout is *why* this analysis only depends on
  the rational-canonical / invariant-factor data of `M`: the commutant dimension is a
  **similarity invariant**, and it is moreover **transpose invariant**.  This file
  makes both symmetries explicit and `0`-axiom.

    * `conjLinearEquiv u` — conjugation `X ↦ u X u⁻¹` by a unit `u : Mₙ(K)ˣ`, packaged
      as a `K`-linear automorphism of `Mₙ(K)`.
    * `map_conj_centralizer` — this automorphism carries the commutant of `M` onto the
      commutant of the conjugate `u M u⁻¹`:  `C(M).map (X ↦ uXu⁻¹) = C(u M u⁻¹)`.
    * `finrank_centralizer_conj` — **similarity invariance**:
      `dim_K C(u M u⁻¹) = dim_K C(M)` for every unit `u`.  Conjugate (similar)
      matrices have commutants of the same dimension; in particular the whole
      Frobenius range analysis is a similarity invariant.
    * `map_transpose_centralizer` / `finrank_centralizer_transpose` — **transpose
      invariance**: `dim_K C(Mᵀ) = dim_K C(M)`.  Transposition is a linear
      anti-automorphism, so it maps `C(M)` bijectively onto `C(Mᵀ)`.
    * `finrank_centralizer_conj_transpose` — the combined statement
      `dim_K C((u M u⁻¹)ᵀ) = dim_K C(M)`.

  All results are `0`-sorry / `0`-axiom on top of Mathlib.
-/
import Mathlib

open Matrix Polynomial

noncomputable section

namespace CyclicCommutantSymmetry

variable {K : Type*} [Field K] {n : ℕ}

/-! ### Conjugation by a unit as a linear automorphism -/

/-- **Conjugation `X ↦ u X u⁻¹` by a unit is `K`-linear.**  For an invertible matrix
    `u : Mₙ(K)ˣ`, the map `X ↦ u X u⁻¹` is a `K`-linear automorphism of `Mₙ(K)`, with
    inverse `X ↦ u⁻¹ X u`.  (Multiplication by fixed matrices on either side is linear,
    and the two-sided cancellation `u⁻¹ u = u u⁻¹ = 1` provides the inverse.) -/
def conjLinearEquiv (u : (Matrix (Fin n) (Fin n) K)ˣ) :
    Matrix (Fin n) (Fin n) K ≃ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun X := u.val * X * (u⁻¹).val
  invFun X := (u⁻¹).val * X * u.val
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' c X := by simp only [RingHom.id_apply, mul_smul_comm, smul_mul_assoc]
  left_inv X := by
    show (u⁻¹).val * (u.val * X * (u⁻¹).val) * u.val = X
    rw [mul_assoc, Units.inv_mul_cancel_right, Units.inv_mul_cancel_left]
  right_inv X := by
    show u.val * ((u⁻¹).val * X * u.val) * (u⁻¹).val = X
    rw [mul_assoc, Units.mul_inv_cancel_right, Units.mul_inv_cancel_left]

@[simp]
theorem conjLinearEquiv_apply (u : (Matrix (Fin n) (Fin n) K)ˣ)
    (X : Matrix (Fin n) (Fin n) K) :
    conjLinearEquiv u X = u.val * X * (u⁻¹).val := rfl

/-- Conjugation is multiplicative: `(u A u⁻¹)(u B u⁻¹) = u (A B) u⁻¹`. -/
theorem conj_mul (u : (Matrix (Fin n) (Fin n) K)ˣ) (A B : Matrix (Fin n) (Fin n) K) :
    (u.val * A * (u⁻¹).val) * (u.val * B * (u⁻¹).val) = u.val * (A * B) * (u⁻¹).val := by
  simp only [mul_assoc]
  rw [Units.inv_mul_cancel_left]

/-! ### Similarity invariance of the commutant -/

/-- **Conjugation carries `C(M)` onto `C(u M u⁻¹)`.**  The linear automorphism
    `X ↦ u X u⁻¹` maps the commutant submodule of `M` exactly onto the commutant
    submodule of the conjugate `u M u⁻¹`. -/
theorem map_conj_centralizer (u : (Matrix (Fin n) (Fin n) K)ˣ)
    (M : Matrix (Fin n) (Fin n) K) :
    Submodule.map (conjLinearEquiv u).toLinearMap
        (Subalgebra.toSubmodule
          (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))))
      = Subalgebra.toSubmodule
          (Subalgebra.centralizer K
            ({u.val * M * (u⁻¹).val} : Set (Matrix (Fin n) (Fin n) K))) := by
  ext X
  simp only [Submodule.mem_map, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq, LinearEquiv.coe_coe, conjLinearEquiv_apply]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    rw [conj_mul, conj_mul, hY]
  · intro hX
    refine ⟨(u⁻¹).val * X * u.val, ?_, ?_⟩
    · have e1 : (u⁻¹).val * ((u.val * M * (u⁻¹).val) * X) * u.val
          = M * ((u⁻¹).val * X * u.val) := by
        simp only [mul_assoc]; rw [Units.inv_mul_cancel_left]
      have e2 : (u⁻¹).val * (X * (u.val * M * (u⁻¹).val)) * u.val
          = ((u⁻¹).val * X * u.val) * M := by
        simp only [mul_assoc]; rw [Units.inv_mul, mul_one]
      rw [← e1, ← e2, hX]
    · simp only [mul_assoc]
      rw [Units.mul_inv_cancel_left, Units.mul_inv, mul_one]

/-- **Similarity invariance of the commutant dimension.**  For every unit
    `u : Mₙ(K)ˣ` and every matrix `M`, the conjugate `u M u⁻¹` has a commutant of the
    same `K`-dimension as `M`:

      `dim_K C(u M u⁻¹) = dim_K C(M)`.

    Conjugation `X ↦ u X u⁻¹` is a linear automorphism carrying `C(M)` onto
    `C(u M u⁻¹)` (`map_conj_centralizer`), so the two subspaces are isomorphic and
    have equal finrank.  In particular the position of `dim_K C(M)` inside the
    Frobenius range `[n, n²]` depends only on the similarity class of `M`. -/
theorem finrank_centralizer_conj (u : (Matrix (Fin n) (Fin n) K)ˣ)
    (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K
          ({u.val * M * (u⁻¹).val} : Set (Matrix (Fin n) (Fin n) K)))
      = Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) := by
  rw [← Subalgebra.finrank_toSubmodule
        (Subalgebra.centralizer K
          ({u.val * M * (u⁻¹).val} : Set (Matrix (Fin n) (Fin n) K))),
      ← Subalgebra.finrank_toSubmodule
        (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))),
      ← map_conj_centralizer u M,
      ← LinearEquiv.finrank_eq
        ((conjLinearEquiv u).submoduleMap
          (Subalgebra.toSubmodule
            (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))))]

/-! ### Transpose invariance of the commutant -/

/-- **Transposition carries `C(M)` onto `C(Mᵀ)`.**  The linear automorphism `X ↦ Xᵀ`
    maps the commutant submodule of `M` exactly onto the commutant submodule of `Mᵀ`.
    (Transposition reverses products, `(AB)ᵀ = BᵀAᵀ`, so it turns `M X = X M` into
    `Xᵀ Mᵀ = Mᵀ Xᵀ`.) -/
theorem map_transpose_centralizer (M : Matrix (Fin n) (Fin n) K) :
    Submodule.map (transposeLinearEquiv (Fin n) (Fin n) K K).toLinearMap
        (Subalgebra.toSubmodule
          (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))))
      = Subalgebra.toSubmodule
          (Subalgebra.centralizer K ({Mᵀ} : Set (Matrix (Fin n) (Fin n) K))) := by
  ext X
  simp only [Submodule.mem_map, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq, LinearEquiv.coe_coe, transposeLinearEquiv_apply]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    show Mᵀ * Yᵀ = Yᵀ * Mᵀ
    rw [← transpose_mul, ← transpose_mul, hY]
  · intro hX
    refine ⟨Xᵀ, ?_, ?_⟩
    · have h := congrArg Matrix.transpose hX
      simp only [transpose_mul, transpose_transpose] at h
      exact h.symm
    · show (Xᵀ)ᵀ = X
      rw [transpose_transpose]

/-- **Transpose invariance of the commutant dimension.**  For every matrix `M`,

      `dim_K C(Mᵀ) = dim_K C(M)`.

    Transposition `X ↦ Xᵀ` is a linear automorphism carrying `C(M)` onto `C(Mᵀ)`
    (`map_transpose_centralizer`), so the two commutants have equal `K`-dimension.
    Together with `finrank_centralizer_conj` this shows the commutant dimension is
    invariant under the full "similarity + transpose" symmetry of `Mₙ(K)`. -/
theorem finrank_centralizer_transpose (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K ({Mᵀ} : Set (Matrix (Fin n) (Fin n) K)))
      = Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) := by
  rw [← Subalgebra.finrank_toSubmodule
        (Subalgebra.centralizer K ({Mᵀ} : Set (Matrix (Fin n) (Fin n) K))),
      ← Subalgebra.finrank_toSubmodule
        (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))),
      ← map_transpose_centralizer M,
      ← LinearEquiv.finrank_eq
        ((transposeLinearEquiv (Fin n) (Fin n) K K).submoduleMap
          (Subalgebra.toSubmodule
            (Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K)))))]

/-- **Combined similarity + transpose invariance.**  For every unit `u : Mₙ(K)ˣ` and
    every matrix `M`, the transposed conjugate `(u M u⁻¹)ᵀ` has a commutant of the
    same dimension as `M`:

      `dim_K C((u M u⁻¹)ᵀ) = dim_K C(M)`.

    Both `M ↦ u M u⁻¹` and `M ↦ Mᵀ` preserve the commutant dimension, so their
    composite does too. -/
theorem finrank_centralizer_conj_transpose (u : (Matrix (Fin n) (Fin n) K)ˣ)
    (M : Matrix (Fin n) (Fin n) K) :
    Module.finrank K
        ↥(Subalgebra.centralizer K
          ({(u.val * M * (u⁻¹).val)ᵀ} : Set (Matrix (Fin n) (Fin n) K)))
      = Module.finrank K
          ↥(Subalgebra.centralizer K ({M} : Set (Matrix (Fin n) (Fin n) K))) := by
  rw [finrank_centralizer_transpose, finrank_centralizer_conj]

end CyclicCommutantSymmetry

end
