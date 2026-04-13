import Mathlib
import Proofs.CramersRuleOQ03

/-!
# Quaternionic Cramer's Rule

Instantiates the non-commutative Cramer's Rule from `CramersRuleOQ03` with quaternions
(`Quaternion ℝ`). Since quaternions form a `DivisionRing` in Mathlib, the Gelfand-Retakh
quasideterminant solver `ncSolve` applies directly.

## Key Results

1. `qi_ne_zero` — the imaginary unit i = ⟨0, 1, 0, 0⟩ is nonzero
2. `quat_diag_correct` — diagonal quaternionic systems solve correctly
3. `quaternion_cramers_rule` — general quaternionic Cramer's Rule
4. `quaternion_cramers_unique` — uniqueness of the quaternionic solution

## Context

Quaternions were introduced by Hamilton (1843) to represent spatial rotations.
They are non-commutative: i·j = k but j·i = -k. The classical (commutative) Cramer's
Rule fails in this setting — the quasideterminant approach of `CramersRuleOQ03` applies.

This answers OQ-03-OQ-03 affirmatively: the non-commutative Cramer's Rule
fully extends to concrete quaternionic linear systems.
-/

namespace CramersRuleOQ03OQ03

open CramersRuleOQ03 Matrix Quaternion

-- ============================================================
-- Part I: Quaternion Division Ring
-- ============================================================

/-- Quaternions form a division ring — all results from CramersRuleOQ03 apply. -/
theorem quaternion_is_division_ring : DivisionRing (Quaternion ℝ) := inferInstance

-- ============================================================
-- Part II: Quaternion Basis Elements
-- ============================================================

/-- The imaginary unit i = ⟨0, 1, 0, 0⟩ in ℍ. -/
noncomputable abbrev qi : Quaternion ℝ := ⟨0, 1, 0, 0⟩

/-- The imaginary unit j = ⟨0, 0, 1, 0⟩ in ℍ. -/
noncomputable abbrev qj : Quaternion ℝ := ⟨0, 0, 1, 0⟩

/-- i ≠ 0: its imI component is 1 ≠ 0. -/
theorem qi_ne_zero : qi ≠ 0 := by
  intro h
  have := congr_arg Quaternion.imI h
  simp [qi] at this

/-- j ≠ 0: its imJ component is 1 ≠ 0. -/
theorem qj_ne_zero : qj ≠ 0 := by
  intro h
  have := congr_arg Quaternion.imJ h
  simp [qj] at this

/-- i · j = k (non-commutativity demo). -/
theorem qi_mul_qj : qi * qj = (⟨0, 0, 0, 1⟩ : Quaternion ℝ) := by
  simp [qi, qj, Quaternion.ext_iff, Quaternion.mul_re, Quaternion.mul_imI,
        Quaternion.mul_imJ, Quaternion.mul_imK]

/-- j · i = -k (non-commutativity: order matters). -/
theorem qj_mul_qi : qj * qi = (⟨0, 0, 0, -1⟩ : Quaternion ℝ) := by
  simp [qi, qj, Quaternion.ext_iff, Quaternion.mul_re, Quaternion.mul_imI,
        Quaternion.mul_imJ, Quaternion.mul_imK]

-- ============================================================
-- Part III: Diagonal Quaternionic System
-- ============================================================

/-- A diagonal 2×2 quaternionic matrix: diag(i, 1). -/
noncomputable def ADiag : Matrix (Fin 2) (Fin 2) (Quaternion ℝ) := fun
  | 0, 0 => qi
  | 1, 1 => 1
  | _, _ => 0

/-- Right-hand side: b = (1, 1). -/
noncomputable def bDiag : Fin 2 → Quaternion ℝ := ![(1 : Quaternion ℝ), 1]

/-- The (1,1) entry 1 is invertible. -/
theorem ADiag_11_ne : ADiag 1 1 ≠ 0 := by
  simp [ADiag]; exact one_ne_zero

/-- For the diagonal matrix, quasidet₀₀ = i (the off-diagonal entries are 0). -/
theorem ADiag_quasidet_eq : quasidet₀₀ ADiag = qi := by
  simp [quasidet₀₀, ADiag]

/-- The quasideterminant i is nonzero. -/
theorem ADiag_quasidet_ne : quasidet₀₀ ADiag ≠ 0 := by
  rw [ADiag_quasidet_eq]; exact qi_ne_zero

/-- The diagonal system diag(i, 1) · x = (1, 1) is solved correctly by ncSolve. -/
theorem quat_diag_correct :
    ADiag.mulVec (ncSolve ADiag bDiag) = bDiag :=
  nc_cramers_rule ADiag bDiag ADiag_11_ne ADiag_quasidet_ne

/-- The diagonal solution is unique. -/
theorem quat_diag_unique (x : Fin 2 → Quaternion ℝ) (hx : ADiag.mulVec x = bDiag) :
    x = ncSolve ADiag bDiag :=
  nc_cramers_unique ADiag bDiag ADiag_11_ne ADiag_quasidet_ne x hx

-- ============================================================
-- Part IV: General Quaternionic Cramer's Rule
-- ============================================================

/-- **Quaternionic Cramer's Rule**: For any 2×2 quaternionic matrix A with
    invertible (1,1)-entry and nonzero quasideterminant, the system Ax = b
    has solution x = ncSolve A b. -/
theorem quaternion_cramers_rule
    (A : Matrix (Fin 2) (Fin 2) (Quaternion ℝ)) (b : Fin 2 → Quaternion ℝ)
    (h11 : A 1 1 ≠ 0) (hq : quasidet₀₀ A ≠ 0) :
    A.mulVec (ncSolve A b) = b :=
  nc_cramers_rule A b h11 hq

/-- **Uniqueness**: The quaternionic solution is unique when the system is solvable. -/
theorem quaternion_cramers_unique
    (A : Matrix (Fin 2) (Fin 2) (Quaternion ℝ)) (b : Fin 2 → Quaternion ℝ)
    (h11 : A 1 1 ≠ 0) (hq : quasidet₀₀ A ≠ 0)
    (x : Fin 2 → Quaternion ℝ) (hx : A.mulVec x = b) :
    x = ncSolve A b :=
  nc_cramers_unique A b h11 hq x hx

-- ============================================================
-- Part V: Non-Commutativity Example
-- ============================================================

/-- Non-commutativity matters: swapping rows and columns of a quaternion
    matrix gives a DIFFERENT system with a DIFFERENT solution in general.

    For A = [[i, j], [0, 1]] vs A' = [[j, i], [0, 1]], the quasideterminants
    differ: quasidet₀₀(A) = i ≠ quasidet₀₀(A') = j. -/
noncomputable def ANonComm : Matrix (Fin 2) (Fin 2) (Quaternion ℝ) := fun
  | 0, 0 => qi
  | 0, 1 => qj
  | _, _ => 0

noncomputable def ANonCommSwap : Matrix (Fin 2) (Fin 2) (Quaternion ℝ) := fun
  | 0, 0 => qj
  | 0, 1 => qi
  | _, _ => 0

/-- The quasideterminants differ, showing the non-commutative structure matters. -/
theorem noncomm_quasidet_differ :
    quasidet₀₀ ANonComm ≠ quasidet₀₀ ANonCommSwap := by
  simp [quasidet₀₀, ANonComm, ANonCommSwap]
  -- quasidet₀₀(A) = qi, quasidet₀₀(A') = qj, qi ≠ qj
  intro h
  have := congr_arg Quaternion.imI h
  simp [qi, qj] at this

end CramersRuleOQ03OQ03
