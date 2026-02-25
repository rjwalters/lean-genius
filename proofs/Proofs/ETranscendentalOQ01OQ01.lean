import Mathlib
import Proofs.ETranscendentalOQ01

/-!
# e + π Transcendence: New Results via Nesterenko's Theorem (OQ-01-OQ-01)

## Overview

This file extends `ETranscendentalOQ01.lean` with new proved transcendence results
derived from Nesterenko's 1996 algebraic independence theorem.

**Key new results** (all 0 sorries):
1. `pi_transcendental_from_nesterenko`: π is transcendental (from Nesterenko, not Lindemann)
2. `exp_pi_transcendental`: **e^π is transcendental** (first formal proof in this codebase)
3. `gamma_quarter_transcendental`: Γ(1/4) is transcendental
4. `pi_times_exp_pi_transcendental`: π · e^π is transcendental
5. `exp_pi_irrational`: e^π is irrational
6. `e_plus_pi_transcendental_via_schanuel`: e+π transcendental (conditional on Schanuel)

## Mathematical Background

**Nesterenko's Theorem (1996)**: π, e^π, and Γ(1/4) are algebraically independent over ℚ.

**Proof technique**: If φ(π, e^π, Γ(1/4)) = 0 for some nonzero multivariate polynomial φ,
we derive a contradiction. Conversely, for ANY expression built from the three constants,
transcendence follows by lifting a univariate polynomial f to a multivariate one.

## Connection to the Open Question (OQ-01)

The open question `e + π transcendental` remains unsolved (as of 2026), but:
- e^π IS transcendental (proved here from Nesterenko)
- At least one of {e+π, e·π} is transcendental (from Vieta + Hermite, in parent file)
- Under Schanuel's Conjecture: e+π IS transcendental (proved conditionally here)
-/

open Real

-- ============================================================
-- PART 1: π is Transcendental (from Nesterenko, not Lindemann)
-- ============================================================

/-
  **Historical Note**: Lindemann proved π transcendental in 1882. Nesterenko in 1996
  proved the much stronger result that {π, e^π, Γ(1/4)} are algebraically independent.
  Nesterenko's theorem implies π transcendence — a 1996 proof of an 1882 result!

  **Proof pattern**: If f(π) = 0 for some nonzero f ∈ ℚ[T], define
    P(X₀, X₁, X₂) = f(X₀) ∈ MvPolynomial (Fin 3) ℚ.
  Then P ≠ 0 and P(π, e^π, Γ(1/4)) = f(π) = 0, contradicting Nesterenko.
-/

/-- π is transcendental over ℚ — derived from Nesterenko's algebraic independence theorem.

    This gives an alternative proof of Lindemann (1882) via the stronger Nesterenko (1996)
    result: {π, e^π, Γ(1/4)} algebraically independent implies π transcendental. -/
theorem pi_transcendental_from_nesterenko : Transcendental ℚ Real.pi := by
  intro h_alg
  obtain ⟨f, hf_ne, hf_root⟩ := h_alg
  let x₀ : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 0
  let P : MvPolynomial (Fin 3) ℚ := Polynomial.aeval x₀ f
  have hP_ne : P ≠ 0 := by
    intro hP_eq
    apply hf_ne
    have hψP_zero : MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0, 0]) P = 0 := by
      rw [hP_eq]; exact map_zero _
    have hψP_eq_f :
        MvPolynomial.aeval (![Polynomial.X (R := ℚ), (0 : Polynomial ℚ), 0]) P = f := by
      show MvPolynomial.aeval (![Polynomial.X (R := ℚ), (0 : Polynomial ℚ), 0])
          (Polynomial.aeval x₀ f) = f
      rw [← Polynomial.aeval_algHom_apply]
      have hx₀ : MvPolynomial.aeval
          (![Polynomial.X (R := ℚ), (0 : Polynomial ℚ), 0]) x₀ = Polynomial.X := by
        simp [x₀, MvPolynomial.aeval_X, Matrix.cons_val_zero]
      rw [hx₀]; exact Polynomial.aeval_X_left_apply f
    exact hψP_eq_f.symm.trans hψP_zero
  have hP_eval :
      MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) P = 0 := by
    show MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter])
        (Polynomial.aeval x₀ f) = 0
    rw [← Polynomial.aeval_algHom_apply]
    have hx₀ : MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) x₀ =
        Real.pi := by
      simp [x₀, MvPolynomial.aeval_X, Matrix.cons_val_zero]
    rw [hx₀]; exact hf_root
  exact hP_ne (nesterenko_algebraic_independence P hP_eval)

-- ============================================================
-- PART 2: e^π is Transcendental (from Nesterenko)
-- ============================================================

/-
  **Theorem**: e^π is transcendental over ℚ.

  **History**: Gel'fond (1929) proved this via the theory of linear forms in logarithms
  (also follows from Gel'fond-Schneider: e^π = (-1)^{-i} with algebraic base and
  algebraic irrational exponent).

  **Our proof**: From Nesterenko's algebraic independence of {π, e^π, Γ(1/4)}.
  If f(e^π) = 0 for nonzero f ∈ ℚ[T], define P(X₀, X₁, X₂) = f(X₁).
  Then P ≠ 0 and P(π, e^π, Γ(1/4)) = f(e^π) = 0, contradiction.
-/

/-- **e^π is transcendental** over ℚ, derived from Nesterenko's algebraic independence theorem.

    **Proof**: Polynomial-lifting. f(e^π) = 0 → define P(X₀,X₁,X₂) = f(X₁).
    P ≠ 0 (specialize X₁↦T, X₀,X₂↦0 to recover f).
    P(π, e^π, Γ(1/4)) = f(e^π) = 0. Contradiction with Nesterenko. □ -/
theorem exp_pi_transcendental : Transcendental ℚ (Real.exp Real.pi) := by
  intro h_alg
  obtain ⟨f, hf_ne, hf_root⟩ := h_alg
  let x₁ : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 1
  let P : MvPolynomial (Fin 3) ℚ := Polynomial.aeval x₁ f
  have hP_ne : P ≠ 0 := by
    intro hP_eq
    apply hf_ne
    have hψP_zero : MvPolynomial.aeval (![0, Polynomial.X (R := ℚ), 0]) P = 0 := by
      rw [hP_eq]; exact map_zero _
    have hψP_eq_f :
        MvPolynomial.aeval (![0, Polynomial.X (R := ℚ), (0 : Polynomial ℚ)]) P = f := by
      show MvPolynomial.aeval (![0, Polynomial.X (R := ℚ), (0 : Polynomial ℚ)])
          (Polynomial.aeval x₁ f) = f
      rw [← Polynomial.aeval_algHom_apply]
      have hx₁ : MvPolynomial.aeval
          (![0, Polynomial.X (R := ℚ), (0 : Polynomial ℚ)]) x₁ = Polynomial.X := by
        simp [x₁, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hx₁]; exact Polynomial.aeval_X_left_apply f
    exact hψP_eq_f.symm.trans hψP_zero
  have hP_eval :
      MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) P = 0 := by
    show MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter])
        (Polynomial.aeval x₁ f) = 0
    rw [← Polynomial.aeval_algHom_apply]
    have hx₁ : MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) x₁ =
        Real.exp Real.pi := by
      simp [x₁, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hx₁]; exact hf_root
  exact hP_ne (nesterenko_algebraic_independence P hP_eval)

-- ============================================================
-- PART 3: Γ(1/4) is Transcendental (from Nesterenko)
-- ============================================================

/-- **Γ(1/4) is transcendental** over ℚ, derived from Nesterenko's theorem.

    Numerical value: Γ(1/4) ≈ 3.6256099082...

    Proof: P(X₀,X₁,X₂) = f(X₂); specialize X₂↦T, X₀,X₁↦0 to show P ≠ 0;
    P(π, e^π, Γ(1/4)) = f(Γ(1/4)) = 0 contradicts Nesterenko. -/
theorem gamma_quarter_transcendental : Transcendental ℚ gammaQuarter := by
  intro h_alg
  obtain ⟨f, hf_ne, hf_root⟩ := h_alg
  let x₂ : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 2
  let P : MvPolynomial (Fin 3) ℚ := Polynomial.aeval x₂ f
  have hP_ne : P ≠ 0 := by
    intro hP_eq
    apply hf_ne
    have hψP_zero : MvPolynomial.aeval (![0, 0, Polynomial.X (R := ℚ)]) P = 0 := by
      rw [hP_eq]; exact map_zero _
    have hψP_eq_f :
        MvPolynomial.aeval (![0, (0 : Polynomial ℚ), Polynomial.X (R := ℚ)]) P = f := by
      show MvPolynomial.aeval (![0, (0 : Polynomial ℚ), Polynomial.X (R := ℚ)])
          (Polynomial.aeval x₂ f) = f
      rw [← Polynomial.aeval_algHom_apply]
      have hx₂ : MvPolynomial.aeval
          (![0, (0 : Polynomial ℚ), Polynomial.X (R := ℚ)]) x₂ = Polynomial.X := by
        simp [x₂, MvPolynomial.aeval_X]
      rw [hx₂]; exact Polynomial.aeval_X_left_apply f
    exact hψP_eq_f.symm.trans hψP_zero
  have hP_eval :
      MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) P = 0 := by
    show MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter])
        (Polynomial.aeval x₂ f) = 0
    rw [← Polynomial.aeval_algHom_apply]
    have hx₂ : MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) x₂ =
        gammaQuarter := by
      simp [x₂, MvPolynomial.aeval_X]
    rw [hx₂]; exact hf_root
  exact hP_ne (nesterenko_algebraic_independence P hP_eval)

-- ============================================================
-- PART 4: π · e^π is Transcendental (from Nesterenko)
-- ============================================================

/-- **π · e^π is transcendental** over ℚ, derived from Nesterenko's theorem.

    Proof: f(π · e^π) = 0 → P(X₀,X₁,X₂) = f(X₀ · X₁) is nonzero
    (specialization X₀↦T, X₁↦1 recovers f), but P(π, e^π, Γ(1/4)) = 0. -/
theorem pi_times_exp_pi_transcendental :
    Transcendental ℚ (Real.pi * Real.exp Real.pi) := by
  intro h_alg
  obtain ⟨f, hf_ne, hf_root⟩ := h_alg
  let x₀₁ : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 0 * MvPolynomial.X 1
  let P : MvPolynomial (Fin 3) ℚ := Polynomial.aeval x₀₁ f
  have hP_ne : P ≠ 0 := by
    intro hP_eq
    apply hf_ne
    have hψP_zero : MvPolynomial.aeval (![Polynomial.X (R := ℚ), 1, 0]) P = 0 := by
      rw [hP_eq]; exact map_zero _
    have hψP_eq_f :
        MvPolynomial.aeval (![Polynomial.X (R := ℚ), (1 : Polynomial ℚ), 0]) P = f := by
      show MvPolynomial.aeval (![Polynomial.X (R := ℚ), (1 : Polynomial ℚ), 0])
          (Polynomial.aeval x₀₁ f) = f
      rw [← Polynomial.aeval_algHom_apply]
      have hx₀₁ : MvPolynomial.aeval
          (![Polynomial.X (R := ℚ), (1 : Polynomial ℚ), 0]) x₀₁ = Polynomial.X := by
        simp only [x₀₁, map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero,
                   Matrix.cons_val_one]
        ring
      rw [hx₀₁]; exact Polynomial.aeval_X_left_apply f
    exact hψP_eq_f.symm.trans hψP_zero
  have hP_eval :
      MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) P = 0 := by
    show MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter])
        (Polynomial.aeval x₀₁ f) = 0
    rw [← Polynomial.aeval_algHom_apply]
    have hx₀₁ : MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) x₀₁ =
        Real.pi * Real.exp Real.pi := by
      simp only [x₀₁, map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero,
                 Matrix.cons_val_one]
    rw [hx₀₁]; exact hf_root
  exact hP_ne (nesterenko_algebraic_independence P hP_eval)

-- ============================================================
-- PART 5: Irrationality Corollary for e^π
-- ============================================================

/-- e^π is irrational. Follows immediately from its transcendence. -/
theorem exp_pi_irrational : Irrational (Real.exp Real.pi) := by
  intro ⟨r, hr⟩
  exact exp_pi_transcendental
    ⟨Polynomial.X - Polynomial.C r, (Polynomial.monic_X_sub_C r).ne_zero, by
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
      have : (algebraMap ℚ ℝ) r = (r : ℝ) := rfl
      linarith [hr.symm]⟩

-- ============================================================
-- PART 6: Schanuel's Conjecture → e + π Transcendental
-- ============================================================

/-!
## Schanuel's Conjecture and e + π

The open question is whether e + π is transcendental. Schanuel's Conjecture provides
the strongest conditional resolution.

  **Schanuel's Conjecture**: If z₁,...,zₙ ∈ ℂ are ℚ-linearly independent, then
  tr.deg_ℚ(z₁,...,zₙ, e^z₁,...,e^zₙ) ≥ n.

  **Application**: Take z₁=1, z₂=iπ (ℚ-lin independent since π is irrational).
  Then tr.deg_ℚ(1, iπ, e^1, e^{iπ}) = tr.deg_ℚ(π, e) ≥ 2.
  So e and π are algebraically independent — hence e+π is transcendental.

We state the key consequence as a named axiom `schanuel_for_e_pi` to explicitly
track the conditional dependency.
-/

/-- **Schanuel's Conjecture for e and π** (stated as named axiom):
    e and π are algebraically independent over ℚ.

    This follows from Schanuel's Conjecture applied with z₁=1, z₂=iπ.
    The full conjecture is one of the central open problems in transcendental number theory.

    Note: Definitionally this is `e_pi_algebraicallyIndependent` from the parent file,
    but named to explicitly track Schanuel's dependency. -/
axiom schanuel_for_e_pi :
    ∀ (p : MvPolynomial (Fin 2) ℚ),
      MvPolynomial.aeval (![Real.exp 1, Real.pi]) p = 0 → p = 0

/-- **e + π is transcendental** — conditionally on Schanuel's Conjecture.

    Chain: `schanuel_for_e_pi` → `e_pi_algebraicallyIndependent`
           → `e_plus_pi_transcendental_from_independence` → e+π transcendental.

    **Proof status**: Proved (0 sorries), conditional on `schanuel_for_e_pi` (unproved). -/
theorem e_plus_pi_transcendental_via_schanuel :
    Transcendental ℚ (Real.exp 1 + Real.pi) :=
  e_plus_pi_transcendental_from_independence schanuel_for_e_pi

/-- **e · π is transcendental** — conditionally on Schanuel's Conjecture. -/
theorem e_times_pi_transcendental_via_schanuel :
    Transcendental ℚ (Real.exp 1 * Real.pi) :=
  e_times_pi_transcendental_from_independence schanuel_for_e_pi

/-- **e + π is irrational** — conditionally on Schanuel's Conjecture.

    Note: Even unconditional irrationality of e+π is open as of 2026! -/
theorem e_plus_pi_irrational_via_schanuel :
    Irrational (Real.exp 1 + Real.pi) :=
  e_plus_pi_irrational_from_independence schanuel_for_e_pi

-- ============================================================
-- PART 7: Summary — The Transcendence Hierarchy
-- ============================================================

/-!
## Complete Transcendence Picture (as of 2026)

**Proved unconditionally**:
  ✓ e is transcendental (Hermite 1873) — `e_transcendental_q` (axiom in parent)
  ✓ π is transcendental (Lindemann 1882) — `pi_transcendental_q` (axiom in parent)
  ✓ π is transcendental (Nesterenko 1996) — `pi_transcendental_from_nesterenko` ← NEW
  ✓ **e^π is transcendental** (Gel'fond 1929) — `exp_pi_transcendental` ← NEW
  ✓ Γ(1/4) is transcendental (Nesterenko 1996) — `gamma_quarter_transcendental` ← NEW
  ✓ π · e^π is transcendental — `pi_times_exp_pi_transcendental` ← NEW
  ✓ π + e^π is transcendental (Nesterenko 1996) — `pi_plus_exp_pi_transcendental` (parent)
  ✓ At least one of {e+π, e·π} is transcendental — `e_plus_pi_or_e_times_pi_transcendental` (parent)

**Proved conditionally on Schanuel's Conjecture**:
  ✓ e + π is transcendental — `e_plus_pi_transcendental_via_schanuel` ← NEW
  ✓ e · π is transcendental — `e_times_pi_transcendental_via_schanuel` ← NEW
  ✓ e + π is irrational — `e_plus_pi_irrational_via_schanuel` ← NEW

**Open (unknown as of 2026)**:
  ? Are e and π algebraically independent? (Open — Schanuel would give this)
  ? Is e + π irrational? (Open even unconditionally!)
  ? Is e + π transcendental? (The main OQ-01)
  ? Is e · π transcendental?
  ? Is e^e transcendental?
-/

/-- Five new transcendence results from Nesterenko's theorem in a single statement. -/
theorem nesterenko_gives_five_transcendence_results :
    Transcendental ℚ Real.pi ∧
    Transcendental ℚ (Real.exp Real.pi) ∧
    Transcendental ℚ gammaQuarter ∧
    Transcendental ℚ (Real.pi * Real.exp Real.pi) ∧
    Transcendental ℚ (Real.pi + Real.exp Real.pi) :=
  ⟨pi_transcendental_from_nesterenko,
   exp_pi_transcendental,
   gamma_quarter_transcendental,
   pi_times_exp_pi_transcendental,
   pi_plus_exp_pi_transcendental⟩

-- Verify key results compile:
#check @pi_transcendental_from_nesterenko
#check @exp_pi_transcendental
#check @gamma_quarter_transcendental
#check @pi_times_exp_pi_transcendental
#check @exp_pi_irrational
#check @e_plus_pi_transcendental_via_schanuel
#check @nesterenko_gives_five_transcendence_results
