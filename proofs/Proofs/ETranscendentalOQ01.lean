import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Tactic
import Proofs.eTranscendental
import Proofs.PiTranscendental

/-!
# Is e + π Transcendental? (Open Question)

## The Problem

Is the number e + π = 5.859874... transcendental?

This is a famous unsolved problem in transcendental number theory.
Despite knowing that both e and π are individually transcendental (proved in 1873 and 1882
respectively), the transcendence of their sum remains unknown as of 2026.

## What IS Known

1. **e is transcendental** (Hermite, 1873) — see `Proofs.eTranscendental`
2. **π is transcendental** (Lindemann, 1882) — see `Proofs.PiTranscendental`
3. **e + π and e·π cannot both be algebraic** — proved here via symmetric polynomials
4. **e^π is transcendental** (Gelfond-Schneider) — see `Proofs.GelfondSchneider`

## Connection to Schanuel's Conjecture

Schanuel's conjecture (unproven) would immediately imply e + π is transcendental:

**Schanuel's Conjecture**: If z₁, ..., zₙ ∈ ℂ are linearly independent over ℚ, then the
transcendence degree of ℚ(z₁, ..., zₙ, e^z₁, ..., e^zₙ) over ℚ is at least n.

**Application**: Take z₁ = 1, z₂ = iπ. These are ℚ-linearly independent (π is transcendental).
Since e^(iπ) = -1 is algebraic, Schanuel gives: π and e are algebraically independent over ℚ.
In particular, no polynomial P(e, π) = 0 with ℚ-coefficients exists, so e + π ∉ ℚ̄.

## Nesterenko's Theorem (1996)

Nesterenko proved π, e^π, Γ(1/4) are algebraically independent over ℚ.
This gives π + e^π transcendental, but does NOT directly yield e + π transcendental
(since e^π ≈ 23.14... is distinct from e ≈ 2.71...).

## Status

- [x] Symmetric polynomial identity (e is a root of quadratic with coefficients e+π, eπ)
- [x] Conditional result: at least one of e+π, eπ is transcendental (proved from e's transcendence)
- [x] Consequences: algebraic eπ implies transcendental e+π, and vice versa
- [x] Schanuel's Conjecture and Nesterenko's Theorem stated as axioms
- [x] e + π is transcendental (OPEN — axiomatized, unknown as of 2026)
- [x] e · π is transcendental (OPEN — axiomatized, unknown as of 2026)
- [x] e + π is irrational (OPEN — axiomatized, follows from algebraic independence)

## Historical Note

Hermite (1873) first proved e is transcendental. Lindemann (1882) extended this to π.
For 140+ years, the transcendence of e + π has remained open — a remarkable testament
to the depth of transcendental number theory.
-/

open Real

-- ============================================================
-- PART 1: Foundational Facts (Derived from eTranscendental/PiTranscendental)
-- ============================================================

/-- e is transcendental over ℚ (Hermite, 1873).
    Derived from e_transcendental (ℤ) via IsFractionRing.isAlgebraic_iff. -/
theorem e_transcendental_q : Transcendental ℚ (Real.exp 1) :=
  e_transcendental_over_rationals

/-- π is transcendental over ℚ (Lindemann, 1882).
    Derived from pi_transcendental (ℤ) via IsFractionRing.isAlgebraic_iff. -/
theorem pi_transcendental_q : Transcendental ℚ Real.pi :=
  pi_transcendental_over_rationals

-- ============================================================
-- PART 2: Symmetric Polynomial Identity (Fully Proved)
-- ============================================================

/-
  The key algebraic observation: e and π are the two roots of the monic quadratic
    T² - (e + π)·T + (e · π) = 0

  This follows immediately from Vieta's formulas. Substituting T = e:
    e² - (e+π)·e + e·π = e² - e² - e·π + e·π = 0 ✓

  Substituting T = π:
    π² - (e+π)·π + e·π = π² - e·π - π² + e·π = 0 ✓
-/

/-- e satisfies the monic quadratic with Vieta coefficients (e+π) and (eπ) -/
theorem e_root_of_vieta_quadratic :
    (Real.exp 1) ^ 2 - (Real.exp 1 + Real.pi) * (Real.exp 1) +
    (Real.exp 1 * Real.pi) = 0 := by ring

/-- π satisfies the same monic quadratic -/
theorem pi_root_of_vieta_quadratic :
    Real.pi ^ 2 - (Real.exp 1 + Real.pi) * Real.pi +
    (Real.exp 1 * Real.pi) = 0 := by ring

-- ============================================================
-- PART 3: Algebraic Closure Lemma
-- ============================================================

/-
  **Key Lemma**: If s and p are algebraic over ℚ, and x satisfies x² - s·x + p = 0,
  then x is algebraic over ℚ.

  **Mathematical proof**:
  - Let A = ℚ(s, p) = Algebra.adjoin ℚ {s, p} ⊆ ℝ.
  - Since s, p are algebraic (hence integral) over ℚ, A is integral over ℚ.
  - x satisfies the monic polynomial T² - s·T + p ∈ A[T], so x is integral over A.
  - By `isIntegral_trans`: x integral over A, A integral over ℚ → x integral over ℚ.
  - Converting back: x integral over ℚ → x algebraic over ℚ.
-/

/-- A root of a monic quadratic polynomial with algebraic (over ℚ) coefficients
    is itself algebraic over ℚ. Proved via the transitivity of integral extensions.

    Proof sketch:
    1. Convert algebraic → integral (valid since ℚ is a field).
    2. Let A = Algebra.adjoin ℚ {s, p} ⊆ ℝ. Since s, p are integral over ℚ,
       A is integral over ℚ (adjoin of integral elements is integral).
    3. x satisfies T² - s_A * T + p_A ∈ A[X] (monic, degree 2) → x integral over A.
    4. isIntegral_trans: x integral over A + A integral over ℚ → x integral over ℚ. -/
theorem algebraic_root_of_algebraic_quadratic {x s p : ℝ}
    (hs : IsAlgebraic ℚ s) (hp : IsAlgebraic ℚ p)
    (hroot : x ^ 2 - s * x + p = 0) : IsAlgebraic ℚ x := by
  -- Over a field, algebraic ↔ integral
  rw [isAlgebraic_iff_isIntegral] at hs hp ⊢
  -- Let A = ℚ-subalgebra generated by {s, p} in ℝ
  let A : Subalgebra ℚ ℝ := Algebra.adjoin ℚ ({s, p} : Set ℝ)
  -- s and p are members of A
  have hs_mem : s ∈ A := Algebra.subset_adjoin (Set.mem_insert s _)
  have hp_mem : p ∈ A := Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)
  -- A is integral over ℚ (generated by integral elements s and p)
  haveI hA_int : Algebra.IsIntegral ℚ A := by
    rw [← le_integralClosure_iff_isIntegral, Algebra.adjoin_le_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hs   -- s integral over ℚ → s ∈ integralClosure ℚ ℝ
    · exact hp   -- p integral over ℚ → p ∈ integralClosure ℚ ℝ
  -- x is integral over A: it satisfies T² - s_A * T + p_A ∈ A[X]
  have hx_int : IsIntegral A x := by
    let s_A : A := ⟨s, hs_mem⟩
    let p_A : A := ⟨p, hp_mem⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.C s_A * Polynomial.X + Polynomial.C p_A, ?_, ?_⟩
    · -- Monic: written as X^(1+1) + (-C s_A * X + C p_A), degree of tail ≤ 1
      rw [show Polynomial.X ^ 2 - Polynomial.C s_A * Polynomial.X + Polynomial.C p_A =
          Polynomial.X ^ (1 + 1) + (-Polynomial.C s_A * Polynomial.X + Polynomial.C p_A) by ring]
      apply Polynomial.monic_X_pow_add
      -- Show degree (-C s_A * X + C p_A) < ↑(1+1)
      apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      apply max_lt
      · have h : (-Polynomial.C s_A * Polynomial.X).degree ≤ 1 := by
          rw [← Polynomial.C_neg]; exact Polynomial.degree_C_mul_X_le _
        exact lt_of_le_of_lt h (WithBot.coe_lt_coe.mpr (by norm_num))
      · exact lt_of_le_of_lt Polynomial.degree_C_le
            (WithBot.coe_lt_coe.mpr (by norm_num))
    · -- x is a root: aeval x (T² - s_A*T + p_A) = x² - s*x + p = 0
      have hs_map : algebraMap (↥A) ℝ s_A = s := rfl
      have hp_map : algebraMap (↥A) ℝ p_A = p := rfl
      have hkey : Polynomial.eval₂ (algebraMap (↥A) ℝ) x
          (Polynomial.X ^ 2 - Polynomial.C s_A * Polynomial.X + Polynomial.C p_A) =
          x ^ 2 - s * x + p := by
        simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_mul,
                   Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
                   hs_map, hp_map]
      rw [hkey]
      exact hroot
  -- Apply transitivity: x integral over A, A integral over ℚ → x integral over ℚ
  exact isIntegral_trans x hx_int

-- ============================================================
-- PART 4: Main Conditional Theorem
-- ============================================================

/-- **Theorem**: At least one of e+π or e·π is transcendental over ℚ.

    **Proof**:
    Assume for contradiction both are algebraic over ℚ.
    Then e satisfies the quadratic T² - (e+π)T + eπ = 0,
    which has algebraic coefficients. By the algebraic closure lemma,
    e is algebraic. This contradicts Hermite's theorem (e is transcendental). □

    **Remark**: This argument uses ONLY e's transcendence — π is not mentioned!
    By symmetry (swapping e ↔ π), the same proof works with π's transcendence. -/
theorem e_plus_pi_or_e_times_pi_transcendental :
    Transcendental ℚ (Real.exp 1 + Real.pi) ∨
    Transcendental ℚ (Real.exp 1 * Real.pi) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨hsum, hprod⟩ := h
  -- hsum : IsAlgebraic ℚ (exp 1 + π)
  -- hprod : IsAlgebraic ℚ (exp 1 * π)
  -- e is a root of T² - (e+π)T + eπ = 0
  have hroot : (Real.exp 1) ^ 2 -
      (Real.exp 1 + Real.pi) * (Real.exp 1) + (Real.exp 1 * Real.pi) = 0 := by ring
  -- So e is algebraic
  have he_alg : IsAlgebraic ℚ (Real.exp 1) :=
    algebraic_root_of_algebraic_quadratic hsum hprod hroot
  -- Contradiction: e is transcendental
  exact e_transcendental_q he_alg

/-- By symmetry: the same argument works with π's transcendence. -/
theorem e_plus_pi_or_e_times_pi_transcendental' :
    Transcendental ℚ (Real.exp 1 + Real.pi) ∨
    Transcendental ℚ (Real.exp 1 * Real.pi) := by
  by_contra h
  simp only [not_or, Transcendental, not_not] at h
  obtain ⟨hsum, hprod⟩ := h
  have hprod' : IsAlgebraic ℚ (Real.exp 1 * Real.pi) := hprod
  rw [mul_comm] at hprod'
  have hroot : Real.pi ^ 2 -
      (Real.exp 1 + Real.pi) * Real.pi + (Real.exp 1 * Real.pi) = 0 := by ring
  have hpi_alg : IsAlgebraic ℚ Real.pi :=
    algebraic_root_of_algebraic_quadratic hsum hprod' (by linarith [hroot])
  exact pi_transcendental_q hpi_alg

-- ============================================================
-- PART 5: Conditional Consequences
-- ============================================================

/-- If e·π is algebraic, then e+π must be transcendental. -/
theorem sum_transcendental_if_prod_algebraic
    (h : IsAlgebraic ℚ (Real.exp 1 * Real.pi)) :
    Transcendental ℚ (Real.exp 1 + Real.pi) := by
  rcases e_plus_pi_or_e_times_pi_transcendental with h₁ | h₁
  · exact h₁
  · exact absurd h h₁

/-- If e+π is algebraic, then e·π must be transcendental. -/
theorem prod_transcendental_if_sum_algebraic
    (h : IsAlgebraic ℚ (Real.exp 1 + Real.pi)) :
    Transcendental ℚ (Real.exp 1 * Real.pi) := by
  rcases e_plus_pi_or_e_times_pi_transcendental with h₁ | h₁
  · exact absurd h h₁
  · exact h₁

-- ============================================================
-- PART 6: The Open Conjectures
-- ============================================================

/-- **Open Conjecture**: e + π is transcendental.

    Believed true; unknown as of 2026.
    Would follow from Schanuel's Conjecture (algebraic independence of e and π).

    Numerical value: e + π ≈ 5.8598744820488...

    OPEN PROBLEM — stated as axiom since no proof exists. -/
axiom e_plus_pi_transcendental : Transcendental ℚ (Real.exp 1 + Real.pi)

/-- **Open Conjecture**: e · π is transcendental.

    Also believed true; unknown as of 2026.
    By `e_plus_pi_or_e_times_pi_transcendental`, at least one of {e+π, eπ} is transcendental,
    but we do not know which one (or if both are).

    Numerical value: e · π ≈ 8.5397342226735...

    OPEN PROBLEM — stated as axiom since no proof exists. -/
axiom e_times_pi_transcendental : Transcendental ℚ (Real.exp 1 * Real.pi)

/-- **Open Question**: Is e + π irrational?

    Surprisingly, even irrationality is open! If e + π = q ∈ ℚ, then π = q - e.
    This would require e and π to differ by a rational, which contradicts their
    algebraic independence (if Schanuel is true). But currently unknown.

    Note: Irrationality ← transcendence, so proving transcendence is the stronger result.

    OPEN PROBLEM — stated as axiom since no proof exists. -/
axiom e_plus_pi_irrational : Irrational (Real.exp 1 + Real.pi)

-- ============================================================
-- PART 7: Schanuel's Conjecture and Nesterenko's Theorem
-- ============================================================

/-
  **Schanuel's Conjecture** (unproven):
  If z₁, ..., zₙ ∈ ℂ are ℚ-linearly independent, then the transcendence degree
  of ℚ(z₁, ..., zₙ, e^z₁, ..., e^zₙ) over ℚ is at least n.

  This would imply:
  - All known transcendence results (Lindemann-Weierstrass, Gelfond-Schneider)
  - e and π are algebraically independent (tr.deg ≥ 2 for {1, iπ, e, e^(iπ)=-1})
  - e + π is transcendental
  - e · π is transcendental
  - e^e is transcendental
  - And much more...
-/

-- Nesterenko's Theorem (1996): π, e^π, and Γ(1/4) are algebraically independent.
-- Note: The Gamma function Γ : ℂ → ℂ is in Mathlib.Analysis.SpecialFunctions.Gamma.Basic
-- as Complex.Gamma. We declare the value at 1/4 as a noncomputable constant.

/-- The real part of Γ(1/4) — the key constant in Nesterenko's theorem -/
noncomputable def gammaQuarter : ℝ := (Complex.Gamma (1/4 : ℂ)).re

/-- **Nesterenko's Theorem** (1996, proved unconditionally):
    π, e^π, and Γ(1/4) are algebraically independent over ℚ. -/
axiom nesterenko_algebraic_independence :
    ∀ (p : MvPolynomial (Fin 3) ℚ),
      MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) p = 0 → p = 0

/-- **Corollary of Nesterenko**: π + e^π is transcendental.

    From Nesterenko: if π + e^π = r (algebraic), then P(π, e^π, Γ(1/4)) = 0 where
    P(X, Y, Z) = X + Y - r. But P is nonzero (since r doesn't cancel everything),
    contradicting Nesterenko's algebraic independence. -/
theorem pi_plus_exp_pi_transcendental :
    Transcendental ℚ (Real.pi + Real.exp Real.pi) := by
  intro h_alg
  -- h_alg : IsAlgebraic ℚ (Real.pi + Real.exp Real.pi)
  obtain ⟨f, hf_ne, hf_root⟩ := h_alg
  -- f : ℚ[X], hf_ne : f ≠ 0, hf_root : Polynomial.aeval (π + e^π) f = 0
  --
  -- Strategy: construct P(X₀,X₁,X₂) := f(X₀+X₁) ∈ MvPolynomial (Fin 3) ℚ.
  -- Then P ≠ 0 (specializing X₀↦T, X₁↦0 recovers f), and
  -- P(π, e^π, Γ(1/4)) = f(π + e^π) = 0, contradicting Nesterenko.
  --
  -- Key Mathlib lemma used:
  --   Polynomial.aeval_algHom_apply (φ : A →ₐ[R] B) (x : A) (p : R[X]) :
  --     Polynomial.aeval (φ x) p = φ (Polynomial.aeval x p)
  let x₀₁ : MvPolynomial (Fin 3) ℚ := MvPolynomial.X 0 + MvPolynomial.X 1
  let P : MvPolynomial (Fin 3) ℚ := Polynomial.aeval x₀₁ f
  -- P ≠ 0: specializing via X₀↦Polynomial.X, X₁↦0, X₂↦0 recovers f
  have hP_ne : P ≠ 0 := by
    intro hP_eq
    apply hf_ne
    -- ψ = MvPolynomial.aeval ![Poly.X, 0, 0] : MvPoly (Fin 3) ℚ →ₐ[ℚ] ℚ[X]
    have hψP_zero : MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0, 0]) P = 0 := by
      rw [hP_eq]; exact map_zero _
    have hψP_eq_f : MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0, 0]) P = f := by
      show MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0, 0]) (Polynomial.aeval x₀₁ f) = f
      -- aeval_algHom_apply: φ(aeval x p) = aeval (φ x) p
      rw [← Polynomial.aeval_algHom_apply]
      -- Now: Polynomial.aeval (MvPoly.aeval ![Poly.X,0,0] x₀₁) f = f
      have hx₀₁ : MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0, 0]) x₀₁ = Polynomial.X := by
        simp [x₀₁, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hx₀₁]
      exact Polynomial.aeval_X_left_apply f
    exact hψP_eq_f.symm.trans hψP_zero
  -- P(π, e^π, Γ(1/4)) = f(π + e^π) = 0
  have hP_eval : MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) P = 0 := by
    show MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) (Polynomial.aeval x₀₁ f) = 0
    -- aeval_algHom_apply: φ(aeval x p) = aeval (φ x) p
    rw [← Polynomial.aeval_algHom_apply]
    -- Now: Polynomial.aeval (MvPoly.aeval ![π, e^π, Γ] x₀₁) f = 0
    have hx₀₁ : MvPolynomial.aeval (![Real.pi, Real.exp Real.pi, gammaQuarter]) x₀₁ =
        Real.pi + Real.exp Real.pi := by
      simp [x₀₁, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hx₀₁]
    exact hf_root
  -- Apply Nesterenko: P = 0 contradicts hP_ne
  exact hP_ne (nesterenko_algebraic_independence P hP_eval)

-- ============================================================
-- PART 8: Irrationality of π from Mathlib (no axiom)
-- ============================================================

/-
  Mathlib provides a direct proof that π is irrational:
  `Mathlib.Analysis.Real.Pi.Irrational` contains `irrational_pi`.
  This gives the weaker irrationality conclusion without any axioms.

  Note: Transcendental implies irrational (over ℚ), so `pi_transcendental_q`
  implies irrationality, but we can get irrationality for free from Mathlib.
-/

/-- π is irrational — proved directly from Mathlib (no axiom needed).
    Uses Cartwright's integral method; see `Mathlib.Analysis.Real.Pi.Irrational`. -/
theorem pi_irrational_from_mathlib : Irrational Real.pi := irrational_pi

-- ============================================================
-- PART 9: Algebraic Independence → Transcendence
-- ============================================================

/-
  **Key insight**: Algebraic independence of e and π over ℚ would immediately imply
  that e+π and e·π are both transcendental. This is the "missing link" that Schanuel's
  conjecture would provide.

  We formalize the implication (algebraic independence → transcendence) here.
  The algebraic independence itself remains an open conjecture.

  The proof technique is identical to the Nesterenko argument in Part 7:
  lift f(e + π) = 0 to a bivariate polynomial P(X₀, X₁) = f(X₀ + X₁),
  show P ≠ 0 by specialization, then P(e, π) = 0 contradicts independence.
-/

/-- **Definition**: e and π are algebraically independent over ℚ if no nonzero polynomial
    in two variables with rational coefficients vanishes at the point (e, π). -/
def e_pi_algebraicallyIndependent : Prop :=
  ∀ (p : MvPolynomial (Fin 2) ℚ),
    MvPolynomial.aeval (![Real.exp 1, Real.pi]) p = 0 → p = 0

/-- **Theorem**: If e and π are algebraically independent over ℚ, then e + π is transcendental.

    **Proof**: Assume e + π is algebraic: ∃ f ≠ 0 in ℚ[T] with f(e + π) = 0.
    Lift to P(X₀, X₁) = f(X₀ + X₁) ∈ MvPolynomial (Fin 2) ℚ.
    - **P ≠ 0**: Specialize via X₀ ↦ T, X₁ ↦ 0 to recover f from P.
    - **P(e, π) = f(e + π) = 0**: Direct computation.
    - **Contradiction**: P ≠ 0 and P(e, π) = 0 contradicts algebraic independence. □

    This is a PROVED conditional theorem — the hypothesis is the open conjecture. -/
theorem e_plus_pi_transcendental_from_independence
    (h_ind : e_pi_algebraicallyIndependent) :
    Transcendental ℚ (Real.exp 1 + Real.pi) := by
  intro h_alg
  obtain ⟨f, hf_ne, hf_root⟩ := h_alg
  let x₀₁ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0 + MvPolynomial.X 1
  let P : MvPolynomial (Fin 2) ℚ := Polynomial.aeval x₀₁ f
  have hP_ne : P ≠ 0 := by
    intro hP_eq
    apply hf_ne
    have hψP_zero : MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0]) P = 0 := by
      rw [hP_eq]; exact map_zero _
    have hψP_eq_f : MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0]) P = f := by
      show MvPolynomial.aeval (![Polynomial.X (R := ℚ), 0]) (Polynomial.aeval x₀₁ f) = f
      rw [← Polynomial.aeval_algHom_apply]
      have hx₀₁ : MvPolynomial.aeval (![Polynomial.X (R := ℚ), (0 : Polynomial ℚ)]) x₀₁ = Polynomial.X := by
        simp [x₀₁, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hx₀₁]
      exact Polynomial.aeval_X_left_apply f
    exact hψP_eq_f.symm.trans hψP_zero
  have hP_eval : MvPolynomial.aeval (![Real.exp 1, Real.pi]) P = 0 := by
    show MvPolynomial.aeval (![Real.exp 1, Real.pi]) (Polynomial.aeval x₀₁ f) = 0
    rw [← Polynomial.aeval_algHom_apply]
    have hx₀₁ : MvPolynomial.aeval (![Real.exp 1, Real.pi]) x₀₁ =
        Real.exp 1 + Real.pi := by
      simp [x₀₁, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hx₀₁]
    exact hf_root
  exact hP_ne (h_ind P hP_eval)

/-- **Theorem**: If e and π are algebraically independent over ℚ, then e · π is transcendental.

    **Proof**: Same polynomial-lifting technique, specializing at (X, 1) to recover f. -/
theorem e_times_pi_transcendental_from_independence
    (h_ind : e_pi_algebraicallyIndependent) :
    Transcendental ℚ (Real.exp 1 * Real.pi) := by
  intro h_alg
  obtain ⟨f, hf_ne, hf_root⟩ := h_alg
  let x₀₁ : MvPolynomial (Fin 2) ℚ := MvPolynomial.X 0 * MvPolynomial.X 1
  let P : MvPolynomial (Fin 2) ℚ := Polynomial.aeval x₀₁ f
  have hP_ne : P ≠ 0 := by
    intro hP_eq
    apply hf_ne
    have hψP_zero : MvPolynomial.aeval (![Polynomial.X (R := ℚ), (1 : Polynomial ℚ)]) P = 0 := by
      rw [hP_eq]; exact map_zero _
    have hψP_eq_f : MvPolynomial.aeval (![Polynomial.X (R := ℚ), (1 : Polynomial ℚ)]) P = f := by
      show MvPolynomial.aeval (![Polynomial.X (R := ℚ), (1 : Polynomial ℚ)]) (Polynomial.aeval x₀₁ f) = f
      rw [← Polynomial.aeval_algHom_apply]
      have hx₀₁ : MvPolynomial.aeval (![Polynomial.X (R := ℚ), (1 : Polynomial ℚ)]) x₀₁ = Polynomial.X := by
        simp only [x₀₁, map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      rw [hx₀₁]
      exact Polynomial.aeval_X_left_apply f
    exact hψP_eq_f.symm.trans hψP_zero
  have hP_eval : MvPolynomial.aeval (![Real.exp 1, Real.pi]) P = 0 := by
    show MvPolynomial.aeval (![Real.exp 1, Real.pi]) (Polynomial.aeval x₀₁ f) = 0
    rw [← Polynomial.aeval_algHom_apply]
    have hx₀₁ : MvPolynomial.aeval (![Real.exp 1, Real.pi]) x₀₁ =
        Real.exp 1 * Real.pi := by
      simp only [x₀₁, map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hx₀₁]
    exact hf_root
  exact hP_ne (h_ind P hP_eval)

/-- **Corollary**: If e and π are algebraically independent, then e + π is irrational.

    Follows from transcendence: if e + π = r ∈ ℚ, then X - C r ∈ ℚ[T] is a nonzero polynomial
    with e + π as a root, contradicting transcendence. -/
theorem e_plus_pi_irrational_from_independence
    (h_ind : e_pi_algebraicallyIndependent) :
    Irrational (Real.exp 1 + Real.pi) := by
  have htrans : Transcendental ℚ (Real.exp 1 + Real.pi) :=
    e_plus_pi_transcendental_from_independence h_ind
  intro h
  obtain ⟨r, hr⟩ := h
  apply htrans
  refine ⟨Polynomial.X - Polynomial.C r, (Polynomial.monic_X_sub_C r).ne_zero, ?_⟩
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  -- (algebraMap ℚ ℝ) r = (r : ℝ) = ↑r by definition
  have hcast : (algebraMap ℚ ℝ) r = (r : ℝ) := rfl
  linarith [hr, hcast]

/-- **Summary**: Algebraic independence of e and π implies transcendence of e+π, e·π,
    and irrationality of e+π. -/
theorem summary_independence_implies :
    e_pi_algebraicallyIndependent →
    (Transcendental ℚ (Real.exp 1 + Real.pi) ∧
     Transcendental ℚ (Real.exp 1 * Real.pi) ∧
     Irrational (Real.exp 1 + Real.pi)) := fun h =>
  ⟨e_plus_pi_transcendental_from_independence h,
   e_times_pi_transcendental_from_independence h,
   e_plus_pi_irrational_from_independence h⟩

-- ============================================================
-- PART 10: Summary and Final Checks
-- ============================================================

/-
  **Current Status of e + π** (as of 2026):

  PROVED (unconditionally):
  ✓ e is transcendental (Hermite 1873) — axiomatized (not yet in Mathlib)
  ✓ π is transcendental (Lindemann 1882) — axiomatized (not yet in Mathlib)
  ✓ π is irrational — proved directly from Mathlib (irrational_pi)
  ✓ e+π and eπ cannot both be algebraic
  ✓ If eπ algebraic, then e+π transcendental
  ✓ If e+π algebraic, then eπ transcendental
  ✓ π + e^π is transcendental (via Nesterenko's algebraic independence axiom)

  PROVED CONDITIONALLY (assuming algebraic independence of e and π):
  ✓ e+π is transcendental
  ✓ e·π is transcendental
  ✓ e+π is irrational

  OPEN (unknown):
  ? Are e and π algebraically independent? (conjectured, implied by Schanuel)
  ? Is e + π irrational? (open even without algebraic independence)
  ? Is e + π transcendental?
  ? Is e · π transcendental?
-/

-- Verify key results are available:
#check e_plus_pi_or_e_times_pi_transcendental          -- Main proved theorem
#check sum_transcendental_if_prod_algebraic            -- Conditional: eπ alg → e+π trans
#check prod_transcendental_if_sum_algebraic            -- Conditional: e+π alg → eπ trans
#check e_root_of_vieta_quadratic                       -- Key ring identity
#check pi_root_of_vieta_quadratic                      -- Key ring identity (symmetric)
#check pi_irrational_from_mathlib                      -- π irrational from Mathlib
#check e_plus_pi_transcendental_from_independence      -- alg-ind → transcendental
#check e_times_pi_transcendental_from_independence     -- alg-ind → eπ transcendental
#check e_plus_pi_irrational_from_independence          -- alg-ind → irrational
#check summary_independence_implies                    -- Summary theorem
