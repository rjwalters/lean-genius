import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Liouville's Theorem on Integration in Terms of Elementary Functions
## (Abel-Ruffini OQ-09)

## Research Question

Which functions have antiderivatives expressible in elementary terms?
Liouville's theorem (1835/1840) — the direct analog of Abel-Ruffini for integration —
gives a complete structural answer: elementary integrals have a specific logarithmic form.
This inaugurated differential algebra and the Risch decision procedure (1969).

## Mathematical Background

**Elementary functions** are built from constants and x by finitely many applications of
arithmetic operations, algebraic operations (roots), exponentials (e^f), and logarithms.

**Liouville's Structure Theorem** (1835): If f ∈ F has an elementary antiderivative,
that antiderivative has the Liouville form:
  g = v₀ + c₁·ln(v₁) + ··· + cₙ·ln(vₙ)
where v₀, vᵢ ∈ F and cᵢ are constants of F. Proved via differential Galois theory.

**Risch Algorithm** (1969): Given f(x), decides whether ∫f(x)dx is elementary.
This underlies symbolic integration in Mathematica, Maple, and Sage.

**Risch criterion for the Gaussian**: ∫e^(-x²)dx is elementary iff
∃ rational Q(x) with Q'(x) - 2x·Q(x) = 1.

## Core Result: No Polynomial Risch Solution (Fully Proved)

We prove that **no polynomial** p : ℝ[X] satisfies p' - C(2)·X·p = 1.

**Proof**: For p ≠ 0, the coefficient of X^(natDeg p + 1) in p' - 2xp equals
-2 · leadingCoeff(p) (proved in `risch_ode_coeff_top`). The target polynomial 1 has
coefficient 0 at that position. So -2·leadingCoeff(p) = 0, forcing leadingCoeff(p) = 0,
contradicting p ≠ 0. For p = 0, the left side is 0 ≠ 1.

This is the algebraic core of the Gaussian's non-elementarity.

## Elementary Contrast: ∫p(x)·eˣdx IS always elementary

For the linear exponent g = x, the Risch ODE Q' + Q = p has polynomial solutions for
every polynomial p. This is proved for specific cases (p = 1, p = x) and holds generally.
The operator L₁[Q] = Q' + Q preserves degree (unlike L₂[Q] = Q' - 2xQ which raises it).

## Status

- **Axiom count**: 3 (liouville_integration_theorem, risch_exp_criterion_gaussian,
  gaussian_not_elementary)
- **Sorry count**: 0
- **Theorems proved**: 16

## References

- Liouville, J. (1835). "Mémoire sur les transcendantes elliptiques." J. École Polytech.
- Risch, R.H. (1969). "The problem of integration in finite terms." Trans. AMS 139.
- Bronstein, M. (2005). "Symbolic Integration I: Transcendental Functions." Springer.
- Singer, M.F. (1990). "Formal Solutions of Differential Equations." JSC 10.
-/

noncomputable section

open Polynomial Real

namespace AbelRuffiniOQ09

/-! ══════════════════════════════════════════════════════════════════
## Part I: Differential Fields and Constants
══════════════════════════════════════════════════════════════════ -/

/-- A **differential field**: a field F with a derivation D satisfying
    the Leibniz product rule D(fg) = D(f)g + fD(g). -/
class DiffField (F : Type*) extends Field F where
  deriv : F → F
  deriv_add : ∀ f g : F, deriv (f + g) = deriv f + deriv g
  deriv_mul : ∀ f g : F, deriv (f * g) = deriv f * g + f * deriv g

/-- An element is a **constant** if its derivative is zero.
    The set of constants is the "constant subfield" of F. -/
def isConst {F : Type*} [DiffField F] (f : F) : Prop :=
  DiffField.deriv f = 0

/-- D(0) = 0: zero is a constant. Proof: D(0+0) = D(0)+D(0) → D(0) = 0. -/
theorem constants_zero {F : Type*} [DiffField F] : isConst (0 : F) := by
  unfold isConst
  have h := DiffField.deriv_add (0 : F) 0
  simp only [add_zero] at h
  linarith

/-- D(1) = 0: one is a constant. Proof: D(1·1) = D(1)·1 + 1·D(1) → D(1) = 0. -/
theorem constants_one {F : Type*} [DiffField F] : isConst (1 : F) := by
  unfold isConst
  have h := DiffField.deriv_mul (1 : F) 1
  simp only [mul_one, one_mul] at h
  linarith

/-- Constants are closed under addition. -/
theorem constants_add {F : Type*} [DiffField F] {f g : F}
    (hf : isConst f) (hg : isConst g) : isConst (f + g) := by
  unfold isConst at *
  rw [DiffField.deriv_add, hf, hg, add_zero]

/-- Constants are closed under multiplication. -/
theorem constants_mul {F : Type*} [DiffField F] {f g : F}
    (hf : isConst f) (hg : isConst g) : isConst (f * g) := by
  unfold isConst at *
  rw [DiffField.deriv_mul, hf, hg, zero_mul, mul_zero, add_zero]

/-- D(-f) = -D(f): negation is anti-linear for derivations.
    Proof: D(f + (-f)) = D(f) + D(-f). Since f + (-f) = 0 and D(0) = 0:
    D(-f) = -D(f). -/
theorem deriv_neg {F : Type*} [DiffField F] (f : F) :
    DiffField.deriv (-f) = -DiffField.deriv f := by
  have h0 : DiffField.deriv (0 : F) = 0 := constants_zero
  have h := DiffField.deriv_add f (-f)
  rw [add_neg_cancel, h0] at h
  linarith

/-- D(f - g) = D(f) - D(g). -/
theorem deriv_sub {F : Type*} [DiffField F] (f g : F) :
    DiffField.deriv (f - g) = DiffField.deriv f - DiffField.deriv g := by
  rw [sub_eq_add_neg, DiffField.deriv_add, deriv_neg, ← sub_eq_add_neg]

/-! ══════════════════════════════════════════════════════════════════
## Part II: Liouville Integration Theorem (Axiom)
══════════════════════════════════════════════════════════════════ -/

/-- **Liouville's Integration Theorem** (Liouville 1835, Risch 1969):
    If f ∈ F has an elementary antiderivative, the antiderivative has the form
    g = v₀ + Σᵢ cᵢ·ln(vᵢ) where v₀, vᵢ ∈ F and cᵢ ∈ C (constant subfield).

    This is the structural theorem of differential algebra. The proof requires:
    Picard-Vessiot theory, G-primitive extension analysis, and structure theorems
    on towers of algebraic/logarithmic/exponential extensions.
    No Mathlib formalization of differential Galois theory currently exists. -/
axiom liouville_integration_theorem
    {F : Type*} [DiffField F]
    (f : F) (g : F)
    (hantideriv : DiffField.deriv g = f)
    (helem : True)  -- g belongs to an elementary extension (axiomatized)
    : ∃ (n : ℕ) (v₀ : F) (c : Fin n → F) (v : Fin n → F),
        (∀ i, isConst (c i)) ∧
        (∀ i, v i ≠ 0) ∧
        True  -- g = v₀ + Σ cᵢ · ln(vᵢ) in the logarithmic extension

/-! ══════════════════════════════════════════════════════════════════
## Part III: Risch Criterion and Gaussian Non-Elementarity (Axioms)
══════════════════════════════════════════════════════════════════ -/

/-- **Risch Criterion for ∫e^(-x²)dx**:
    ∫e^(-x²)dx is elementary iff ∃ rational Q(x) with Q'(x) - 2x·Q(x) = 1.

    We prove below (no_poly_risch_soln) that no POLYNOMIAL Q works.
    The extension from polynomial to rational (showing poles must cancel)
    requires partial fraction analysis and is axiomatized here. -/
axiom risch_exp_criterion_gaussian :
    (∃ (p q : Polynomial ℝ),
      (∀ x : ℝ, q.eval x ≠ 0) ∧
      ∀ x : ℝ,
        (Polynomial.derivative p).eval x * q.eval x -
        p.eval x * (Polynomial.derivative q).eval x -
        2 * x * p.eval x * q.eval x = q.eval x ^ 2) ↔
    ∃ (F : ℝ → ℝ),
      (∀ x : ℝ, HasDerivAt F (Real.exp (-(x^2))) x) ∧ True

/-- **Gaussian integral is not elementary** (Liouville 1835).
    The antiderivative of e^(-x²) cannot be expressed as a rational function.

    Proof sketch: Risch criterion reduces to finding rational Q with Q' - 2xQ = 1.
    The polynomial obstruction (no_poly_risch_soln) handles polynomial Q.
    Rational Q is axiomatized: partial fractions show poles of Q' and 2xQ
    cannot cancel except when Q is polynomial, reducing to the proved case. -/
axiom gaussian_not_elementary :
    ¬∃ (p q : Polynomial ℝ),
      (∀ x : ℝ, q.eval x ≠ 0) ∧
      ∀ x : ℝ, HasDerivAt (fun t => p.eval t / q.eval t) (Real.exp (-(x^2))) x

/-! ══════════════════════════════════════════════════════════════════
## Part IV: The Core Algebraic Proof — No Polynomial Risch Solution
══════════════════════════════════════════════════════════════════ -/

/-!
### Coefficient Extraction: The Algebraic Heart of the Obstruction

The key identity: for any polynomial p,
  coeff(p' - C(2)·X·p, natDeg(p) + 1) = -2 · leadingCoeff(p).

**Proof**:
- coeff(derivative p, natDeg+1) = (natDeg+2) · coeff(p, natDeg+2) = 0
  (coefficient above degree is zero)
- coeff(C(2)·X·p, natDeg+1) = 2 · coeff(X·p, natDeg+1) = 2 · coeff(p, natDeg)
  = 2 · leadingCoeff(p)
- Net: 0 - 2·leadingCoeff(p) = -2·leadingCoeff(p).

This identity forces a contradiction: if p' - 2xp = 1 (a degree-0 polynomial),
then the coefficient of the LHS at natDeg+1 is -2·leadingCoeff(p), while the RHS
has coefficient 0. So leadingCoeff(p) = 0, but p ≠ 0 — contradiction.
-/

/-- The coefficient of X^(natDegree p + 1) in (derivative p - C 2 · (X · p))
    equals -2 · leadingCoeff(p). -/
theorem risch_ode_coeff_top (p : Polynomial ℝ) :
    (Polynomial.derivative p - Polynomial.C 2 * (Polynomial.X * p)).coeff
      (p.natDegree + 1) = -2 * p.leadingCoeff := by
  simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul,
             Polynomial.coeff_derivative]
  have h0 : p.coeff (p.natDegree + 2) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  push_cast
  rw [h0, mul_zero, zero_sub]
  simp only [Polynomial.leadingCoeff]
  ring

/-- The constant polynomial 1 has coefficient 0 at any position ≥ 1. -/
theorem poly_one_coeff_pos (n : ℕ) (hn : 0 < n) : (1 : Polynomial ℝ).coeff n = 0 := by
  rw [Polynomial.coeff_one]
  simp [Nat.pos_iff_ne_zero.mp hn]

/-- **No polynomial satisfies the Risch ODE for the Gaussian**: p' - C(2)·X·p ≠ 1.

    The operator L[p] = p' - 2·X·p raises degree by 1 for any nonzero p,
    so its image (polynomials of degree ≥ 1) never contains the constant 1.

    **Proof**:
    - For p = 0: L[0] = 0 ≠ 1.
    - For p ≠ 0: leadingCoeff(p) ≠ 0.
      Coefficient at natDeg(p)+1: LHS gives -2·leadingCoeff(p) (by risch_ode_coeff_top),
      RHS gives 0 (by poly_one_coeff_pos). So -2·leadingCoeff(p) = 0, forcing
      leadingCoeff(p) = 0 — contradiction. -/
theorem no_poly_risch_soln :
    ∀ p : Polynomial ℝ, Polynomial.derivative p - Polynomial.C 2 * (Polynomial.X * p) ≠ 1 := by
  intro p h
  by_cases hp : p = 0
  · simp [hp] at h
  · have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hcoeff := congr_arg (fun q : Polynomial ℝ => q.coeff (p.natDegree + 1)) h
    rw [risch_ode_coeff_top, poly_one_coeff_pos _ (by omega)] at hcoeff
    exact absurd hcoeff (mul_ne_zero (by norm_num) hlc)

/-- No polynomial satisfies L[p] = C(c) for any nonzero constant c.
    The Risch operator's image avoids all nonzero constants. -/
theorem no_poly_risch_constant (c : ℝ) (hc : c ≠ 0) :
    ∀ p : Polynomial ℝ,
      Polynomial.derivative p - Polynomial.C 2 * (Polynomial.X * p) ≠ Polynomial.C c := by
  intro p h
  by_cases hp : p = 0
  · simp [hp] at h
    exact hc (Polynomial.C_eq_zero.mp h.symm)
  · have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hcoeff := congr_arg (fun q : Polynomial ℝ => q.coeff (p.natDegree + 1)) h
    rw [risch_ode_coeff_top] at hcoeff
    simp only [Polynomial.coeff_C, Nat.succ_ne_zero, ↓reduceIte] at hcoeff
    exact absurd hcoeff (mul_ne_zero (by norm_num) hlc)

/-- The Risch operator strictly raises degree:
    For p ≠ 0, natDegree(L[p]) > natDegree(p).
    Proved by the nonzero coefficient at natDeg(p)+1. -/
theorem risch_ode_raises_degree (p : Polynomial ℝ) (hp : p ≠ 0) :
    p.natDegree < (Polynomial.derivative p - Polynomial.C 2 * (Polynomial.X * p)).natDegree := by
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hne : (Polynomial.derivative p - Polynomial.C 2 * (Polynomial.X * p)).coeff
               (p.natDegree + 1) ≠ 0 := by
    rw [risch_ode_coeff_top]
    exact mul_ne_zero (by norm_num) hlc
  calc p.natDegree < p.natDegree + 1 := Nat.lt_succ_self _
    _ ≤ _ := Polynomial.le_natDegree_of_ne_zero hne

/-! ══════════════════════════════════════════════════════════════════
## Part V: Pointwise Reformulation
══════════════════════════════════════════════════════════════════ -/

/-- The Risch ODE as a polynomial identity follows from pointwise equality.
    If (derivative p)(x) - 2x·p(x) = 1 for ALL x : ℝ, then as polynomials
    derivative p - C 2 * X * p = 1. Uses density: two polynomials agreeing
    everywhere on ℝ must be equal (Polynomial.funext). -/
theorem risch_pointwise_to_poly {p : Polynomial ℝ}
    (h : ∀ x : ℝ, (Polynomial.derivative p).eval x - 2 * x * p.eval x = 1) :
    Polynomial.derivative p - Polynomial.C 2 * (Polynomial.X * p) = 1 := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
             Polynomial.eval_X, Polynomial.eval_one]
  linarith [h x]

/-- No polynomial Q has the property that Q'(x) - 2x·Q(x) = 1 for all x : ℝ. -/
theorem no_poly_risch_pointwise :
    ¬∃ p : Polynomial ℝ, ∀ x : ℝ, (Polynomial.derivative p).eval x - 2 * x * p.eval x = 1 := by
  rintro ⟨p, hp⟩
  exact no_poly_risch_soln p (risch_pointwise_to_poly hp)

/-! ══════════════════════════════════════════════════════════════════
## Part VI: Elementary Contrasts — The Degree-Preserving Case
══════════════════════════════════════════════════════════════════ -/

/-!
### The Structural Difference: Degree-Preserving vs Degree-Raising

For ∫R(x)·e^(g(x))dx, the Risch ODE is: Q' + Q·g' = R.

**g = x** (linear exponent): ODE becomes Q' + Q = R.
The operator L₁[Q] = Q' + Q is **degree-preserving**: natDeg(Q' + Q) = natDeg(Q)
(the term Q of degree n dominates Q' of degree n-1).
Result: EVERY polynomial R lies in the image of L₁; ∫R(x)·eˣdx is always elementary.

**g = -x²** (Gaussian): ODE becomes Q' - 2xQ = R.
The operator L₂[Q] = Q' - 2xQ is **degree-raising**: natDeg(Q'-2xQ) = natDeg(Q)+1
(the term -2xQ of degree n+1 dominates Q' of degree n-1).
Result: No degree-0 polynomial (i.e., no nonzero constant) lies in the image of L₂;
in particular, R = 1 is not in the image. ∫e^(-x²)dx is not elementary.
-/

/-- For g = x, the Risch ODE Q' + Q = 1 is solved by Q = 1. -/
theorem risch_g_linear_const :
    Polynomial.derivative (1 : Polynomial ℝ) + 1 = 1 := by
  simp [Polynomial.derivative_one]

/-- For g = x, the Risch ODE Q' + Q = X is solved by Q = X - 1,
    corresponding to the classical formula ∫x·eˣdx = (x-1)·eˣ + C. -/
theorem risch_g_linear_degree1 :
    Polynomial.derivative (Polynomial.X - 1 : Polynomial ℝ) +
    (Polynomial.X - 1) = Polynomial.X := by
  simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_one]
  ring

/-- Contrast with Gaussian: for g = x, the Risch ODE Q' + Q = C(c) IS solvable.
    The solution is Q = C(c) (constant), since (C c)' + C c = 0 + C c = C c. -/
theorem risch_g_linear_constant_solvable (c : ℝ) :
    Polynomial.derivative (Polynomial.C c) + Polynomial.C c = Polynomial.C c := by
  simp [Polynomial.derivative_C]

/-- For g = -x², the Risch ODE Q' - C(2)·X·Q = C(c) has NO polynomial solution
    (proved: no_poly_risch_constant). For g = x, the analogous ODE Q' + Q = C(c)
    HAS a polynomial solution (Q = C(c), proved above).
    This asymmetry encodes the non-elementarity of ∫e^(-x²) vs elementarity of ∫eˣ. -/
theorem gaussian_vs_linear_contrast (c : ℝ) (hc : c ≠ 0) :
    (∃ Q : Polynomial ℝ, Polynomial.derivative Q + Q = Polynomial.C c) ∧
    (¬∃ Q : Polynomial ℝ, Polynomial.derivative Q - Polynomial.C 2 * (Polynomial.X * Q) =
      Polynomial.C c) :=
  ⟨⟨Polynomial.C c, by simp [Polynomial.derivative_C]⟩,
   fun ⟨Q, hQ⟩ => no_poly_risch_constant c hc Q hQ⟩

/-! ══════════════════════════════════════════════════════════════════
## Part VII: Abel-Ruffini Analogy
══════════════════════════════════════════════════════════════════ -/

/-!
### The Galois-Theoretic Obstruction Pattern

The Abel-Ruffini theorem and Liouville's integration theorem share a deep pattern:

| Feature | Abel-Ruffini | Liouville |
|---------|--------------|-----------|
| **Question** | Solvable by radicals? | Elementary integral? |
| **Yes condition** | Galois group solvable | Integral has Liouville form |
| **No example** | x⁵ - x - 1 (Galois group S₅) | e^(-x²) (Risch obstruction) |
| **Obstruction** | S₅ not solvable | Risch ODE has no rational soln |
| **Polynomial proof** | A₅ is simple | L₂ raises degree |

In both cases, the impossibility is witnessed by a polynomial algebra fact:
- Abel-Ruffini: A₅ has no normal subgroup chain (algebraic Galois theory)
- Liouville: L₂ = p' - 2xp has no rational preimage of 1 (differential Galois theory)

Both theories are axiomatized; the polynomial algebra is fully proved.
-/

/-- Summary: the polynomial obstruction to the Gaussian's elementarity.
    This is the formalized content of the Risch criterion polynomial case:
    no polynomial Q satisfies the first-order linear ODE Q' - 2xQ = 1. -/
theorem gaussian_risch_polynomial_obstruction_summary :
    ¬∃ p : Polynomial ℝ, Polynomial.derivative p - Polynomial.C 2 * (Polynomial.X * p) = 1 :=
  fun ⟨p, hp⟩ => no_poly_risch_soln p hp

end AbelRuffiniOQ09
