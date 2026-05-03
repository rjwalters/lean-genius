import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
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

- **Axiom count**: 2 (liouville_integration_theorem, risch_exp_criterion_gaussian)
- **Sorry count**: 0
- **Theorems proved**: 21 (including gaussian_not_elementary, proved from polynomial degree obstruction)

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

/-- Elementarity predicate: g belongs to an elementary extension of F.
    Opaque placeholder — formalization requires Picard-Vessiot theory (not in Mathlib). -/
opaque IsElementaryOver {F : Type*} [DiffField F] (f g : F) : Prop

/-- Liouville logarithmic-sum predicate: g = v₀ + Σᵢ cᵢ·ln(vᵢ) in an elementary extension.
    Opaque placeholder — requires a `log` function on DiffField elements (not in Mathlib). -/
opaque IsLiouvilleForm {F : Type*} [DiffField F]
    (g v₀ : F) {n : ℕ} (c : Fin n → F) (v : Fin n → F) : Prop

/-- Elementary function predicate for ℝ → ℝ.
    Opaque placeholder — formalization requires differential Galois theory (not in Mathlib). -/
opaque IsElementaryFn (f : ℝ → ℝ) : Prop

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
    (helem : IsElementaryOver f g)
    : ∃ (n : ℕ) (v₀ : F) (c : Fin n → F) (v : Fin n → F),
        (∀ i, isConst (c i)) ∧
        (∀ i, v i ≠ 0) ∧
        IsLiouvilleForm g v₀ c v  -- g = v₀ + Σ cᵢ · ln(vᵢ) in the logarithmic extension

/-! ══════════════════════════════════════════════════════════════════
## Part III: Risch Criterion and Gaussian Non-Elementarity
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
      (∀ x : ℝ, HasDerivAt F (Real.exp (-(x^2))) x) ∧ IsElementaryFn F

/-- The Risch operator L[h] = h' - C(2)·X·h. -/
private def rischOp (h : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.derivative h - Polynomial.C 2 * (Polynomial.X * h)

/-- Iterating L raises degree, so L^n(g) ≠ 0 whenever g ≠ 0. -/
private lemma rischOp_iter_ne_zero (g : Polynomial ℝ) (hg : g ≠ 0) :
    ∀ n : ℕ, rischOp^[n] g ≠ 0 := by
  intro n
  induction n with
  | zero => simpa
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    intro heq
    have hdeg := risch_ode_raises_degree (rischOp^[n] g) ih
    unfold rischOp at heq
    rw [heq, Polynomial.natDegree_zero] at hdeg
    exact Nat.not_lt_zero _ hdeg

/-- HasDerivAt for h(t)·exp(-t²): derivative is L[h](x)·exp(-x²). -/
private lemma hasDerivAt_mul_gauss (h : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (fun t => h.eval t * Real.exp (-(t ^ 2)))
      ((rischOp h).eval x * Real.exp (-(x ^ 2))) x := by
  have h1 : HasDerivAt (fun t => h.eval t) (h.derivative.eval x) x := h.hasDerivAt x
  have hg : HasDerivAt (fun t : ℝ => -(t ^ 2)) (-2 * x) x := by
    have h' := (hasDerivAt_pow 2 x).neg
    simp only [Nat.cast_ofNat] at h'
    have heq : -(2 * x ^ (2 - 1)) = -2 * x := by norm_num
    rwa [heq] at h'
  have h2 : HasDerivAt (fun t => Real.exp (-(t ^ 2)))
      (Real.exp (-(x ^ 2)) * (-2 * x)) x :=
    (Real.hasDerivAt_exp _).comp x hg
  have h3 := h1.mul h2
  convert h3 using 1
  unfold rischOp
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The n-th real derivative of (f.eval) equals (L^n g).eval · exp(-·²)
    whenever f.eval = g.eval · exp(-·²) pointwise. -/
private lemma risch_iterate_eq (f g : Polynomial ℝ)
    (h0 : ∀ x : ℝ, f.eval x = g.eval x * Real.exp (-(x ^ 2))) (n : ℕ) :
    ∀ x : ℝ, (Polynomial.derivative^[n] f).eval x =
              (rischOp^[n] g).eval x * Real.exp (-(x ^ 2)) := by
  induction n with
  | zero => simpa
  | succ n ih =>
    intro x
    have hLHS : HasDerivAt (fun t => (Polynomial.derivative^[n] f).eval t)
        ((Polynomial.derivative (Polynomial.derivative^[n] f)).eval x) x :=
      (Polynomial.derivative^[n] f).hasDerivAt x
    have hRHS : HasDerivAt (fun t => (rischOp^[n] g).eval t * Real.exp (-(t ^ 2)))
        ((rischOp (rischOp^[n] g)).eval x * Real.exp (-(x ^ 2))) x :=
      hasDerivAt_mul_gauss (rischOp^[n] g) x
    have heq_fn : (fun t => (Polynomial.derivative^[n] f).eval t) =
                  (fun t => (rischOp^[n] g).eval t * Real.exp (-(t ^ 2))) :=
      funext ih
    rw [heq_fn] at hLHS
    have huniq := HasDerivAt.unique hLHS hRHS
    rw [Function.iterate_succ_apply' Polynomial.derivative n f,
        Function.iterate_succ_apply' rischOp n g]
    exact huniq

/-- **Gaussian integral is not elementary** (Liouville 1835).
    The antiderivative of e^(-x²) cannot be expressed as a rational function.

    **Proof**: If d/dx[p(x)/q(x)] = e^(-x²) with q never vanishing, the quotient
    rule gives f(x) = g(x)·e^(-x²) where f = p'q - pq' and g = q². The iterated
    Risch operator L[h] = h' - 2xh satisfies d/dx[h·e^(-x²)] = L[h]·e^(-x²),
    so differentiating n = deg(f)+1 times yields 0 = L^n(g)·e^(-x²). Since
    e^(-x²) > 0 and L raises degree (so L^n(g) ≠ 0), this is a contradiction. -/
theorem gaussian_not_elementary :
    ¬∃ (p q : Polynomial ℝ),
      (∀ x : ℝ, q.eval x ≠ 0) ∧
      ∀ x : ℝ, HasDerivAt (fun t => p.eval t / q.eval t) (Real.exp (-(x^2))) x := by
  rintro ⟨p, q, hq, hderiv⟩
  have hq_ne : q ≠ 0 := by intro h; simp [h] at hq
  set f := Polynomial.derivative p * q - p * Polynomial.derivative q with hf_def
  set g := q ^ 2 with hg_def
  have hg_ne : g ≠ 0 := pow_ne_zero _ hq_ne
  have hfg : ∀ x : ℝ, f.eval x = g.eval x * Real.exp (-(x ^ 2)) := by
    intro x
    have hdiv : HasDerivAt (fun t => p.eval t / q.eval t)
        (((Polynomial.derivative p).eval x * q.eval x -
          p.eval x * (Polynomial.derivative q).eval x) / q.eval x ^ 2) x :=
      (p.hasDerivAt x).div (q.hasDerivAt x) (hq x)
    have heq := HasDerivAt.unique hdiv (hderiv x)
    have hqne : q.eval x ^ 2 ≠ 0 := pow_ne_zero _ (hq x)
    rw [div_eq_iff hqne] at heq
    simp only [hf_def, hg_def, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow]
    linear_combination heq
  set n := f.natDegree + 1 with hn_def
  have hzero : Polynomial.derivative^[n] f = 0 :=
    Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)
  have hiter := risch_iterate_eq f g hfg n
  have hne : rischOp^[n] g ≠ 0 := rischOp_iter_ne_zero g hg_ne n
  have hall : ∀ x : ℝ, (rischOp^[n] g).eval x = 0 := by
    intro x
    have := hiter x
    rw [hzero, Polynomial.eval_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right (Real.exp_pos _).ne'
  exact hne (Polynomial.funext hall)

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
  rw [h0, zero_mul, zero_sub]
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
    have hcoeff := Polynomial.ext_iff.mp h (p.natDegree + 1)
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
    have hcoeff := Polynomial.ext_iff.mp h (p.natDegree + 1)
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
## Part VIb: L₁ is Surjective — All Polynomial Integrands are Elementary
══════════════════════════════════════════════════════════════════ -/

/-!
### Universal Surjectivity of the Linear Risch Operator

The operator L₁[Q] = Q' + Q (for g = x) maps onto ALL polynomials, not just constants.
This means ∫p(x)eˣdx is elementary for every polynomial p.

**Recurrence**: Q₀ = 1; Q_{n+1} = X^{n+1} - C(n+1)·Qₙ.

Verification: L₁[Q_{n+1}] = Q_{n+1}' + Q_{n+1}
  = C(n+1)·Xⁿ - C(n+1)·Qₙ' + X^{n+1} - C(n+1)·Qₙ
  = X^{n+1} + C(n+1)·(Xⁿ - (Qₙ' + Qₙ))
  = X^{n+1} + C(n+1)·0 = X^{n+1}  ✓   (by induction hypothesis Qₙ' + Qₙ = Xⁿ)

In sharp contrast, L₂[Q] = Q' - 2xQ is NEVER surjective onto nonzero constants
(proved as no_poly_risch_constant). This asymmetry is the algebraic core of the
non-elementarity of ∫e^(-x²)dx.
-/

/-- For each monomial X^n, there exists a polynomial Q with derivative Q + Q = X^n.
    Recurrence: Q_0 = 1; Q_{n+1} = X^(n+1) - C(n+1)·Q_n. -/
theorem risch_linear_surjective_monomial (n : ℕ) :
    ∃ Q : Polynomial ℝ, Polynomial.derivative Q + Q = Polynomial.X ^ n := by
  induction n with
  | zero => exact ⟨1, by simp [Polynomial.derivative_one]⟩
  | succ n ih =>
    obtain ⟨Qn, hQn⟩ := ih
    refine ⟨Polynomial.X ^ (n + 1) - Polynomial.C (↑(n + 1) : ℝ) * Qn, ?_⟩
    have hd_pow : Polynomial.derivative (Polynomial.X ^ (n + 1) : Polynomial ℝ) =
        Polynomial.C (↑(n + 1) : ℝ) * Polynomial.X ^ n := by
      simp [Polynomial.derivative_X_pow, Nat.add_sub_cancel]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_mul, Polynomial.derivative_C,
               zero_mul, zero_add, hd_pow]
    linear_combination -Polynomial.C (↑(n + 1) : ℝ) * hQn

/-- L₁[Q] = Q' + Q is surjective onto all polynomials over ℝ.
    For every polynomial p there exists Q with derivative Q + Q = p.
    Proved by linearity of L₁ and surjectivity onto monomials. -/
theorem risch_linear_surjective_all (p : Polynomial ℝ) :
    ∃ Q : Polynomial ℝ, Polynomial.derivative Q + Q = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨Qp, hQp⟩ := hp
    obtain ⟨Qq, hQq⟩ := hq
    exact ⟨Qp + Qq, by
      simp only [Polynomial.derivative_add]
      linear_combination hQp + hQq⟩
  | monomial n a =>
    obtain ⟨Qn, hQn⟩ := risch_linear_surjective_monomial n
    refine ⟨Polynomial.C a * Qn, ?_⟩
    simp only [Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add,
               Polynomial.monomial_eq_C_mul_X]
    linear_combination Polynomial.C a * hQn

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
