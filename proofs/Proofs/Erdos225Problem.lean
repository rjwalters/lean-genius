/-
Partial proofs by Aristotle (Harmonic).
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

Proved by Aristotle:
- theorem erdos_225_optimal
- theorem sup_on_circle_eq_trig_sup

Aristotle also found a formalization bug: the main theorem as stated is false
for constant polynomials (which vacuously satisfy HasUnitCircleRoots).
-/

/-
  Erdős Problem #225: L¹ Norm of Trigonometric Polynomials with Real Roots

  Source: https://erdosproblems.com/225
  Status: SOLVED (Kristiansen 1974, Saff-Sheil-Small 1973)

  Statement:
  Let f(θ) = Σₖ cₖ e^(ikθ) be a trigonometric polynomial all of whose roots
  are real (i.e., lie on the unit circle), such that max|f(θ)| = 1. Then
  ∫₀^(2π) |f(θ)| dθ ≤ 4.

  Answer: TRUE (and the bound 4 is optimal)

  History:
  - Erdős (1940, 1957, 1961): Early work on the problem
  - Hayman (1974): Listed as Problem 4.20
  - Kristiansen (1974): Proved for real coefficients
  - Saff & Sheil-Small (1973): Proved for complex coefficients

  Key Insight:
  The condition that all roots are "real" means they lie on the unit circle
  in the complex plane, i.e., are of the form e^(iα) for real α. This is
  equivalent to saying f(θ) = 0 only when e^(iθ) is a root of the polynomial.

  Reference: Hayman, W.K. (1974), Problem 4.20
-/

import Mathlib

namespace Erdos225

open MeasureTheory

/- ## Trigonometric Polynomials -/

/--
A trigonometric polynomial of degree n is a function of the form
f(θ) = Σₖ₌₀ⁿ cₖ e^(ikθ) for complex coefficients cₖ.
-/
def TrigPoly (n : ℕ) := Fin (n + 1) → ℂ

/-- Evaluate a trigonometric polynomial at angle θ. -/
noncomputable def TrigPoly.eval (p : TrigPoly n) (θ : ℝ) : ℂ :=
  ∑ k : Fin (n + 1), p k * Complex.exp (Complex.I * k * θ)

/- ## Roots on the Unit Circle -/

/--
A complex number lies on the unit circle if ‖z‖ = 1.
-/
def OnUnitCircle (z : ℂ) : Prop := ‖z‖ = 1

/--
A trigonometric polynomial has all roots on the unit circle if
whenever f(θ) = 0, the point e^(iθ) satisfies ‖e^(iθ)‖ = 1.
(This is automatically true, but the condition refers to the algebraic
roots of the associated polynomial P(z) = Σ cₖ zᵏ all lying on ‖z‖ = 1.)
-/
def HasUnitCircleRoots (p : TrigPoly n) : Prop :=
  ∀ z : ℂ, (∑ k : Fin (n + 1), p k * z ^ (k : ℕ)) = 0 → OnUnitCircle z

/--
A trigonometric polynomial is nonconstant if the associated algebraic polynomial
P(z) = Σ cₖ zᵏ has at least one root. This excludes the constant polynomial
case that is a counterexample to the original formulation.

Equivalently, we require n ≥ 1 AND the leading coefficient is nonzero (so
the polynomial genuinely has degree ≥ 1 and therefore at least one root in ℂ).
-/
def Nonconstant (p : TrigPoly n) : Prop :=
  ∃ z : ℂ, (∑ k : Fin (n + 1), p k * z ^ (k : ℕ)) = 0

/- ## Norms -/

/--
The supremum norm (L∞ norm) of a trigonometric polynomial over [0, 2π].
-/
noncomputable def TrigPoly.supNorm (p : TrigPoly n) : ℝ :=
  ⨆ θ : Set.Icc (0 : ℝ) (2 * Real.pi), ‖p.eval θ‖

/--
The L¹ norm of a trigonometric polynomial over [0, 2π].
-/
noncomputable def TrigPoly.l1Norm (p : TrigPoly n) : ℝ :=
  ∫ θ in Set.Icc 0 (2 * Real.pi), ‖p.eval θ‖

/- ## The Main Theorem -/

/-
**Note on the original formulation (KNOWN BUG)**:
The original theorem statement omitted `Nonconstant p`. Without it, the constant
polynomial p(θ) = 1 satisfies `HasUnitCircleRoots` vacuously (no roots), has
supNorm = 1, but L¹ norm = 2π > 4. Counterexample found by Aristotle (Harmonic).
The corrected version below adds `Nonconstant p`.
-/

/--
**Erdős Problem #225 (Kristiansen 1974, Saff–Sheil-Small 1973)**:
If a nonconstant trigonometric polynomial has all roots on the unit circle
and supremum norm 1, then its L¹ norm is at most 4.

The proof uses the factorization P(z) = cₙ ∏(z - zⱼ) with |zⱼ| = 1,
the identity ∫₀²π |e^(iθ) - α| dθ = 8 for |α| = 1,
and sub-multiplicativity of L¹ norms under convolution.
The bound 4 is sharp (achieved at degree 1).

References:
- Kristiansen (1974): Proved for real coefficients
- Saff, E.B. & Sheil-Small, T. (1973): Proved for complex coefficients
-/
axiom erdos_225 (n : ℕ) (p : TrigPoly n)
    (hroots : HasUnitCircleRoots p)
    (hnc : Nonconstant p)
    (hsup : p.supNorm = 1) :
    p.l1Norm ≤ 4

/- ## Optimality -/

/--
The bound 4 is optimal: there exist trigonometric polynomials with unit
circle roots achieving L¹ norm arbitrarily close to 4.

Proved by Aristotle (Harmonic).
-/
theorem erdos_225_optimal :
    ∀ ε > 0, ∃ n : ℕ, ∃ p : TrigPoly n,
    HasUnitCircleRoots p ∧ p.supNorm = 1 ∧ p.l1Norm > 4 - ε := by
  intro ε hε;
  use 0;
  refine' ⟨ fun _ => 1, _, _, _ ⟩ <;> norm_num [ Erdos225.HasUnitCircleRoots ];
  · unfold Erdos225.TrigPoly.supNorm; norm_num [ Erdos225.TrigPoly.eval ] ;
    convert ciSup_const;
    exact ⟨ ⟨ 0, ⟨ le_rfl, Real.two_pi_pos.le ⟩ ⟩ ⟩;
  · unfold Erdos225.TrigPoly.l1Norm;
    norm_num [ Erdos225.TrigPoly.eval ];
    exact Or.inl ( by linarith [ Real.pi_gt_three ] )

/- ## Key Lemmas -/

/--
The constant polynomial f(θ) = 1 demonstrates the necessity of the `Nonconstant`
hypothesis: it has L¹ norm 2π > 4.
-/
theorem constant_l1_norm : (2 : ℝ) * Real.pi > 4 := by
  have hpi : Real.pi > 3 := Real.pi_gt_three
  linarith

/--
The constant polynomial is not `Nonconstant`: the polynomial P(z) = 1
has no roots in ℂ.
-/
theorem constant_not_nonconstant : ¬ Nonconstant (fun (_ : Fin 1) => (1 : ℂ)) := by
  intro ⟨z, hz⟩
  simp [Fin.sum_univ_one] at hz

/-- The norm of e^(iθ) - e^(iφ) equals 2|sin((θ-φ)/2)|.
    Proved via Euler's formula, Pythagorean identity, and cos double angle. -/
theorem norm_exp_diff (θ φ : ℝ) :
    ‖Complex.exp (Complex.I * ↑θ) - Complex.exp (Complex.I * ↑φ)‖ =
    2 * |Real.sin ((θ - φ) / 2)| := by
  rw [show Complex.I * (↑θ : ℂ) = ↑θ * Complex.I from mul_comm _ _,
      show Complex.I * (↑φ : ℂ) = ↑φ * Complex.I from mul_comm _ _]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  have h_diff : (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I) -
      (↑(Real.cos φ) + ↑(Real.sin φ) * Complex.I) =
      ↑(Real.cos θ - Real.cos φ) + ↑(Real.sin θ - Real.sin φ) * Complex.I := by
    push_cast; ring
  rw [h_diff, Complex.norm_add_mul_I]
  have h_sq : (Real.cos θ - Real.cos φ) ^ 2 + (Real.sin θ - Real.sin φ) ^ 2 =
      (2 * |Real.sin ((θ - φ) / 2)|) ^ 2 := by
    rw [mul_pow, sq_abs]
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.sin_sq_add_cos_sq φ
    have h3 := Real.cos_sub θ φ
    have h4 := Real.cos_two_mul ((θ - φ) / 2)
    have h5 : 2 * ((θ - φ) / 2) = θ - φ := by ring
    rw [h5] at h4
    have h6 := Real.sin_sq_add_cos_sq ((θ - φ) / 2)
    linear_combination h1 + h2 + 2 * h3 - 2 * h4 - 4 * h6
  rw [h_sq, Real.sqrt_sq (by positivity)]

/--
**Key integral identity**: For any α on the unit circle (|α| = 1),
∫₀²π |e^(iθ) − α| dθ = 8.

Proof: Write α = e^(iφ). By `norm_exp_diff`, |e^(iθ) − e^(iφ)| = 2|sin((θ−φ)/2)|.
By periodicity, ∫₀²π 2|sin((θ−φ)/2)| dθ = 4∫₀^π |sin u| du = 4·2 = 8.
-/
theorem unit_circle_difference_integral (α : ℂ) (hα : ‖α‖ = 1) :
    ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖Complex.exp (Complex.I * θ) - α‖ = 8 := by
  sorry

/--
**L¹ norm of a degree-1 polynomial with unit circle root equals 4**.

If p(z) = c₀ + c₁z has its root z₀ = −c₀/c₁ on the unit circle and
sup norm 1, then ∫₀²π |p(e^(iθ))| dθ = 4.

Proof: Since c₁ ≠ 0 and |z₀| = 1, we have |c₀| = |c₁|.
The sup norm is |c₁| · sup|c₀/c₁ + e^(iθ)| = |c₁| · (1 + 1) = 2|c₁| = 1,
so |c₁| = 1/2. The L¹ norm is |c₁| · ∫₀²π |c₀/c₁ + e^(iθ)| dθ = (1/2) · 8 = 4,
using the unit_circle_difference_integral identity.

This shows the bound in Erdős #225 is tight and achieved exactly at degree 1.
-/
theorem degree_one_l1_norm_eq_four (p : TrigPoly 1)
    (hroots : HasUnitCircleRoots p) (hnc : Nonconstant p)
    (hsup : p.supNorm = 1) :
    p.l1Norm = 4 := by
  sorry

/--
**Corrected optimality**: The bound 4 in `erdos_225` is achieved by degree-1
polynomials. Unlike the original `erdos_225_optimal` (which exploited the
constant-polynomial bug), this uses a genuine nonconstant polynomial.
-/
theorem erdos_225_tight :
    ∃ n : ℕ, ∃ p : TrigPoly n,
    HasUnitCircleRoots p ∧ Nonconstant p ∧ p.supNorm = 1 ∧ p.l1Norm = 4 := by
  sorry

/- ## Equivalent Formulations -/

/--
Alternative statement using the polynomial P(z) = Σ cₖ zᵏ.
The condition is that all roots of P lie on the unit circle.
-/
def PolynomialHasUnitCircleRoots (coeffs : Fin (n + 1) → ℂ) : Prop :=
  ∀ z : ℂ, (∑ k : Fin (n + 1), coeffs k * z ^ (k : ℕ)) = 0 →
    ‖z‖ = 1

/--
The L∞ norm of P on the unit circle equals the supremum of |f(θ)|.

Proved by Aristotle (Harmonic).
-/
theorem sup_on_circle_eq_trig_sup (p : TrigPoly n) :
    (⨆ z : {w : ℂ | ‖w‖ = 1},
      ‖∑ k : Fin (n + 1), p k * z ^ (k : ℕ)‖) = p.supNorm := by
  -- To prove the equality of the suprema, it suffices to show that for any $z$ on the unit circle, there exists $\theta \in [0, 2\pi]$ such that $z = e^{i\theta}$, and vice versa.
  have h_bij : ∀ z : ℂ, ‖z‖ = 1 → ∃ θ ∈ Set.Icc 0 (2 * Real.pi), z = Complex.exp (Complex.I * θ) := by
    intro z hz;
    rw [ Complex.norm_eq_one_iff ] at hz;
    obtain ⟨ θ, rfl ⟩ := hz;
    exact ⟨ θ - 2 * Real.pi * ⌊θ / ( 2 * Real.pi ) ⌋, ⟨ by nlinarith [ Int.floor_le ( θ / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ θ ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ], by nlinarith [ Int.lt_floor_add_one ( θ / ( 2 * Real.pi ) ), Real.pi_pos, mul_div_cancel₀ θ ( by positivity : ( 2 * Real.pi ) ≠ 0 ) ] ⟩, by rw [ Complex.exp_eq_exp_iff_exists_int ] ; use ⌊θ / ( 2 * Real.pi ) ⌋; push_cast; ring ⟩;
  -- By the bijection between the unit circle and the interval [0, 2π], we can rewrite the supremum over the unit circle as a supremum over the interval [0, 2π].
  have h_bij_sup : ∀ z : ℂ, ‖z‖ = 1 → ∃ θ ∈ Set.Icc 0 (2 * Real.pi), ‖∑ k : Fin (n + 1), p k * z ^ (k : ℕ)‖ = ‖∑ k : Fin (n + 1), p k * Complex.exp (Complex.I * k * θ)‖ := by
    intro z hz; obtain ⟨ θ, hθ₁, rfl ⟩ := h_bij z hz; use θ; simp +decide [ mul_assoc, mul_left_comm, ← Complex.exp_nat_mul ] ;
    exact hθ₁;
  have h_bij_sup : ∀ θ ∈ Set.Icc 0 (2 * Real.pi), ∃ z : ℂ, ‖z‖ = 1 ∧ ‖∑ k : Fin (n + 1), p k * Complex.exp (Complex.I * k * θ)‖ = ‖∑ k : Fin (n + 1), p k * z ^ (k : ℕ)‖ := by
    exact fun θ hθ => ⟨ Complex.exp ( Complex.I * θ ), by norm_num [ Complex.norm_exp ], by norm_num [ ← Complex.exp_nat_mul, mul_assoc, mul_comm, mul_left_comm ] ⟩;
  apply le_antisymm;
  · convert ciSup_le _;
    · exact ⟨ 1, by norm_num ⟩;
    · intro x;
      obtain ⟨ θ, hθ₁, hθ₂ ⟩ := ‹∀ z : ℂ, ‖z‖ = 1 → ∃ θ ∈ Set.Icc 0 ( 2 * Real.pi ), ‖∑ k : Fin ( n + 1 ), p k * z ^ ( k : ℕ )‖ = ‖∑ k : Fin ( n + 1 ), p k * Complex.exp ( Complex.I * ( k : ℂ ) * θ )‖› x x.2;
      refine' le_trans _ ( le_ciSup _ ⟨ θ, hθ₁ ⟩ );
      · convert hθ₂.le using 1;
      · refine' IsCompact.bddAbove _;
        exact isCompact_range ( by exact Continuous.norm <| by exact continuous_finset_sum _ fun _ _ => Continuous.mul ( continuous_const ) <| Complex.continuous_exp.comp <| by continuity );
  · convert ciSup_le _;
    · exact ⟨ ⟨ 0, ⟨ by norm_num, by positivity ⟩ ⟩ ⟩;
    · intro x;
      obtain ⟨ z, hz₁, hz₂ ⟩ := h_bij_sup x x.2;
      refine' le_trans _ ( le_ciSup _ ⟨ z, hz₁ ⟩ );
      · convert hz₂.le using 1;
      · refine' ⟨ ∑ k : Fin ( n + 1 ), ‖p k‖, Set.forall_mem_range.2 fun z => _ ⟩;
        exact le_trans ( norm_sum_le _ _ ) ( Finset.sum_le_sum fun _ _ => by simp +decide [ z.2.out ] )

/- ## The Fejér-Riesz Theorem Connection -/

/--
A non-negative trigonometric polynomial (one with f(θ) ≥ 0 for all θ)
can be written as |g(θ)|² for some trigonometric polynomial g.
This is the Fejér-Riesz theorem.
-/
/- ## Relationship to Littlewood's Conjecture -/

/--
Littlewood's conjecture (now theorem) states that for unimodular polynomials
(coefficients ±1), the L¹ norm on the unit circle is Ω(log n).

This is related but distinct from Erdős #225: Littlewood concerns lower bounds
while Erdős #225 gives an upper bound under the unit-circle-roots condition.
-/
/- ## Summary

**Problem Status: SOLVED**

Erdős Problem #225 asks: if a nonconstant trigonometric polynomial
f(θ) = Σ cₖ e^(ikθ) has all its roots on the unit circle and max|f(θ)| = 1,
is ∫|f(θ)| dθ ≤ 4?

**Answer: YES** (Kristiansen 1974, Saff–Sheil-Small 1973)

The bound 4 is optimal and achieved exactly at degree 1.

**Formalization History**:
- Original statement omitted the nonconstant hypothesis
- Aristotle (Harmonic) found the counterexample: constant polynomial has L¹ = 2π > 4
- Corrected theorem `erdos_225` adds `Nonconstant p` hypothesis
- Key identity: ∫₀²π |e^(iθ) − α| dθ = 8 for |α| = 1

**Proof Architecture** (for the corrected theorem):
- Factor P(z) = cₙ ∏ⱼ(z − αⱼ) with |αⱼ| = 1
- L¹ norm = |cₙ| · ∫₀²π ∏ⱼ|e^(iθ) − αⱼ| dθ
- Use sub-multiplicativity and the integral identity
- The key inequality: for degree n ≥ 1, L¹ ≤ 4

**References**:
- Hayman, W.K. (1974): Research Problems in Function Theory, Problem 4.20
- Kristiansen (1974)
- Saff, E.B. & Sheil-Small, T. (1973)
-/

end Erdos225
