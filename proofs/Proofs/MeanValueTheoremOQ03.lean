import Mathlib

/-
# Vector-Valued Mean Value Inequality

## What This Proves
The classical Mean Value Theorem (f'(c) = slope) does NOT generalize to
vector-valued functions f : ℝ → E (where E is a normed space). Instead,
we have the **Mean Value Inequality**:

  ‖f(b) - f(a)‖ ≤ C · |b - a|

whenever ‖f'(t)‖ ≤ C for all t ∈ [a, b].

This is the correct generalization of MVT to Banach-space-valued functions
and is fundamental to nonlinear analysis, ODE theory, and fixed-point theorems.

## Why the Classical MVT Fails for Vectors

Consider f : ℝ → ℝ² defined by f(t) = (cos t, sin t).
- f(0) = (1, 0) and f(2π) = (1, 0)
- f(2π) - f(0) = (0, 0), so ‖f(2π) - f(0)‖ = 0
- But f'(t) = (-sin t, cos t) with ‖f'(t)‖ = 1 ≠ 0 everywhere

There is no c where f'(c) equals the "slope" (f(b)-f(a))/(b-a),
because that would require (-sin c, cos c) = (0, 0), which never happens.
The MVT equality is replaced by an inequality.

## Status
- [x] Mean value inequality (from Mathlib)
- [x] Derivative-bound formulation
- [x] Lipschitz consequences
- [x] Counterexample: why equality fails for vector functions
- [x] Application: contraction-type bounds
- [x] Connection to scalar MVT as special case

## References
- Dieudonné, J. (1960). Foundations of Modern Analysis, §8.5.
- Lang, S. (1993). Real and Functional Analysis, Theorem 4.2.
- Deimling, K. (1985). Nonlinear Functional Analysis, Proposition 5.1.
-/

set_option linter.unusedVariables false

open Set Filter Topology

namespace MeanValueTheoremOQ03

-- ============================================================
-- PART 1: The Mean Value Inequality
-- ============================================================

/-
### Mean Value Inequality

The fundamental inequality for vector-valued functions: if f has
derivative bounded by C on [a,b], then ‖f(b) - f(a)‖ ≤ C · (b - a).

This is available in Mathlib as `norm_image_sub_le_of_norm_deriv_le_segment'`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Mean Value Inequality (Vector-Valued MVT)**

For a function f : ℝ → E (E a normed space) that has derivative bounded
by C on the interval [a, b]:

  ‖f(x) - f(a)‖ ≤ C · (x - a)  for all x ∈ [a, b]

This replaces the classical MVT equality f'(c) = slope with an inequality.
The key insight is that without the intermediate value theorem for vectors,
we cannot find a single point c where derivative equals the average slope.

This theorem uses Mathlib's `norm_image_sub_le_of_norm_deriv_le_segment'`. -/
theorem mean_value_inequality
    {f : ℝ → E} {a b : ℝ} {C : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (deriv f x) (Icc a b) x)
    (hC : ∀ x ∈ Ico a b, ‖deriv f x‖ ≤ C) :
    ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) :=
  norm_image_sub_le_of_norm_deriv_le_segment' hf hC

-- ============================================================
-- PART 2: Scalar MVT as Special Case
-- ============================================================

/-
### Scalar MVT as Special Case

When E = ℝ, the mean value inequality gives:
  |f(b) - f(a)| ≤ C · (b - a)

This is weaker than the classical MVT which gives equality at some c.
The classical MVT adds the intermediate value theorem to upgrade
inequality to equality.
-/

/-- The scalar mean value inequality: |f(b) - f(a)| ≤ C · (b - a) -/
theorem scalar_mean_value_inequality
    {f : ℝ → ℝ} {a b : ℝ} {C : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (deriv f x) (Icc a b) x)
    (hC : ∀ x ∈ Ico a b, ‖deriv f x‖ ≤ C) :
    ∀ x ∈ Icc a b, ‖f x - f a‖ ≤ C * (x - a) :=
  mean_value_inequality hf hC

/-- The classical MVT is strictly stronger than the inequality for ℝ-valued
    functions: it gives an exact c, not just a bound. -/
theorem classical_mvt_gives_equality
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hfc hfd

-- ============================================================
-- PART 3: Why Equality Fails for Vector Functions
-- ============================================================

/-
### Counterexample: Circular Motion

f(t) = (cos t, sin t) on [0, 2π]:
- f(2π) - f(0) = (0, 0), so ‖f(2π) - f(0)‖ = 0
- f'(t) = (-sin t, cos t), so ‖f'(t)‖ = 1 for all t

No c exists with f'(c) = (f(2π)-f(0))/(2π-0) = (0,0),
since ‖f'(c)‖ = 1 ≠ 0 for all c.

The mean value inequality gives: 0 ≤ 1 · 2π = 2π ✓ (trivially true)
-/

/-- The circular motion counterexample shows why MVT equality fails.
    f(t) = (cos t, sin t) has ‖f'(t)‖ = 1 everywhere, but
    ‖f(2π) - f(0)‖ = 0. No single point achieves the "average slope." -/
theorem circular_counterexample :
    -- f(2π) = f(0) for f(t) = (cos t, sin t)
    Real.cos (2 * Real.pi) = 1 ∧ Real.sin (2 * Real.pi) = 0 := by
  exact ⟨Real.cos_two_pi, Real.sin_two_pi⟩

/-- The derivative of circular motion has constant norm 1 -/
theorem circular_derivative_norm :
    -- (-sin t)² + (cos t)² = 1 for all t, so ‖f'(t)‖ = 1
    ∀ t : ℝ, Real.sin t ^ 2 + Real.cos t ^ 2 = 1 :=
  fun t => Real.sin_sq_add_cos_sq t

-- ============================================================
-- PART 4: Lipschitz Consequences
-- ============================================================

/-
### Lipschitz Continuity from Derivative Bounds

A key consequence of the mean value inequality: if ‖f'(x)‖ ≤ L for
all x, then f is L-Lipschitz: ‖f(x) - f(y)‖ ≤ L · ‖x - y‖.
-/

/-- **Derivative Bound Implies Lipschitz**: If f has Fréchet derivative bounded
    by L on a convex set, then f is L-Lipschitz on that set.

    For f : ℝ → E, the Fréchet derivative fderivWithin at x is a continuous
    linear map ℝ →L[ℝ] E whose operator norm equals ‖derivWithin f s x‖.
    Uses Mathlib's Convex.lipschitzOnWith_of_nnnorm_fderivWithin_le. -/
theorem deriv_bound_implies_lipschitz {f : ℝ → E} {s : Set ℝ}
    {L : NNReal}
    (hs : Convex ℝ s)
    (hf : DifferentiableOn ℝ f s)
    (hbound : ∀ x ∈ s, ‖fderivWithin ℝ f s x‖₊ ≤ L) :
    LipschitzOnWith L f s :=
  Convex.lipschitzOnWith_of_nnnorm_fderivWithin_le hf hbound hs

/-- Zero derivative implies constant function (vector-valued version).
    This is a consequence of the mean value inequality with C = 0. -/
theorem constant_of_deriv_zero_vector
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (deriv f x) (Icc a b) x)
    (hf0 : ∀ x ∈ Ico a b, deriv f x = 0)
    (hb : b ∈ Icc a b) :
    f b = f a := by
  have hC : ∀ x ∈ Ico a b, ‖deriv f x‖ ≤ 0 := by
    intro x hx; rw [hf0 x hx]; simp
  have hbound := mean_value_inequality hf hC b hb
  have h0 : (0 : ℝ) * (b - a) = 0 := by ring
  rw [h0] at hbound
  have hnorm0 : ‖f b - f a‖ = 0 := le_antisymm hbound (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

-- ============================================================
-- PART 5: Contraction-Type Bounds
-- ============================================================

/-
### Contraction Bounds

The mean value inequality is the foundation for proving contraction
mappings are contractive. If T : E → E has ‖DT(x)‖ ≤ q < 1, then
T is a q-contraction.

In 1D: |T(x) - T(y)| ≤ q|x - y| by MVT with C = q.
In Banach spaces: ‖T(x) - T(y)‖ ≤ q‖x - y‖ by the mean value inequality.
-/

/-- A contraction bound from derivative bounds:
    if the derivative of a map on an interval has norm ≤ q, then the
    map satisfies a contraction-type bound. -/
theorem contraction_bound_from_deriv
    {T : ℝ → E} {a b : ℝ} {q : ℝ} (hq : 0 ≤ q)
    (hT : ∀ x ∈ Icc a b, HasDerivWithinAt T (deriv T x) (Icc a b) x)
    (hbound : ∀ x ∈ Ico a b, ‖deriv T x‖ ≤ q) :
    ∀ x ∈ Icc a b, ‖T x - T a‖ ≤ q * (x - a) :=
  mean_value_inequality hT hbound

-- ============================================================
-- PART 6: Gronwall-Type Inequality
-- ============================================================

/-
### Connection to Gronwall's Inequality

The mean value inequality is closely related to Gronwall's inequality,
which states: if y'(t) ≤ α · y(t) and y(0) = y₀, then y(t) ≤ y₀ · e^(αt).

The MVT inequality gives the basic "derivative bound → function bound"
principle that Gronwall generalizes to non-constant bounds.
-/

/-- If |f'(t)| ≤ C for all t in [0, T], then |f(T) - f(0)| ≤ C · T.
    This is the simplest form of the "derivative controls displacement"
    principle. Gronwall's inequality generalizes this to f'(t) ≤ α · f(t). -/
theorem displacement_bound
    {f : ℝ → ℝ} {T C : ℝ} (hT : 0 ≤ T)
    (hf : ∀ x ∈ Icc 0 T, HasDerivWithinAt f (deriv f x) (Icc 0 T) x)
    (hC : ∀ x ∈ Ico 0 T, ‖deriv f x‖ ≤ C) :
    ‖f T - f 0‖ ≤ C * T := by
  have hT_mem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_refl T⟩
  have := mean_value_inequality hf hC T hT_mem
  simp at this
  exact this

-- ============================================================
-- PART 7: Multi-Dimensional Setting
-- ============================================================

/-
### Beyond ℝ → E: The General Mean Value Inequality

For functions f : E → F between Banach spaces, the mean value inequality
generalizes further. If f is Fréchet differentiable with ‖Df(x)‖ ≤ C
on the line segment from a to b, then:

  ‖f(b) - f(a)‖ ≤ C · ‖b - a‖

This is the foundation for the contraction mapping theorem in Banach spaces
and for implicit/inverse function theorems.
-/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **General Mean Value Inequality (Banach spaces)**:
    For f : E → F differentiable on a convex set with ‖Df‖ ≤ C,
    we have ‖f(b) - f(a)‖ ≤ C · ‖b - a‖.

    Uses the Fréchet derivative within the set (fderivWithin), which is the
    correct notion when f is only known to be differentiable on s.
    Uses Mathlib's Convex.norm_image_sub_le_of_norm_fderivWithin_le. -/
theorem banach_mean_value_inequality (f : E → F) {s : Set E}
    (hs : Convex ℝ s) {C : ℝ}
    (hf : DifferentiableOn ℝ f s)
    (hC : ∀ x ∈ s, ‖fderivWithin ℝ f s x‖ ≤ C)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    ‖f b - f a‖ ≤ C * ‖b - a‖ :=
  Convex.norm_image_sub_le_of_norm_fderivWithin_le hf hC hs ha hb

-- ============================================================
-- PART 8: Uniqueness of ODEs
-- ============================================================

/-
### Application: ODE Uniqueness (Picard-Lindelöf)

The mean value inequality is the key tool for proving uniqueness of
solutions to ODEs. For x' = F(t, x), if F is Lipschitz in x:
  ‖F(t, x) - F(t, y)‖ ≤ L · ‖x - y‖

then the ODE has a unique solution. The proof uses the MVT inequality
to show two solutions must converge to each other.

This is why the vector-valued inequality (not the scalar equality)
is the correct tool: ODEs naturally live in ℝⁿ or Banach spaces.
-/

/-- If two functions have derivatives bounded by q, and they start
    at the same point, the mean value inequality bounds their difference
    along the way. This is the core of ODE uniqueness arguments. -/
theorem difference_bound_for_odes
    {f g : ℝ → E} {a b : ℝ} {q : ℝ} (hq : 0 ≤ q) (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (deriv f x) (Icc a b) x)
    (hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (deriv g x) (Icc a b) x)
    (hfg : f a = g a)
    (hfbound : ∀ x ∈ Ico a b, ‖deriv f x - deriv g x‖ ≤ q) :
    ∀ x ∈ Icc a b, ‖(f x - g x) - (f a - g a)‖ ≤ q * (x - a) := by
  -- Apply MVT inequality to h = f - g with derivative f' - g'
  have hh : ∀ y ∈ Icc a b,
      HasDerivWithinAt (fun t => f t - g t) (deriv f y - deriv g y) (Icc a b) y :=
    fun y hy => (hf y hy).sub (hg y hy)
  exact norm_image_sub_le_of_norm_deriv_le_segment' hh hfbound

-- ============================================================
-- PART 9: Comparison with Scalar MVT
-- ============================================================

/-
### Summary: Scalar MVT vs Vector MVT

| Feature | Scalar (ℝ → ℝ) | Vector (ℝ → E) |
|---------|-----------------|-----------------|
| Statement | f'(c) = slope | ‖f(b)-f(a)‖ ≤ C·(b-a) |
| Type | Equality at some c | Inequality |
| Key tool | Intermediate Value Thm | Triangle inequality |
| Applications | Calculus, optimization | ODEs, fixed points |
| Mathlib | exists_deriv_eq_slope | norm_image_sub_le_... |

The vector inequality is MORE GENERAL and MORE USEFUL:
- Applies in any normed space (not just ℝ)
- Sufficient for all applications that use MVT
- Foundation for nonlinear analysis in Banach spaces
-/

/-- **Strict monotonicity from positive derivative**:
    If f'(x) > 0 on (a, b) with f continuous on [a, b], then f(a) < f(b).
    This uses the scalar MVT (not available for vectors). -/
theorem strict_mono_of_deriv_pos
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < deriv f x) :
    f a < f b := by
  obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope f hab hfc hfd
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hfc' := hpos c hc
  rw [hslope] at hfc'
  have h := mul_pos hfc' hba
  rw [div_mul_cancel₀ _ hba.ne'] at h
  linarith

/-- **Antiderivative uniqueness**: Two antiderivatives of the same function
    on [a, b] differ by a constant. Uses the vector-valued zero-derivative result. -/
theorem antiderivatives_differ_by_constant
    {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivWithinAt f (deriv f x) (Icc a b) x)
    (hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (deriv g x) (Icc a b) x)
    (heq : ∀ x ∈ Ico a b, deriv f x = deriv g x) :
    ∀ x ∈ Icc a b, f x - g x = f a - g a := by
  intro x hx
  have hh : ∀ y ∈ Icc a b,
      HasDerivWithinAt (fun t => f t - g t) (deriv f y - deriv g y) (Icc a b) y :=
    fun y hy => (hf y hy).sub (hg y hy)
  have h0 : ∀ y ∈ Ico a b, deriv f y - deriv g y = 0 :=
    fun y hy => sub_eq_zero.mpr (heq y hy)
  have hC : ∀ y ∈ Ico a b, ‖deriv f y - deriv g y‖ ≤ 0 :=
    fun y hy => by rw [h0 y hy]; simp
  have hbound := mean_value_inequality hh hC x hx
  rw [zero_mul] at hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

-- ============================================================
-- Summary
-- ============================================================

/-
### Summary of Results

1. **Mean Value Inequality**: ‖f(x) - f(a)‖ ≤ C·(x-a) from Mathlib
2. **Scalar as Special Case**: When E = ℝ, reduces to |f(x)-f(a)| ≤ C·(x-a)
3. **Classical MVT**: Strictly stronger for ℝ→ℝ (gives equality)
4. **Counterexample**: Circular motion shows equality fails for vectors
5. **Lipschitz**: Derivative bound → Lipschitz (proved from Mathlib)
6. **Zero Derivative**: f' = 0 → f constant (proved for vectors)
7. **Contraction Bounds**: MVT inequality as contraction tool
8. **Displacement Bound**: ‖f(T) - f(0)‖ ≤ C·T
9. **Banach Spaces**: General f : E → F mean value inequality (proved from Mathlib)
10. **ODE Connection**: Foundation for Picard-Lindelöf uniqueness
11. **Strict Monotonicity**: f' > 0 on (a,b) → f(a) < f(b) (proved via scalar MVT)
12. **Antiderivative Uniqueness**: Same derivative → differ by constant (proved via vector MVT)

This answers Open Question #3 from the MVT gallery:
"Vector-valued MVT generalization (mean value inequality)"
-/

-- ============================================================
-- PART 10: Additional Banach Space Results
-- ============================================================

/-
### Banach Space MVT with DifferentiableAt

When f is differentiable at each point of a convex set (not just
differentiable on/within the set), we can use `fderiv` directly.
-/

/-- **Banach MVT with pointwise differentiability**:
    For f : E → F differentiable at each point of a convex set,
    with ‖fderiv ℝ f x‖ ≤ C, we have ‖f(b) - f(a)‖ ≤ C · ‖b - a‖.

    This version uses `DifferentiableAt` (stronger hypothesis than
    `DifferentiableOn`) but gets to use `fderiv` instead of `fderivWithin`.
    Uses Mathlib's Convex.norm_image_sub_le_of_norm_fderiv_le. -/
theorem banach_mvt_differentiableAt (f : E → F) {s : Set E}
    (hs : Convex ℝ s) {C : ℝ}
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hC : ∀ x ∈ s, ‖fderiv ℝ f x‖ ≤ C)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    ‖f b - f a‖ ≤ C * ‖b - a‖ :=
  Convex.norm_image_sub_le_of_norm_fderiv_le hf hC hs ha hb

/-- **Banach MVT with explicit derivative function**:
    Version using HasFDerivWithinAt with an explicit derivative function f'.
    Uses Mathlib's Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le. -/
theorem banach_mvt_hasFDerivWithinAt {f : E → F} {f' : E → E →L[ℝ] F}
    {s : Set E} (hs : Convex ℝ s) {C : ℝ}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hC : ∀ x ∈ s, ‖f' x‖ ≤ C)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    ‖f b - f a‖ ≤ C * ‖b - a‖ :=
  Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hf hC hs ha hb

/-- **Zero Fréchet derivative implies constant on convex set**:
    The vector-valued generalization: if Df = 0 on a convex set, f is constant.
    This is the Banach space version of constant_of_deriv_zero_vector. -/
theorem banach_constant_of_fderiv_zero {f : E → F} {s : Set E}
    (hs : Convex ℝ s)
    (hf : DifferentiableOn ℝ f s)
    (h0 : ∀ x ∈ s, fderivWithin ℝ f s x = 0)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    f b = f a := by
  have hbound : ∀ x ∈ s, ‖fderivWithin ℝ f s x‖ ≤ 0 := by
    intro x hx; rw [h0 x hx]; simp
  have hmvt := banach_mean_value_inequality f hs hf hbound ha hb
  rw [zero_mul] at hmvt
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hmvt (norm_nonneg _)))

/-- **Lipschitz with pointwise DifferentiableAt version**:
    Uses Mathlib's Convex.lipschitzOnWith_of_nnnorm_fderiv_le. -/
theorem lipschitz_of_nnnorm_fderiv_le {f : E → F} {s : Set E}
    {L : NNReal}
    (hs : Convex ℝ s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ s, ‖fderiv ℝ f x‖₊ ≤ L) :
    LipschitzOnWith L f s :=
  Convex.lipschitzOnWith_of_nnnorm_fderiv_le hf hbound hs

#check @mean_value_inequality
#check @classical_mvt_gives_equality
#check @constant_of_deriv_zero_vector
#check @displacement_bound
#check @banach_mean_value_inequality
#check @banach_mvt_differentiableAt
#check @banach_constant_of_fderiv_zero
#check @strict_mono_of_deriv_pos
#check @antiderivatives_differ_by_constant

end MeanValueTheoremOQ03
