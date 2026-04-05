/-
# Triangle Inequality for Geodesic/Path Metrics (OQ-04)

The triangle inequality for geodesic distances on Riemannian manifolds.

## Mathematical Background

On a Riemannian manifold M, the **geodesic distance** between two points p, q is:

  d(p, q) = inf { length(γ) | γ : [0,1] → M is a piecewise-smooth path from p to q }

where length(γ) = ∫₀¹ ‖γ'(t)‖ dt is the Riemannian arc length.

The triangle inequality d(p, r) ≤ d(p, q) + d(q, r) holds because:
1. Given any path γ₁ from p to q and γ₂ from q to r, their concatenation γ₁ ∗ γ₂
   is a path from p to r
2. length(γ₁ ∗ γ₂) = length(γ₁) + length(γ₂)   [additivity under concatenation]
3. Therefore d(p, r) ≤ length(γ₁) + length(γ₂) for any choice of γ₁, γ₂
4. Taking infimum over all γ₁, γ₂: d(p, r) ≤ d(p, q) + d(q, r)

## What We Formalize

Mathlib (v4.26.0) lacks full Riemannian manifold formalization, but has:
- `Path x y` : continuous paths between points (PathConnected.lean)
- `eVariationOn` : total variation = arc length for continuous curves (BoundedVariation.lean)
- `Path.trans` : path concatenation (γ₁ ∗ γ₂)
- `eVariationOn.comp_eq_of_monotoneOn` : reparameterization invariance of arc length

We formalize the **path metric** (intrinsic metric) in any metric space, which captures
the essential mathematical content. The same proof applies verbatim to Riemannian manifolds
once Riemannian structure is added to Mathlib.

## Key Results

1. `pathLength_trans` : length(γ₁ ∗ γ₂) = length(γ₁) + length(γ₂)
2. `intrinsicDist_triangle` : triangle inequality for path/intrinsic metric

## Status

- [x] Triangle inequality for path metric (main theorem, complete proof, 0 sorries)
- [x] Additivity of arc length under concatenation (complete)
- [x] Application to sphere as concrete Riemannian manifold example
- [ ] Full Riemannian manifold (awaits Mathlib Riemannian geometry formalization)
-/

import Mathlib.Topology.Connected.PathConnected
import Mathlib.Analysis.BoundedVariation
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

open Set ENNReal

namespace TriangleInequalityOQ04

variable {X : Type*} [PseudoMetricSpace X]

/-!
## Part I: Path Length via Total Variation

The **arc length** of a continuous curve γ : [0,1] → X is its total variation,
measuring the total distance traveled along the path.

For a smooth curve in ℝⁿ, this equals ∫₀¹ ‖γ'(t)‖ dt.
We use `eVariationOn` (total variation in ℝ≥0∞) to handle the general continuous case.
-/

/-- The arc length of a path γ : x → y, defined as total variation on [0,1].

    Uses ℝ≥0∞ to avoid needing compactness or rectifiability assumptions. -/
noncomputable def pathLength {x y : X} (γ : Path x y) : ℝ≥0∞ :=
  eVariationOn γ.extend (Icc 0 1)

/-- A constant path (staying at a single point x) has zero arc length. -/
@[simp]
theorem pathLength_refl (x : X) : pathLength (Path.refl x) = 0 := by
  simp only [pathLength, Path.refl_extend]
  rw [eVariationOn.eq_zero_iff]
  intro a _ b _
  simp [edist_self]

/-!
## Part II: Path Concatenation and Length Additivity

`Path.trans γ₁ γ₂` concatenates two paths:
- First half t ∈ [0, 1/2]: runs γ₁ at double speed (t ↦ γ₁(2t))
- Second half t ∈ [1/2, 1]: runs γ₂ at double speed (t ↦ γ₂(2t-1))

The key property: length(γ₁ ∗ γ₂) = length(γ₁) + length(γ₂).

Proof uses:
- `eVariationOn.Icc_add_Icc` : variation splits at an intermediate point
- `eVariationOn.comp_eq_of_monotoneOn` : reparameterization invariance
-/

-- Image of [0, 1/2] under t ↦ 2t equals [0, 1]
private lemma image_scale_half : (· * 2) '' Icc (0 : ℝ) (1 / 2) = Icc 0 1 := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨x / 2, ⟨by linarith, by linarith⟩, by ring⟩

-- Image of [1/2, 1] under t ↦ 2t - 1 equals [0, 1]
private lemma image_shift_half : (· * 2 - 1) '' Icc (1 / 2 : ℝ) 1 = Icc 0 1 := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h0, h1⟩
    exact ⟨(x + 1) / 2, ⟨by linarith, by linarith⟩, by ring⟩

/-- On [0, 1/2], the concatenated path γ₁ ∗ γ₂ agrees with t ↦ γ₁(2t). -/
private lemma eqOn_first {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    EqOn (γ₁.trans γ₂).extend (γ₁.extend ∘ (· * 2)) (Icc (0 : ℝ) (1 / 2)) := by
  intro t ⟨ht0, ht12⟩
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, by linarith⟩
  have h2t : t * 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [Function.comp_apply]
  -- (γ₁.trans γ₂).extend t = (γ₁.trans γ₂) ⟨t, ht01⟩  [since t ∈ [0,1]]
  rw [Path.extend_apply _ ht01]
  -- By trans_apply: = γ₁ ⟨2t, ...⟩  [since t ≤ 1/2]
  rw [Path.trans_apply]
  simp only [dif_pos ht12]
  -- γ₁.extend (t * 2) = γ₁ ⟨t*2, h2t⟩  [since t*2 ∈ [0,1]]
  rw [Path.extend_apply γ₁ h2t]
  -- Both sides are γ₁ applied to a subtype element with val 2t = t*2
  congr 1; ext; ring

/-- On [1/2, 1], the concatenated path γ₁ ∗ γ₂ agrees with t ↦ γ₂(2t - 1). -/
private lemma eqOn_second {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    EqOn (γ₁.trans γ₂).extend (γ₂.extend ∘ (· * 2 - 1)) (Icc (1 / 2 : ℝ) 1) := by
  intro t ⟨ht12, ht1⟩
  have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨by linarith, ht1⟩
  have h2t : t * 2 - 1 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  simp only [Function.comp_apply]
  rw [Path.extend_apply _ ht01]
  rw [Path.trans_apply]
  by_cases h : t ≤ 1 / 2
  · -- t = 1/2: both sides equal the midpoint y
    obtain rfl : t = 1 / 2 := le_antisymm h ht12
    simp only [le_refl, dif_pos]
    -- LHS: γ₁ at time 1 = target of γ₁ = y
    have lhs_eq : γ₁ ⟨2 * (1 / 2 : ℝ), by norm_num⟩ = y := by
      have heq : (⟨2 * (1 / 2 : ℝ), by norm_num⟩ : unitInterval) = ⟨1, by norm_num⟩ := by ext; norm_num
      rw [heq]; exact γ₁.target
    -- RHS: γ₂.extend at time 0 = source of γ₂ = y
    have rhs_eq : γ₂.extend ((1 / 2 : ℝ) * 2 - 1) = y := by
      have : (1 / 2 : ℝ) * 2 - 1 = 0 := by norm_num
      rw [this, γ₂.extend_zero]
    rw [lhs_eq, rhs_eq]
  · -- t > 1/2: else branch of trans_apply
    rw [dif_neg h, Path.extend_apply γ₂ h2t]
    congr 1; ext; ring

/-- **Length Additivity Under Concatenation**

    The arc length of the concatenated path γ₁ ∗ γ₂ equals the sum of the lengths.

    Proof:
    1. Split [0,1] at 1/2: length(γ₁ ∗ γ₂) = varFirst + varSecond
    2. varFirst = variation on [0,1/2] = variation of γ₁(2·) on [0,1/2]
                = variation of γ₁ on [0,1]   [by reparameterization invariance]
    3. varSecond = variation on [1/2,1] = variation of γ₂(2·-1) on [1/2,1]
                 = variation of γ₂ on [0,1]  [by reparameterization invariance] -/
theorem pathLength_trans {x y z : X} (γ₁ : Path x y) (γ₂ : Path y z) :
    pathLength (γ₁.trans γ₂) = pathLength γ₁ + pathLength γ₂ := by
  simp only [pathLength]
  -- Step 1: Split [0,1] at 1/2
  have hsplit : eVariationOn (γ₁.trans γ₂).extend (Icc (0 : ℝ) (1 / 2)) +
      eVariationOn (γ₁.trans γ₂).extend (Icc (1 / 2 : ℝ) 1) =
      eVariationOn (γ₁.trans γ₂).extend (Icc (0 : ℝ) 1) := by
    have h := eVariationOn.Icc_add_Icc (γ₁.trans γ₂).extend
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 ≤ 1 by norm_num)
      (show (1 / 2 : ℝ) ∈ Set.univ from Set.mem_univ _)
    simp only [Set.univ_inter] at h; exact h
  -- Step 2: First half = length of γ₁ (reparameterization t ↦ 2t on [0, 1/2])
  have first : eVariationOn (γ₁.trans γ₂).extend (Icc (0 : ℝ) (1 / 2)) =
      eVariationOn γ₁.extend (Icc 0 1) := by
    rw [eVariationOn.eq_of_eqOn (eqOn_first γ₁ γ₂),
        eVariationOn.comp_eq_of_monotoneOn γ₁.extend (· * 2)
          (fun a _ b _ h => by linarith),
        image_scale_half]
  -- Step 3: Second half = length of γ₂ (reparameterization t ↦ 2t-1 on [1/2, 1])
  have second : eVariationOn (γ₁.trans γ₂).extend (Icc (1 / 2 : ℝ) 1) =
      eVariationOn γ₂.extend (Icc 0 1) := by
    rw [eVariationOn.eq_of_eqOn (eqOn_second γ₁ γ₂),
        eVariationOn.comp_eq_of_monotoneOn γ₂.extend (· * 2 - 1)
          (fun a _ b _ h => by linarith),
        image_shift_half]
  -- Combine: split + first + second gives the result
  -- Goal: eVar (trans) [0,1] = eVar γ₁ [0,1] + eVar γ₂ [0,1]
  rw [← hsplit, first, second]

/-!
## Part III: The Path (Intrinsic) Metric

The **geodesic distance** or **intrinsic metric** between two points is the infimum
of arc lengths over all continuous paths connecting them.

On a Riemannian manifold, this equals the Riemannian geodesic distance.
-/

/-- The intrinsic (path/geodesic) distance between two points: infimum of path lengths. -/
noncomputable def intrinsicDist (x y : X) : ℝ≥0∞ :=
  ⨅ γ : Path x y, pathLength γ

@[simp]
theorem intrinsicDist_self (x : X) : intrinsicDist x x = 0 :=
  le_antisymm (iInf_le_of_le (Path.refl x) (pathLength_refl x).le) (zero_le _)

/-- **Main Theorem: Triangle Inequality for Geodesic/Path Distance**

    For any points x, y, z in a (pseudo-)metric space:
      d_path(x, z) ≤ d_path(x, y) + d_path(y, z)

    **Proof by concatenation:**
    - For any γ₁ : x → y and γ₂ : y → z:
        d_path(x, z) ≤ length(γ₁.trans γ₂) = length(γ₁) + length(γ₂)
    - Therefore d_path(x,z) ≤ inf_γ₁ length(γ₁) + inf_γ₂ length(γ₂)
                            = d_path(x,y) + d_path(y,z)

    This is the essential geometric argument for Riemannian geodesic distances. -/
theorem intrinsicDist_triangle (x y z : X) :
    intrinsicDist x z ≤ intrinsicDist x y + intrinsicDist y z := by
  simp only [intrinsicDist]
  calc ⨅ γ : Path x z, pathLength γ
      -- d(x,z) ≤ length(γ₁) + length(γ₂) for any γ₁ : x→y, γ₂ : y→z
      ≤ ⨅ γ₁ : Path x y, ⨅ γ₂ : Path y z, pathLength γ₁ + pathLength γ₂ := by
        apply le_iInf; intro γ₁
        apply le_iInf; intro γ₂
        -- γ₁.trans γ₂ is a path from x to z with the right length
        exact (iInf_le _ (γ₁.trans γ₂)).trans (pathLength_trans γ₁ γ₂).le
    -- iInf over product = sum of iInfs (independence of minimization)
    _ = (⨅ γ₁ : Path x y, pathLength γ₁) + ⨅ γ₂ : Path y z, pathLength γ₂ := by
        simp_rw [ENNReal.iInf_add, ENNReal.add_iInf]

/-!
## Part IV: Application to Concrete Riemannian Manifolds

### Sphere S^(n-1) ⊂ ℝⁿ

The unit sphere in an inner product space has a smooth manifold structure (via
stereographic projection charts). The intrinsic distance on the sphere is the
great-circle arc length, and it satisfies the triangle inequality by our theorem.
-/

/-- On the unit sphere, the path metric satisfies the triangle inequality.
    This is a direct instance of `intrinsicDist_triangle` for the sphere. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (p q r : Metric.sphere (0 : E) 1) :
    intrinsicDist p r ≤ intrinsicDist p q + intrinsicDist q r :=
  intrinsicDist_triangle p q r

/-!
### The Riemannian Connection

For a full Riemannian manifold (M, g), the geodesic distance is:

  d_g(p, q) = inf { ∫₀¹ √(g_{γ(t)}(γ'(t), γ'(t))) dt | γ smooth path from p to q }

This is precisely the `intrinsicDist` for the Riemannian arc length functional.

**What's needed for a complete Riemannian formalization:**
1. Inner product field g on tangent bundles: not in Mathlib v4.26.0
2. Riemannian arc length = ∫₀¹ ‖γ'(t)‖_g dt
3. Equivalence: Riemannian arc length = total variation for smooth γ

Steps 2-3 would instantiate our `pathLength` with the Riemannian length,
making `intrinsicDist_triangle` the exact theorem needed.

**The argument is complete:** the triangle inequality for geodesic distances
follows from path concatenation, regardless of the specific metric tensor.
-/

/-- Summary: geodesic/intrinsic metric satisfies the triangle inequality -/
theorem geodesic_triangle_ineq (p q r : X) :
    intrinsicDist p r ≤ intrinsicDist p q + intrinsicDist q r :=
  intrinsicDist_triangle p q r

end TriangleInequalityOQ04
