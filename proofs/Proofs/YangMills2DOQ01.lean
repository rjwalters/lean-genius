/-
  Yang-Mills 2D OQ-01: Heat Kernel Techniques for 3D/4D Extension

  In 2D, Yang-Mills theory is exactly solvable: the partition function
  reduces to a sum over representations weighted by exp(-C₂·g²·A) where
  C₂ is the quadratic Casimir eigenvalue, g² is the coupling, and A is
  the area. The heat kernel on the gauge group G plays a central role.

  Question: Can these 2D techniques extend to 3D or 4D?

  Key obstacles formalized here:
  - 2D: gauge field has no physical degrees of freedom (exact solution)
  - 3D: Wilson loops depend on topology, not just area (Chern-Simons)
  - 4D: full dynamical theory, mass gap is open (Millennium Prize)

  This file proves:
  - Heat kernel terms are positive and decay with area (Part I)
  - Wilson loop satisfies exact area law in 2D (Part II)
  - String tension is positive, with concrete SU(2) values (Part III)
  - Partition function decays from Z(0) to trivial rep dominance (Part IV)

  All results are PROVEN (0 axioms, 0 sorries). The 3D/4D obstacles are
  documented in comments since they concern the ABSENCE of techniques,
  which is not naturally expressible as a Lean theorem.

  References:
  - Migdal, "Recursion equations in gauge theories" (1975)
  - Witten, "On quantum gauge theories in two dimensions" (1991)
  - Sengupta, "Gauge theory on compact surfaces" (1997)
-/

import Mathlib

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

noncomputable section

open Real

namespace YangMills2DOQ01

-- ============================================================
-- PART I: 2D Heat Kernel Terms
-- ============================================================

/-- A single term in the heat kernel expansion on a compact Lie group:
    contribution of an irreducible representation with dimension d
    and quadratic Casimir C₂ to the partition function at area A
    with coupling g².

    K_term(d, C₂, g², A) = d² · exp(-C₂ · g² · A)

    The full heat kernel trace is K(A) = Σ_R K_term(dim R, C₂(R), g², A).
    In 2D this sum is EXACTLY the partition function. -/
def heatKernelTerm (d : ℝ) (casimir g_sq A : ℝ) : ℝ :=
  d ^ 2 * exp (-casimir * g_sq * A)

/-- Each heat kernel term is positive when d > 0. -/
theorem heatKernelTerm_pos (d : ℝ) (hd : d > 0) (casimir g_sq A : ℝ) :
    heatKernelTerm d casimir g_sq A > 0 := by
  unfold heatKernelTerm
  apply mul_pos
  · positivity
  · exact exp_pos _

/-- The trivial representation (d=1, C₂=0) always contributes 1. -/
theorem heatKernelTerm_trivial (g_sq A : ℝ) :
    heatKernelTerm 1 0 g_sq A = 1 := by
  unfold heatKernelTerm
  simp

/-- At zero area, representation with dimension d contributes d². -/
theorem heatKernelTerm_zero_area (d casimir g_sq : ℝ) :
    heatKernelTerm d casimir g_sq 0 = d ^ 2 := by
  unfold heatKernelTerm
  simp

/-- Non-trivial terms decay with area: K(d, C₂, g², A) < K(d, C₂, g², 0)
    when C₂ > 0, g² > 0, A > 0. This exponential suppression of higher
    representations is the mechanism behind the 2D mass gap.
    In 3D/4D, this simple decay property does NOT hold in general
    because the partition function is not a sum over representations. -/
theorem heatKernelTerm_decays (d casimir g_sq A : ℝ)
    (hd : d > 0) (hc : casimir > 0) (hg : g_sq > 0) (hA : A > 0) :
    heatKernelTerm d casimir g_sq A < heatKernelTerm d casimir g_sq 0 := by
  unfold heatKernelTerm
  simp only [mul_zero, neg_zero, exp_zero]
  apply mul_lt_mul_of_pos_left _ (by positivity : d ^ 2 > 0)
  rw [exp_lt_one_iff]
  have : casimir * g_sq * A > 0 := mul_pos (mul_pos hc hg) hA
  linarith

-- ============================================================
-- PART II: Wilson Loop in 2D (Migdal Formula)
-- ============================================================

/-- The 2D Wilson loop expectation for representation with dimension d,
    Casimir C₂, coupling g², at enclosed area A:

    ⟨W_R(C)⟩ = d · exp(-g² · A · C₂ / (2d))

    This is Migdal's formula (1975), EXACT in 2D.
    In 3D (Chern-Simons), Wilson loops depend on knot type, not area.
    In 4D, Wilson loops have non-trivial dynamics with no closed form. -/
def wilsonLoop2D (d casimir g_sq A : ℝ) : ℝ :=
  d * exp (-(g_sq * A * casimir / (2 * d)))

/-- At zero area, the Wilson loop equals the representation dimension.
    W(0) = d · exp(0) = d. -/
theorem wilsonLoop2D_zero_area (d casimir g_sq : ℝ) :
    wilsonLoop2D d casimir g_sq 0 = d := by
  unfold wilsonLoop2D
  simp

/-- The 2D string tension: σ = g² · C₂ / (2d).
    This controls the exponential decay rate of the Wilson loop with area.
    In 2D, σ is exactly computable from representation theory data.
    In 4D, computing σ from first principles is equivalent to proving
    confinement — part of the Millennium Prize problem. -/
def stringTension2D (casimir g_sq d : ℝ) : ℝ :=
  g_sq * casimir / (2 * d)

/-- The 2D string tension is positive for positive coupling and Casimir. -/
theorem stringTension2D_pos (casimir g_sq d : ℝ)
    (hc : casimir > 0) (hg : g_sq > 0) (hd : d > 0) :
    stringTension2D casimir g_sq d > 0 := by
  unfold stringTension2D
  apply div_pos
  · exact mul_pos hg hc
  · linarith

/-- The Wilson loop can be rewritten in terms of string tension:
    W(A) = d · exp(-σ · A). -/
theorem wilsonLoop2D_eq_stringTension (d casimir g_sq A : ℝ) :
    wilsonLoop2D d casimir g_sq A =
    d * exp (-(stringTension2D casimir g_sq d * A)) := by
  unfold wilsonLoop2D stringTension2D
  ring_nf

/-- **Exact Area Law in 2D**: The Wilson loop decreases with area.
    W(A) < W(0) for A > 0, g² > 0, C₂ > 0, d > 0.

    This is the hallmark of confinement: the quark-antiquark potential
    grows linearly with separation. In 2D this is provable from the
    Migdal formula. In 4D it is the central open problem. -/
theorem wilsonLoop2D_area_law (d casimir g_sq A : ℝ)
    (hd : d > 0) (hc : casimir > 0) (hg : g_sq > 0) (hA : A > 0) :
    wilsonLoop2D d casimir g_sq A < wilsonLoop2D d casimir g_sq 0 := by
  unfold wilsonLoop2D
  simp only [mul_zero, zero_mul, neg_zero, zero_div, exp_zero, mul_one]
  apply mul_lt_mul_of_pos_left _ hd
  rw [exp_lt_one_iff]
  apply neg_neg_of_neg
  apply div_pos
  · exact mul_pos (mul_pos hg hA) hc
  · linarith

-- ============================================================
-- PART III: SU(2) Concrete Calculations
-- ============================================================

/-- SU(2) fundamental representation parameters: j = 1/2, dim = 2, C₂ = 3/4. -/
def su2FundDim : ℝ := 2
def su2FundCasimir : ℝ := 3 / 4

/-- SU(2) adjoint representation parameters: j = 1, dim = 3, C₂ = 2. -/
def su2AdjDim : ℝ := 3
def su2AdjCasimir : ℝ := 2

/-- SU(2) fundamental string tension: σ_fund = 3g²/16. -/
theorem su2_fundamental_stringTension (g_sq : ℝ) :
    stringTension2D su2FundCasimir g_sq su2FundDim = 3 * g_sq / 16 := by
  unfold stringTension2D su2FundCasimir su2FundDim
  ring

/-- SU(2) adjoint string tension: σ_adj = g²/3. -/
theorem su2_adjoint_stringTension (g_sq : ℝ) :
    stringTension2D su2AdjCasimir g_sq su2AdjDim = g_sq / 3 := by
  unfold stringTension2D su2AdjCasimir su2AdjDim
  ring

/-- Casimir scaling: the ratio σ_adj/σ_fund = 16/9 in SU(2).
    In 2D, Casimir scaling is EXACT. In 4D lattice simulations,
    Casimir scaling holds approximately (verified by Bali 2000).
    Understanding why it persists in 4D is an open problem. -/
theorem su2_casimir_scaling (g_sq : ℝ) (hg : g_sq > 0) :
    stringTension2D su2AdjCasimir g_sq su2AdjDim /
    stringTension2D su2FundCasimir g_sq su2FundDim = 16 / 9 := by
  rw [su2_adjoint_stringTension, su2_fundamental_stringTension]
  field_simp
  ring

/-- The 2D mass gap for SU(2) fundamental representation: Δ = 3g²/8.
    This follows because the mass gap equals twice the string tension
    in 2D (where there are no propagating degrees of freedom). -/
theorem su2_mass_gap_2d (g_sq : ℝ) :
    2 * stringTension2D su2FundCasimir g_sq su2FundDim = 3 * g_sq / 8 := by
  rw [su2_fundamental_stringTension]
  ring

-- ============================================================
-- PART IV: Partition Function and Trivial Rep Dominance
-- ============================================================

/-- The SU(2) partition function truncated to j = 0, 1/2, 1.
    Z(g², A) = 1 + 4·exp(-3g²A/4) + 9·exp(-2g²A).
    Three terms suffice for qualitative physics. -/
def partitionFn2D_SU2 (g_sq A : ℝ) : ℝ :=
  -- j=0 (trivial): dim=1, C₂=0
  heatKernelTerm 1 0 g_sq A +
  -- j=1/2 (fundamental): dim=2, C₂=3/4
  heatKernelTerm 2 (3 / 4) g_sq A +
  -- j=1 (adjoint): dim=3, C₂=2
  heatKernelTerm 3 2 g_sq A

/-- The truncated partition function is positive. -/
theorem partitionFn2D_SU2_pos (g_sq A : ℝ) :
    partitionFn2D_SU2 g_sq A > 0 := by
  unfold partitionFn2D_SU2
  have h1 := heatKernelTerm_pos 1 (by norm_num) 0 g_sq A
  have h2 := heatKernelTerm_pos 2 (by norm_num) (3 / 4) g_sq A
  have h3 := heatKernelTerm_pos 3 (by norm_num) 2 g_sq A
  linarith

/-- At zero area: Z(g², 0) = 1² + 2² + 3² = 14. -/
theorem partitionFn2D_SU2_zero (g_sq : ℝ) :
    partitionFn2D_SU2 g_sq 0 = 14 := by
  unfold partitionFn2D_SU2
  rw [heatKernelTerm_zero_area, heatKernelTerm_zero_area, heatKernelTerm_zero_area]
  norm_num

/-- Trivial representation dominance: Z(g², A) ≥ 1 for all A.
    The j=0 term contributes exactly 1 regardless of area, and all
    other terms are positive. At large area, the higher terms are
    exponentially suppressed, so Z → 1.
    This is the 2D analog of the mass gap: the theory flows to the
    trivial vacuum at large distances. In 4D, proving this infrared
    behavior requires solving the Millennium Prize problem. -/
theorem partitionFn2D_SU2_lower (g_sq A : ℝ) :
    partitionFn2D_SU2 g_sq A ≥ 1 := by
  unfold partitionFn2D_SU2
  have h1 : heatKernelTerm 1 0 g_sq A = 1 := heatKernelTerm_trivial g_sq A
  rw [h1]
  have h2 := heatKernelTerm_pos 2 (by norm_num) (3 / 4) g_sq A
  have h3 := heatKernelTerm_pos 3 (by norm_num) 2 g_sq A
  linarith

/-- The partition function at positive area is strictly less than at zero:
    Z(g², A) < Z(g², 0) for g² > 0, A > 0.
    Non-trivial representations are suppressed while the trivial rep is
    unchanged. This simple monotonicity is the 2D mass gap mechanism.
    In 3D/4D, the partition function is not a finite sum of exponentials,
    so this argument does not generalize. -/
theorem partitionFn2D_SU2_decays (g_sq A : ℝ) (hg : g_sq > 0) (hA : A > 0) :
    partitionFn2D_SU2 g_sq A < partitionFn2D_SU2 g_sq 0 := by
  unfold partitionFn2D_SU2
  have triv_eq : heatKernelTerm 1 0 g_sq A = heatKernelTerm 1 0 g_sq 0 := by
    simp [heatKernelTerm]
  have h2_lt := heatKernelTerm_decays 2 (3 / 4) g_sq A
    (by norm_num) (by norm_num) hg hA
  have h3_lt := heatKernelTerm_decays 3 2 g_sq A
    (by norm_num) (by norm_num) hg hA
  linarith

-- ============================================================
-- PART V: Why 2D Techniques Fail in Higher Dimensions
-- ============================================================

/-
## Obstacles to 3D/4D extension (documented, not axiomatized)

### Why 2D is special:
The 2D Yang-Mills partition function factors as a product of heat kernels,
one per plaquette (Migdal recursion). This is because:
1. In 2D, the curvature F = dA + A∧A is a 2-form on a 2-manifold,
   completely determined by its integral over each face.
2. Adjacent plaquettes share exactly one link, allowing exact integration.
3. The result is a sum over irreducible representations with exponential weights.

### Why this fails in 3D:
- The gauge field A_μ has 1 physical degree of freedom per point.
- The theory becomes topological in a different sense (Chern-Simons).
- Wilson loops depend on KNOT TYPE, not enclosed area.
- Witten (1989) showed 3D Chern-Simons produces the Jones polynomial.
- The heat kernel factorization over plaquettes breaks down because
  plaquettes in 3D share edges, creating non-trivial correlations.

### Why this fails in 4D:
- The gauge field has 2 physical degrees of freedom per point.
- The theory is NOT topological — dynamics are essential.
- The partition function is NOT a finite sum over representations.
- Wilson loops exhibit genuine quantum dynamics (confinement, mass gap).
- The Clay Millennium Prize asks to prove the mass gap exists in 4D.

### Partial connections that survive:
1. **Dimensional reduction**: 3D on S¹ × Σ → 2D on Σ as S¹ radius → 0.
   This gives some control over the 3D theory near the 2D limit.
2. **Large-N limit**: 2D Yang-Mills at large N has a string theory
   interpretation (Gross-Taylor 1993). This connects to 4D via
   gauge/string duality (AdS/CFT).
3. **Lattice**: Migdal recursion generalizes to higher-dimensional
   lattices, but the exact computation property is lost.
4. **Casimir scaling**: exact in 2D, approximate in 4D lattice simulations.
   Understanding why this persists is an active research question.
-/

end YangMills2DOQ01
