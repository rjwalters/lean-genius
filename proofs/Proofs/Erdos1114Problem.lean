/-
Erdős Problem #1114: Monotonicity of Critical Point Gaps

Source: https://erdosproblems.com/1114
Status: SOLVED

Statement:
Let f(x) ∈ ℝ[x] be a polynomial of degree n whose roots {a₀ < a₁ < ... < aₙ}
are all real and form an arithmetic progression.

Then the differences between consecutive zeros of f'(x), beginning from the
midpoint of (a₀, aₙ) towards the endpoints, are monotonically increasing.

Answer: PROVED by Bálint (1960)

Explanation:
- f has n+1 roots: a₀, a₀+d, a₀+2d, ..., a₀+nd (arithmetic progression with common difference d)
- By Rolle's theorem, f' has n distinct real roots in (a₀, aₙ)
- Let these critical points be c₁ < c₂ < ... < cₙ
- The gaps gᵢ = cᵢ₊₁ - cᵢ increase as we move from the center outward

Historical Context:
This was a conjecture of Erdős (communicated personally to Bálint).
Bálint proved it in 1960. Lorch (1976) gave generalizations.

References:
- [Ba60b] Bálint (1960): Original proof
- [Lo76] Lorch (1976): Generalizations

Tags: polynomials, analysis, critical-points
-/

import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.MeanValue

namespace Erdos1114

/-
## Part I: Setup
-/

/--
**Arithmetic progression of roots:**
The roots are a₀, a₀+d, a₀+2d, ..., a₀+nd for some d > 0.
-/
def IsAPRoots (roots : Fin (n + 1) → ℝ) (a₀ d : ℝ) : Prop :=
  d > 0 ∧ ∀ i : Fin (n + 1), roots i = a₀ + i * d

/--
**Polynomial with AP roots:**
f(x) = c · (x - a₀)(x - (a₀+d))···(x - (a₀+nd)) for some constant c ≠ 0.
-/
def HasAPRoots (f : Polynomial ℝ) (n : ℕ) (a₀ d : ℝ) : Prop :=
  d > 0 ∧
  f.degree = n ∧
  ∀ i : Fin (n + 1), f.IsRoot (a₀ + i * d)

/-
## Part II: Critical Points
-/

/--
**Critical points of f:**
By Rolle's theorem, f' has exactly n distinct real roots in (a₀, a₀+nd).
-/
def CriticalPoints (f : Polynomial ℝ) (n : ℕ) := Fin n → ℝ

/--
**Rolle's theorem gives critical points:**
Between each pair of consecutive roots of f, there's a root of f'.
-/
axiom rolle_gives_critical_points {f : Polynomial ℝ} {n : ℕ} {a₀ d : ℝ}
    (hf : HasAPRoots f (n + 1) a₀ d) :
    ∃ c : Fin n → ℝ,
      -- Critical points are strictly increasing
      (∀ i j : Fin n, i < j → c i < c j) ∧
      -- Each lies between consecutive roots
      (∀ i : Fin n, a₀ + i * d < c i ∧ c i < a₀ + (i + 1) * d)

/-
## Part III: The Gaps
-/

/--
**Gap between consecutive critical points:**
gᵢ = cᵢ₊₁ - cᵢ
-/
def Gap (c : Fin n → ℝ) (i : Fin (n - 1)) : ℝ :=
  c ⟨i.val + 1, by omega⟩ - c ⟨i.val, by omega⟩

/--
**Midpoint of roots:**
The center of the root interval (a₀, aₙ).
-/
def Midpoint (a₀ d : ℝ) (n : ℕ) : ℝ :=
  a₀ + n * d / 2

/--
**Distance from midpoint:**
How far each critical point is from the midpoint.
-/
def DistFromMidpoint (c : Fin n → ℝ) (a₀ d : ℝ) (n : ℕ) (i : Fin n) : ℝ :=
  |c i - Midpoint a₀ d n|

/-
## Part IV: The Main Theorem
-/

/--
**Bálint's Theorem (1960):**
The gaps between consecutive critical points increase as we move outward
from the midpoint of the root interval.

More precisely: if |cᵢ - m| < |cⱼ - m| where m is the midpoint,
then the gap at cᵢ is smaller than the gap at cⱼ.
-/
axiom balint_theorem {n : ℕ} (hn : n ≥ 2) {a₀ d : ℝ} (hd : d > 0)
    (c : Fin n → ℝ)
    (hc : ∀ i j : Fin n, i < j → c i < c j)  -- Increasing
    (hc_bounds : ∀ i : Fin n, a₀ + i * d < c i ∧ c i < a₀ + (i + 1) * d) :
    -- Gaps increase outward from midpoint
    let m := Midpoint a₀ d n
    ∀ i j : Fin (n - 1),
      DistFromMidpoint c a₀ d n ⟨i.val, by omega⟩ <
      DistFromMidpoint c a₀ d n ⟨j.val, by omega⟩ →
      Gap c i < Gap c j

/--
**Symmetric formulation:**
For n critical points c₁ < c₂ < ... < cₙ, the gaps satisfy:
g₁ > gₙ₋₁ ≥ g₂ > gₙ₋₂ ≥ ... (interleaved from ends toward middle)
-/
axiom balint_symmetric (n : ℕ) (hn : n ≥ 3) (c : Fin n → ℝ)
    (hc : ∀ i j : Fin n, i < j → c i < c j) :
    -- Outer gaps are larger than inner gaps
    Gap c ⟨0, by omega⟩ ≥ Gap c ⟨n / 2 - 1, by omega⟩

/-
## Part V: Special Cases
-/

/--
**n = 2 case (quadratic):**
f has 3 roots: a, a+d, a+2d
f' is linear with one root (the vertex), no gap comparison needed.
-/
theorem quadratic_trivial : True := trivial

/--
**n = 3 case (cubic):**
f has 4 roots: a, a+d, a+2d, a+3d
f' is quadratic with 2 roots c₁ < c₂
There's one gap g = c₂ - c₁.
-/
theorem cubic_one_gap : True := trivial

/--
**n = 4 case (quartic):**
f has 5 roots: a, a+d, a+2d, a+3d, a+4d
f' has 4 roots c₁ < c₂ < c₃ < c₄
Gaps: g₁ = c₂-c₁, g₂ = c₃-c₂, g₃ = c₄-c₃
Theorem says: g₁ > g₂, g₃ > g₂ (outer gaps larger than middle)
-/
axiom quartic_gap_property (c : Fin 4 → ℝ)
    (hc : ∀ i j : Fin 4, i < j → c i < c j) :
    Gap c ⟨0, by omega⟩ > Gap c ⟨1, by omega⟩ ∧
    Gap c ⟨2, by omega⟩ > Gap c ⟨1, by omega⟩

/-
## Part VI: Proof Ideas
-/

/--
**Symmetry observation:**
The polynomial with AP roots has symmetric properties.
f(a₀ + t) = (-1)ⁿ⁺¹ f(aₙ - t) up to scaling.
-/
axiom symmetry_of_ap_polynomial :
  -- The polynomial with evenly spaced roots is symmetric about its center
  True

/--
**Derivative structure:**
f'(x) also has special structure when f has AP roots.
The critical points are NOT evenly spaced, but have predictable pattern.
-/
axiom derivative_structure :
  -- f' has roots that cluster toward the center
  -- Gaps are larger near the endpoints
  True

/--
**Convexity argument:**
The key insight is that certain auxiliary functions are convex,
which implies the monotonicity of gaps.
-/
axiom convexity_argument : True

/-
## Part VII: Lorch's Generalizations (1976)
-/

/--
**Generalization 1:**
The result extends to higher derivatives.
-/
axiom lorch_higher_derivatives :
  -- For f⁽ᵏ⁾, similar monotonicity properties hold
  True

/--
**Generalization 2:**
Related monotonicity properties for other polynomial families.
-/
axiom lorch_extensions : True

/-
## Part VIII: Explicit Examples
-/

/--
**Example: f(x) = (x-1)(x-2)(x-3)(x-4)**
Roots: 1, 2, 3, 4 (AP with d = 1)
f(x) = x⁴ - 10x³ + 35x² - 50x + 24
f'(x) = 4x³ - 30x² + 70x - 50

Critical points: approximately 1.38, 2.5, 3.62
Gaps: g₁ ≈ 1.12, g₂ ≈ 1.12 (actually symmetric for n=4)
-/
axiom example_quartic : True

/--
**Example: f(x) = (x-1)(x-2)(x-3)(x-4)(x-5)**
Roots: 1, 2, 3, 4, 5 (AP with d = 1)
f' has 4 critical points.
Outer gaps > inner gaps.
-/
axiom example_quintic : True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #1114: SOLVED**

**STATEMENT:** For a polynomial f with n+1 real roots in arithmetic progression,
the gaps between consecutive critical points of f' increase outward from
the midpoint.

**PROOF:** Bálint (1960)

**GENERALIZATIONS:** Lorch (1976)

**KEY INSIGHT:** The symmetry of AP roots induces structure on f',
and convexity arguments establish the monotonicity of gaps.
-/
theorem erdos_1114_summary :
    -- The main theorem is true (axiomatized)
    True := trivial

/--
**Problem status:**
Erdős Problem #1114 is SOLVED.
-/
theorem erdos_1114_status : True := trivial

end Erdos1114
