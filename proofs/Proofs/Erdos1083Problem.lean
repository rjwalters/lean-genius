/-
Erdős Problem #1083: Distinct Distances in Higher Dimensions

Source: https://erdosproblems.com/1083
Status: OPEN

Statement:
Let d ≥ 3, and let f_d(n) be the minimal number of distinct distances determined
by any set of n points in ℝ^d. Estimate f_d(n) - in particular, is
f_d(n) = n^{2/d - o(1)}?

Known bounds:
- Erdős (1946): n^{1/d} ≪ f_d(n) ≪ n^{2/d}
- Solymosi-Vu: f_d(n) ≫ n^{2/d - c/d²} for d ≥ 4

References:
- Erdős (1946): Initial bounds
- Solymosi, Vu: Improved lower bounds for d ≥ 4
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos1083

/-
## Part I: Definitions
-/

/--
f_d(n): the minimum number of distinct distances determined by n points in ℝ^d.
Axiomatized as an extremal quantity over point configurations.
-/
axiom f (d n : ℕ) : ℕ

/-
## Part II: Erdős's Bounds
-/

/--
**Erdős (1946)**: n^{1/d} ≪ f_d(n) ≪ n^{2/d}.

The upper bound is achieved by a grid configuration.
The lower bound uses a pigeonhole argument.
-/
axiom erdos_bounds (d : ℕ) (hd : d ≥ 3) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      c₁ * (n : ℝ) ^ (1 / (d : ℝ)) ≤ (f d n : ℝ) ∧
      (f d n : ℝ) ≤ c₂ * (n : ℝ) ^ (2 / (d : ℝ))

/-
## Part III: Solymosi-Vu Improvement
-/

/--
**Solymosi-Vu**: For d ≥ 4, f_d(n) ≫ n^{2/d - c/d²} for some constant c > 0.

This improves the lower bound from n^{1/d} toward the conjectured n^{2/d}.
-/
/-
## Part IV: The Conjecture
-/

/--
**Erdős's Conjecture (OPEN)**: f_d(n) = n^{2/d - o(1)}.

The conjectured lower bound matches the grid upper bound up to
subpolynomial factors.
-/
/-
## Part V: Main Theorem
-/

/--
**Erdős Problem #1083: OPEN**

Known: n^{1/d} ≪ f_d(n) ≪ n^{2/d}.
Conjecture: f_d(n) = n^{2/d - o(1)}.
-/
theorem erdos_1083 (d : ℕ) (hd : d ≥ 3) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      c₁ * (n : ℝ) ^ (1 / (d : ℝ)) ≤ (f d n : ℝ) ∧
      (f d n : ℝ) ≤ c₂ * (n : ℝ) ^ (2 / (d : ℝ)) :=
  erdos_bounds d hd

end Erdos1083
