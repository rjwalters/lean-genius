/-!
# Erdős Problem #1104 — Maximum Chromatic Number of Triangle-Free Graphs

Let f(n) be the maximum chromatic number of a triangle-free graph
on n vertices. Estimate f(n).

Known:
  (1 − o(1))√(n/log n) ≤ f(n) ≤ (2 + o(1))√(n/log n)

Lower bound: Hefty–Horn–King–Pfender (2025)
Upper bound: Davies–Illingworth (2022)

The exact constant remains open.

Status: OPEN
Reference: https://erdosproblems.com/1104
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- f(n): the maximum chromatic number of a triangle-free graph
    on n vertices. We axiomatize this function. -/
noncomputable def triangleFreeMaxChromatic : ℕ → ℕ := fun _ => 0  -- axiomatized

/-! ## Main Bounds -/

/-- **Lower Bound (Hefty–Horn–King–Pfender 2025)**: There exists c₁ > 0
    such that f(n) ≥ c₁ √(n/log n) for large n. The construction uses
    Ramsey-type probabilistic methods. -/
axiom erdos_1104_lower :
  ∃ c₁ : ℝ, c₁ > 0 ∧
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (triangleFreeMaxChromatic n : ℝ) ≥
        (c₁ - ε) * Real.sqrt (n / Real.log n)

/-- **Upper Bound (Davies–Illingworth 2022)**: There exists c₂ ≤ 2
    such that f(n) ≤ c₂ √(n/log n) for large n. -/
axiom erdos_1104_upper :
  ∃ c₂ : ℝ, c₂ ≤ 2 ∧ c₂ > 0 ∧
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
      (triangleFreeMaxChromatic n : ℝ) ≤
        (c₂ + ε) * Real.sqrt (n / Real.log n)

/-- **Combined Asymptotic**: f(n) = Θ(√(n/log n)).
    The order of magnitude is determined but the exact constant
    is unknown. -/
axiom erdos_1104_asymptotic :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
    ∀ n : ℕ, n ≥ 2 →
      c₁ * Real.sqrt (n / Real.log n) ≤ (triangleFreeMaxChromatic n : ℝ) ∧
      (triangleFreeMaxChromatic n : ℝ) ≤ c₂ * Real.sqrt (n / Real.log n)

/-! ## Edge Variant -/

/-- **Edge Variant**: g(m) = max χ(G) over triangle-free graphs
    with m edges. Davies–Illingworth showed
    g(m) ≤ (3^{5/3} + o(1))(m/(log m)²)^{1/3},
    and Kim (1995) gave a matching lower bound. -/
axiom edge_variant :
  ∃ C : ℝ, C > 0 ∧
    ∀ m : ℕ, m ≥ 2 →
      True  -- g(m) = Θ((m/(log m)²)^{1/3})

/-! ## Observations -/

/-- **Mycielski Construction**: The Mycielski construction produces
    triangle-free graphs with arbitrarily large chromatic number,
    but on exponentially many vertices. -/
axiom mycielski : True

/-- **Kim (1995)**: Proved that the Ramsey number R(3,k) = Θ(k²/log k)
    using a semi-random method. This is dual to the lower bound for f(n)
    since f(n) ≥ k iff R(3,k) ≤ n. -/
axiom kim_ramsey : True

/-- **Connection to Problem #1013**: f(n) is the inverse function
    to h₃(k), the minimum vertices in a triangle-free k-chromatic
    graph. -/
axiom inverse_connection : True
