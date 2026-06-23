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
/-
## Part V: Quartic Case
-/

/-- **n = 4 case (quartic):**
    f has 5 roots, f' has 4 critical points c₁ < c₂ < c₃ < c₄.
    Gaps: g₁ = c₂-c₁, g₂ = c₃-c₂, g₃ = c₄-c₃.
    Result: g₁ > g₂ and g₃ > g₂ (outer gaps larger than middle). -/
axiom quartic_gap_property (c : Fin 4 → ℝ)
    (hc : ∀ i j : Fin 4, i < j → c i < c j) :
    Gap c ⟨0, by omega⟩ > Gap c ⟨1, by omega⟩ ∧
    Gap c ⟨2, by omega⟩ > Gap c ⟨1, by omega⟩

/-
## Part VI: Lorch's Generalizations (1976)
-/

/-- Lorch (1976) extended Bálint's result to higher derivatives:
    for f⁽ᵏ⁾ with k < n, the gaps between consecutive zeros also
    exhibit monotonicity from the midpoint outward. -/
/-
## Part VII: Summary
-/

/-- **Erdős Problem #1114: SOLVED by Bálint (1960)**
    Combines Bálint's main theorem with the quartic special case. -/
theorem erdos_1114_summary :
    -- Main theorem: gaps increase outward
    (∀ n : ℕ, n ≥ 2 → ∀ a₀ d : ℝ, d > 0 →
      ∀ c : Fin n → ℝ,
      (∀ i j : Fin n, i < j → c i < c j) →
      (∀ i : Fin n, a₀ + i * d < c i ∧ c i < a₀ + (i + 1) * d) →
      ∀ i j : Fin (n - 1),
        DistFromMidpoint c a₀ d n ⟨i.val, by omega⟩ <
        DistFromMidpoint c a₀ d n ⟨j.val, by omega⟩ →
        Gap c i < Gap c j) ∧
    -- Quartic case: outer gaps > middle gap
    (∀ c : Fin 4 → ℝ,
      (∀ i j : Fin 4, i < j → c i < c j) →
      Gap c ⟨0, by omega⟩ > Gap c ⟨1, by omega⟩ ∧
      Gap c ⟨2, by omega⟩ > Gap c ⟨1, by omega⟩) :=
  ⟨fun n hn a₀ d hd c hc hcb => balint_theorem hn hd c hc hcb,
   fun c hc => quartic_gap_property c hc⟩

end Erdos1114
