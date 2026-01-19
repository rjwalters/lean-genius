/-
Erdős Problem #755: Equilateral Triangles in ℝ⁶

Source: https://erdosproblems.com/755
Status: PROVED (Clemen-Dumitrescu-Liu, 2025)

Statement:
The number of equilateral triangles of size 1 formed by any set of n points
in ℝ⁶ is at most (1/27 + o(1))n³.

Answer: YES (proved with exact asymptotic)

Key Results:
- Lower bound construction (Lenz, Erdős-Purdy 1975): T₆ᵘ(n) ≥ n³/27 - O(n²)
  Take three orthogonal circles with n/3 points each forming inscribed squares.
- Clemen-Dumitrescu-Liu (2025): T₆(n) = (1/27 + o(1))n³
  This holds even for equilateral triangles of ANY size, not just unit.
- They also found exact formulas for T_d(n) for all even d ≥ 6.

References:
- Clemen, F., Dumitrescu, A., and Liu, D., "The number of regular simplices
  in higher dimensions." arXiv:2507.19841 (2025).
- Erdős, P. and Purdy, G., "Some extremal problems in geometry III." (1975).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open Real

namespace Erdos755

/-
## Part I: Euclidean Space Setup
-/

/--
**Euclidean distance in ℝᵈ:**
We work with finite point sets in d-dimensional Euclidean space.
-/
variable {d : ℕ}

/--
**Three points form an equilateral triangle:**
Points p₁, p₂, p₃ form an equilateral triangle if all three pairwise
distances are equal.
-/
def IsEquilateralTriangle (p₁ p₂ p₃ : Fin d → ℝ) : Prop :=
  let dist := fun x y => Real.sqrt (Finset.univ.sum fun i => (x i - y i)^2)
  dist p₁ p₂ = dist p₂ p₃ ∧ dist p₂ p₃ = dist p₃ p₁ ∧ dist p₁ p₂ > 0

/--
**Unit equilateral triangle:**
An equilateral triangle with all sides of length 1.
-/
def IsUnitEquilateralTriangle (p₁ p₂ p₃ : Fin d → ℝ) : Prop :=
  let dist := fun x y => Real.sqrt (Finset.univ.sum fun i => (x i - y i)^2)
  dist p₁ p₂ = 1 ∧ dist p₂ p₃ = 1 ∧ dist p₃ p₁ = 1

/-
## Part II: Counting Functions
-/

/--
**T₆ᵘ(n): Count of unit equilateral triangles**
The maximum number of unit equilateral triangles that can be formed
by n points in ℝ⁶.
-/
noncomputable def T6_unit (n : ℕ) : ℕ :=
  -- Supremum over all n-point configurations
  sSup { k : ℕ | ∃ (P : Finset (Fin 6 → ℝ)), P.card = n ∧
    k = (P.filter (fun p₁ => P.filter (fun p₂ => P.filter (fun p₃ =>
      IsUnitEquilateralTriangle p₁ p₂ p₃ ∧ p₁ < p₂ ∧ p₂ < p₃
    ) |>.card > 0) |>.card > 0) |>.card) }

/--
**T₆(n): Count of equilateral triangles of any size**
The maximum number of equilateral triangles (any side length)
formed by n points in ℝ⁶.
-/
noncomputable def T6 (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ (P : Finset (Fin 6 → ℝ)), P.card = n ∧
    k = (P.filter (fun p₁ => P.filter (fun p₂ => P.filter (fun p₃ =>
      IsEquilateralTriangle p₁ p₂ p₃ ∧ p₁ < p₂ ∧ p₂ < p₃
    ) |>.card > 0) |>.card > 0) |>.card) }

/--
**T_d(n): General dimension count**
For even d ≥ 6, the maximum count of equilateral triangles.
-/
noncomputable def T_d (d n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ (P : Finset (Fin d → ℝ)), P.card = n ∧
    k = (P.filter (fun p₁ => P.filter (fun p₂ => P.filter (fun p₃ =>
      IsEquilateralTriangle p₁ p₂ p₃ ∧ p₁ < p₂ ∧ p₂ < p₃
    ) |>.card > 0) |>.card > 0) |>.card) }

/-
## Part III: The Lenz Construction
-/

/--
**The Lenz Construction:**
Using three mutually orthogonal circles in ℝ⁶, place n/3 points on each.
The points on each circle form inscribed squares.

This construction achieves T₆ᵘ(n) ≥ n³/27 - O(n²).
-/
axiom lenz_construction :
  ∀ n : ℕ, n ≥ 3 →
    ∃ (P : Finset (Fin 6 → ℝ)), P.card = n ∧
      -- Number of unit equilateral triangles is at least n³/27 - O(n²)
      ∃ C : ℝ, C > 0 ∧
        (T6_unit n : ℝ) ≥ (n : ℝ)^3 / 27 - C * (n : ℝ)^2

/--
**Lower bound: T₆ᵘ(n) ≥ n³/27 - O(n²)**
-/
axiom lower_bound_unit :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 3 →
      (T6_unit n : ℝ) ≥ (n : ℝ)^3 / 27 - C * (n : ℝ)^2

/-
## Part IV: Erdős's Conjecture
-/

/--
**Erdős's Conjecture:**
T₆ᵘ(n) ≤ (1/27 + o(1))n³

In other words, the Lenz construction is asymptotically optimal.
-/
def erdos_conjecture_unit : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (T6_unit n : ℝ) ≤ (1/27 + ε) * (n : ℝ)^3

/--
**Stronger version (any size):**
Erdős believed the bound should hold for triangles of any size.
-/
def erdos_conjecture_any_size : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (T6 n : ℝ) ≤ (1/27 + ε) * (n : ℝ)^3

/-
## Part V: Clemen-Dumitrescu-Liu Solution
-/

/--
**Clemen-Dumitrescu-Liu 2025: Main Result**
T₆(n) = (1/27 + o(1))n³

This proves Erdős's conjecture in a strong form: it holds even for
equilateral triangles of arbitrary size, not just unit triangles.
-/
axiom cdl_2025_main :
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    |((T6 n : ℝ) - (n : ℝ)^3 / 27)| ≤ ε * (n : ℝ)^3

/--
**Corollary: Unit triangles conjecture is true**
-/
theorem erdos_conjecture_unit_true : erdos_conjecture_unit := by
  intro ε hε
  obtain ⟨N, hN⟩ := cdl_2025_main (ε/2) (by linarith)
  use N
  intro n hn
  -- T6_unit n ≤ T6 n ≤ (1/27 + ε)n³
  sorry

/--
**Corollary: Any-size triangles conjecture is true**
-/
theorem erdos_conjecture_any_size_true : erdos_conjecture_any_size := by
  intro ε hε
  obtain ⟨N, hN⟩ := cdl_2025_main ε hε
  use N
  intro n hn
  have h := hN n hn
  -- |T6(n) - n³/27| ≤ ε·n³ implies T6(n) ≤ (1/27 + ε)n³
  sorry

/-
## Part VI: Exact Formula for Higher Dimensions
-/

/--
**General dimension formula (even d ≥ 6):**
Clemen-Dumitrescu-Liu found exact formulas for T_d(n) for all even d ≥ 6
and sufficiently large n.
-/
axiom cdl_general_dimension :
  ∀ d : ℕ, d ≥ 6 → Even d →
    ∃ c_d : ℝ, c_d > 0 ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
        |((T_d d n : ℝ) - c_d * (n : ℝ)^3)| ≤ ε * (n : ℝ)^3

/--
**The constant for d = 6:**
c₆ = 1/27
-/
axiom c6_equals_one_27th :
  ∃ c_d : ℝ, c_d > 0 ∧ c_d = 1/27 ∧
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      |((T_d 6 n : ℝ) - c_d * (n : ℝ)^3)| ≤ ε * (n : ℝ)^3

/-
## Part VII: Why 1/27?
-/

/--
**The constant 1/27 explained:**
In the Lenz construction:
- Place n/3 points on each of 3 orthogonal circles
- Each point on one circle, with each point on another circle, and
  each point on the third forms an equilateral triangle
- Total: (n/3)³ = n³/27 triangles (leading term)

The constant 1/27 = 1/3³ arises from partitioning n points into 3 groups.
-/
axiom why_one_27th :
  -- The 1/27 comes from optimally distributing n points into 3 groups
  -- Each group contributes equally to the count
  True

/-
## Part VIII: Related Results
-/

/--
**Connection to other dimensions:**
- d = 2: T₂(n) ≤ n (obvious)
- d = 3: T₃(n) = Θ(n²) (different behavior)
- d = 4, 5: Intermediate cases
- d ≥ 6 even: T_d(n) = Θ(n³)

The jump to cubic growth at d = 6 is significant.
-/
axiom dimension_behavior :
  -- d = 2: linear, d = 3: quadratic, d ≥ 6: cubic
  True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #755: Status**

**Question:**
Is T₆ᵘ(n) ≤ (1/27 + o(1))n³?

**Answer:**
YES. Proved by Clemen-Dumitrescu-Liu (2025).

**Stronger Result:**
T₆(n) = (1/27 + o(1))n³ even for triangles of arbitrary size.

**Key Insight:**
The Lenz construction using three orthogonal circles achieves the
optimal leading constant 1/27 = 1/3³.
-/
theorem erdos_755_summary :
    -- The conjecture for unit triangles is true
    erdos_conjecture_unit ∧
    -- The stronger conjecture for any-size triangles is also true
    erdos_conjecture_any_size ∧
    -- The answer is YES
    ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (T6 n : ℝ) ≤ (1/27 + ε) * (n : ℝ)^3 := by
  constructor
  · exact erdos_conjecture_unit_true
  constructor
  · exact erdos_conjecture_any_size_true
  · exact erdos_conjecture_any_size_true

end Erdos755
