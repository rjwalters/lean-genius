/-
# Erdős Problem #135: Four Points, Five Distances

**Problem**: Let $A \subset \mathbb{R}^2$ be a set of $n$ points such that any
four points determine at least 5 distinct distances. Must $A$ determine
$\gg n^2$ many distinct distances?

**Answer**: NO — disproved by **Tao (2024)**.

Tao constructed $n$-point sets with the "five-distance property" but only
$O(n^2 / \sqrt{\log n})$ distinct distances — strictly below $\Omega(n^2)$.

**Key technique**: Randomized algebraic curves (parabolas mod $p$) over finite
fields, with random affine transformations to eliminate forbidden 4-point patterns.
Probabilistic deletion of remaining bad 4-tuples yields the construction.

**Connection to Guth-Katz**: Any $n$ points have $\geq c \cdot n / \sqrt{\log n}$
distinct distances (Guth-Katz 2015). Tao's construction achieves
$O(n^2 / \sqrt{\log n})$ — matching the exponent of log, with an extra factor of $n$.

**Prize**: $250 (now closed — DISPROVED)

**References**:
- Tao, T. (2024): "Planar point sets with forbidden 4-point patterns and few
  distinct distances." arXiv:2409.01343
- Erdős, P.; Gyárfás, A.: Original conjecture
- Guth, L.; Katz, N. (2015): Lower bound for distinct distances. Ann. Math.
- https://erdosproblems.com/135
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos135

open Set Finset Real

/- ## Definitions -/

/-- A point in the plane $\mathbb{R}^2$. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The set of distinct (squared) distances in $A$: positive pairwise values. -/
noncomputable def distinctDistances (A : Finset Point) : Finset ℝ :=
  ((A ×ˢ A).filter fun pq => pq.1 ≠ pq.2).image fun pq => dist pq.1 pq.2

/-- The count of distinct distances. -/
noncomputable def distanceCount (A : Finset Point) : ℕ := (distinctDistances A).card

/-- All 6 pairwise distances of 4 points (as a Finset, so duplicates are merged). -/
noncomputable def fourPointDistances (p₁ p₂ p₃ p₄ : Point) : Finset ℝ :=
  {dist p₁ p₂, dist p₁ p₃, dist p₁ p₄, dist p₂ p₃, dist p₂ p₄, dist p₃ p₄}

/-- A set has the **five-distance property** if any 4 distinct points determine
at least 5 distinct distances. -/
def HasFiveDistanceProperty (A : Finset Point) : Prop :=
  ∀ p₁ p₂ p₃ p₄ : Point,
    p₁ ∈ A → p₂ ∈ A → p₃ ∈ A → p₄ ∈ A →
    p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
    (fourPointDistances p₁ p₂ p₃ p₄).card ≥ 5

/-- Four points form a **parallelogram** if two pairs of opposite sides are equal. -/
def IsParallelogram (p₁ p₂ p₃ p₄ : Point) : Prop :=
  p₁ - p₂ = p₄ - p₃ ∨ p₁ - p₃ = p₄ - p₂ ∨ p₁ - p₄ = p₃ - p₂

/-- A 4-point pattern is **forbidden** if it determines fewer than 5 distinct distances. -/
def IsForbiddenPattern (p₁ p₂ p₃ p₄ : Point) : Prop :=
  (fourPointDistances p₁ p₂ p₃ p₄).card < 5

/- ## Erdős's Conjecture (Disproved) -/

/-- **Erdős Conjecture #135**: If $A$ has the five-distance property, then
$A$ determines $\Omega(n^2)$ distinct distances. -/
def ErdosConjecture135 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ A : Finset Point,
    HasFiveDistanceProperty A → (distanceCount A : ℝ) ≥ c * (A.card : ℝ)^2

/- ## Key Results (Axiomatized) -/

/-- **Tao's theorem (2024)**: Erdős Conjecture #135 is FALSE. -/
axiom erdos_135_false : ¬ErdosConjecture135

/-- **Tao's construction**: For large $n$, there exists an $n$-point set with
the five-distance property and only $O(n^2/\sqrt{\log n})$ distinct distances. -/
axiom tao_counterexample :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    ∃ A : Finset Point,
      HasFiveDistanceProperty A ∧
      A.card = n ∧
      (distanceCount A : ℝ) ≤ C * n ^ 2 / Real.sqrt (Real.log n)

/-- **Guth-Katz (2015)**: Any $n$-point set determines at least
$c \cdot n / \sqrt{\log n}$ distinct distances. -/
axiom guth_katz_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ A : Finset Point, A.card ≥ 2 →
    (distanceCount A : ℝ) ≥ c * A.card / Real.sqrt (Real.log A.card)

/-- **Parallelograms determine ≤ 3 distances** (as the two side lengths and the diagonal
may coincide, giving 2 or 3 values). This is why parabola-based constructions avoid them. -/
axiom parallelogram_few_distances (p₁ p₂ p₃ p₄ : Point)
    (h : IsParallelogram p₁ p₂ p₃ p₄)
    (hdist : p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄) :
    (fourPointDistances p₁ p₂ p₃ p₄).card ≤ 3

/-- **Tao avoids parallelograms**: Sets with the five-distance property contain
no parallelogram — parallelograms determine ≤ 3 distances, failing the threshold.
The parabola construction is specifically designed to avoid this pattern. -/
axiom tao_avoids_parallelograms :
  ∀ A : Finset Point, HasFiveDistanceProperty A →
    ∀ p₁ p₂ p₃ p₄ : Point, p₁ ∈ A → p₂ ∈ A → p₃ ∈ A → p₄ ∈ A →
      p₁ ≠ p₂ → p₁ ≠ p₃ → p₁ ≠ p₄ → p₂ ≠ p₃ → p₂ ≠ p₄ → p₃ ≠ p₄ →
      ¬IsParallelogram p₁ p₂ p₃ p₄

/- ## Proved Consequences -/

/-- **Corollary**: Erdős Conjecture #135 is disproved. -/
theorem erdos_135_disproved : ¬ErdosConjecture135 := erdos_135_false

/-- **Parallelograms are forbidden patterns**: A parallelogram determines ≤ 3 distances,
hence is a "forbidden" 4-point pattern (requires ≥ 5). -/
theorem parallelogram_forbidden (p₁ p₂ p₃ p₄ : Point)
    (h : IsParallelogram p₁ p₂ p₃ p₄)
    (hdist : p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₁ ≠ p₄ ∧ p₂ ≠ p₃ ∧ p₂ ≠ p₄ ∧ p₃ ≠ p₄) :
    IsForbiddenPattern p₁ p₂ p₃ p₄ := by
  have h3 := parallelogram_few_distances p₁ p₂ p₃ p₄ h ⟨hdist.1, hdist.2.1, hdist.2.2.1⟩
  exact Nat.lt_of_le_of_lt h3 (by norm_num)

/-- **Tao matches Guth-Katz in the log exponent**: The lower bound for all point sets
($\geq n/\sqrt{\log n}$ distances) and the upper bound for five-distance-property sets
($\leq n^2/\sqrt{\log n}$ distances) have the same exponent $1/2$ on the log factor.
The gap between them is exactly a factor of $n$.
-/
theorem tao_optimal_up_to_log :
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧
      (∀ A : Finset Point, A.card ≥ 2 →
        (distanceCount A : ℝ) ≥ C₁ * A.card / Real.sqrt (Real.log A.card)) ∧
      (∀ n : ℕ, n ≥ 2 → ∃ A : Finset Point,
        HasFiveDistanceProperty A ∧ A.card = n ∧
          (distanceCount A : ℝ) ≤ C₂ * n ^ 2 / Real.sqrt (Real.log n)) := by
  obtain ⟨c, hc, hbound⟩ := guth_katz_lower_bound
  obtain ⟨C, hC, htao⟩ := tao_counterexample
  exact ⟨c, C, hc, hC, hbound, htao⟩

end Erdos135
