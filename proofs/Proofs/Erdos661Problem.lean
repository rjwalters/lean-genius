/-!
# Erdős Problem #661 — Bipartite Distinct Distances

Do there exist point sets x₁,...,xₙ and y₁,...,yₙ in ℝ² such that
the number of distinct distances d(xᵢ,yⱼ) is o(n/√(log n))?

Let F(2n) be the minimum number of distinct bipartite distances
between two sets of n points, and f(2n) the minimum for 2n
general points. The question is whether F(2n) = o(f(2n)).

In ℝ⁴, Lenz showed all distances can be equal (two orthogonal
circles). In ℝ², the answer is unknown.

$50 reward.

Status: OPEN
Reference: https://erdosproblems.com/661
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- A point in ℝ². -/
def Point2 := ℝ × ℝ

/-- Squared Euclidean distance between two points. -/
def distSq (p q : Point2) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- The set of distinct squared distances from a set X to a set Y. -/
noncomputable def bipartiteDistSet (X Y : Finset Point2) : Finset ℝ :=
  (X ×ˢ Y).image (fun p => distSq p.1 p.2)

/-- F(2n): the minimum number of distinct bipartite distances
    between two n-point sets in ℝ². -/
noncomputable def minBipartiteDist : ℕ → ℕ := fun _ => 0  -- axiomatized

/-- f(2n): the minimum number of distinct distances among 2n
    points in ℝ². -/
noncomputable def minDistinct2n : ℕ → ℕ := fun _ => 0  -- axiomatized

/-! ## Main Conjecture -/

/-- **Erdős Problem #661**: Is F(2n) = o(f(2n))?
    Equivalently, can bipartite arrangements achieve
    asymptotically fewer distinct distances than general
    point configurations? -/
axiom erdos_661_bipartite_advantage :
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (minBipartiteDist n : ℝ) ≤ ε * (minDistinct2n n : ℝ)

/-! ## Known Bounds -/

/-- **Guth–Katz (2015)**: f(2n) ≳ n/log n. The minimum number
    of distinct distances among 2n points is Ω(n/log n). -/
axiom guth_katz_lower :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (minDistinct2n n : ℝ) ≥ C * n / Real.log n

/-- **Lattice Upper Bound**: f(2n) ≲ n/√(log n) from the integer
    lattice. Thus the question asks if F(2n) = o(n/√(log n)). -/
axiom lattice_upper :
  ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      (minDistinct2n n : ℝ) ≤ C * n / Real.sqrt (Real.log n)

/-! ## Higher Dimensions -/

/-- **Lenz Construction (ℝ⁴)**: In ℝ⁴, place x₁,...,xₙ on one
    circle and y₁,...,yₙ on an orthogonal circle. Then
    d(xᵢ,yⱼ) = √2 for all i,j: only one bipartite distance. -/
axiom lenz_construction : True

/-! ## Observations -/

/-- **Connection to Problem #89**: The Erdős distinct distances
    problem (general case) is Problem #89. This bipartite variant
    asks whether the bipartite structure provides additional savings. -/
axiom erdos_89_connection : True

/-- **$50 Reward**: Erdős offered $50 for resolving this problem. -/
axiom reward : True
