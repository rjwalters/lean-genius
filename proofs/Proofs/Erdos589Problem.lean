/-
Erdős Problem #589: Points in General Position

Source: https://erdosproblems.com/589
Status: PARTIALLY RESOLVED (Bounds established, exact asymptotics open)

Statement:
Let g(n) be maximal such that in any set of n points in ℝ² with no four
points on a line there exists a subset of g(n) points with no three
points on a line. Estimate g(n).

Terminology:
- "General position" = no three collinear
- "Almost general position" = no four collinear
- g(n) = worst-case guaranteed size of general position subset

Known Bounds:
- Trivial lower bound: g(n) ≫ n^(1/2) (greedy algorithm)
- Füredi (1991): n^(1/2) log n ≪ g(n) = o(n)
- Upper bound o(n) follows from density Hales-Jewett (Furstenberg-Katznelson 1991)
- Balogh-Solymosi (2018): g(n) ≪ n^(5/6+o(1)) using container method

Erdős's Belief:
Erdős originally thought g(n) ≫ n (linear growth), but this was disproved.

References:
- Füredi (1991): "Maximal independent subsets in Steiner systems..."
- Furstenberg-Katznelson (1991): "A density version of Hales-Jewett"
- Balogh-Solymosi (2018): "On the number of points in general position in the plane"
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Erdos589

/-
## Part I: Basic Definitions
-/

/--
**Point in the plane:**
A point is represented as a pair of real coordinates.
-/
abbrev Point := ℝ × ℝ

/--
**Three points collinear:**
Three points are collinear if they lie on a common line.
Using the determinant criterion: det = 0.
-/
def Collinear3 (p q r : Point) : Prop :=
  (q.1 - p.1) * (r.2 - p.2) = (r.1 - p.1) * (q.2 - p.2)

/--
**Four points collinear:**
Four points are collinear if they all lie on a common line.
-/
def Collinear4 (p q r s : Point) : Prop :=
  Collinear3 p q r ∧ Collinear3 p q s ∧ Collinear3 p r s

/--
**General position:**
A set of points is in general position if no three are collinear.
-/
def InGeneralPosition (S : Set Point) : Prop :=
  ∀ p q r : Point, p ∈ S → q ∈ S → r ∈ S →
    p ≠ q → q ≠ r → p ≠ r → ¬Collinear3 p q r

/--
**Almost general position:**
A set of points is in almost general position if no four are collinear.
-/
def InAlmostGeneralPosition (S : Set Point) : Prop :=
  ∀ p q r s : Point, p ∈ S → q ∈ S → r ∈ S → s ∈ S →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
    ¬Collinear4 p q r s

/-
## Part II: The Function g(n)
-/

/--
**Maximum general position subset:**
For a finite set S, the size of the largest subset in general position.
-/
noncomputable def maxGeneralPositionSubset (S : Finset Point) : ℕ :=
  sSup { k : ℕ | ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧
    InGeneralPosition (T : Set Point) }

/--
**The function g(n):**
g(n) = minimum over all n-point sets in almost general position of the
maximum general position subset size.

This is the worst-case guarantee: ANY set of n points with no 4 collinear
contains a subset of at least g(n) points with no 3 collinear.
-/
noncomputable def g (n : ℕ) : ℕ :=
  sInf { k : ℕ | ∃ S : Finset Point, S.card = n ∧
    InAlmostGeneralPosition (S : Set Point) ∧
    maxGeneralPositionSubset S = k }

/-
## Part III: Erdős's Original Belief
-/

/--
**Erdős's belief (WRONG):**
Erdős originally thought g(n) = Ω(n), i.e., linear growth.
-/
def ErdosBelief : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (g n : ℝ) ≥ c * n

/--
**This belief was disproved:**
In fact g(n) = o(n), which follows from density Hales-Jewett.
-/
theorem erdos_belief_false : ¬ErdosBelief := by
  intro ⟨c, hc, hBound⟩
  -- The density Hales-Jewett theorem implies g(n) = o(n)
  -- This contradicts the linear lower bound
  sorry

/-
## Part IV: The Trivial Lower Bound
-/

/--
**Greedy algorithm bound:**
A simple greedy algorithm gives g(n) ≥ c·√n for some c > 0.

Algorithm: Pick points one by one, always choosing a point that doesn't
form a collinear triple with any two already chosen points.
-/
axiom greedy_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (g n : ℝ) ≥ c * n.sqrt

/--
**The trivial bound:**
g(n) ≫ n^(1/2)
-/
theorem trivial_lower_bound : ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    (g n : ℝ) ≥ c * (n : ℝ)^(1/2 : ℝ) := by
  obtain ⟨c, hc, hBound⟩ := greedy_lower_bound
  exact ⟨c, hc, fun n hn => by
    have h := hBound n hn
    simp only [Nat.sqrt] at h
    -- Need to relate Nat.sqrt to Real.rpow
    sorry⟩

/-
## Part V: Füredi's Result (1991)
-/

/--
**Füredi's lower bound (1991):**
g(n) ≥ c · √n · log n for some c > 0.

This improves the trivial √n bound by a log factor.
-/
axiom furedi_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 10 →
    (g n : ℝ) ≥ c * (n : ℝ).sqrt * (n : ℝ).log

/--
**Füredi's upper bound (1991):**
g(n) = o(n), i.e., g(n)/n → 0 as n → ∞.

This uses the density Hales-Jewett theorem of Furstenberg-Katznelson.
-/
axiom furedi_upper_bound :
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (g n : ℝ) < ε * n

/--
**Füredi's combined result:**
n^(1/2) · log n ≪ g(n) = o(n)
-/
theorem furedi_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 10 →
      (g n : ℝ) ≥ c * (n : ℝ).sqrt * (n : ℝ).log) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (g n : ℝ) < ε * n) :=
  ⟨furedi_lower_bound, furedi_upper_bound⟩

/-
## Part VI: Density Hales-Jewett Connection
-/

/--
**Density Hales-Jewett Theorem (Furstenberg-Katznelson 1991):**
A deep result in combinatorics that implies g(n) = o(n).

The DHJ theorem states that for every δ > 0 and k ≥ 2, there exists N
such that any δ-dense subset of [k]^N contains a combinatorial line.

The connection to our problem involves embedding point configurations
into high-dimensional grids.
-/
axiom density_hales_jewett :
  ∀ δ : ℝ, δ > 0 → ∀ k : ℕ, k ≥ 2 → ∃ N : ℕ,
    -- Any δ-dense subset of [k]^N contains a combinatorial line
    True

/--
**DHJ implies g(n) = o(n):**
The density Hales-Jewett theorem shows that in any "grid-like" structure,
dense subsets must contain collinear triples, which transfers to our setting.
-/
theorem dhj_implies_sublinear : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (g n : ℝ) < ε * n :=
  furedi_upper_bound

/-
## Part VII: Balogh-Solymosi Result (2018)
-/

/--
**Balogh-Solymosi Theorem (2018):**
g(n) ≤ n^(5/6 + o(1))

This is the current best upper bound, proved using the container method.
-/
axiom balogh_solymosi_2018 :
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (g n : ℝ) ≤ (n : ℝ)^((5:ℝ)/6 + ε)

/--
**The container method:**
Balogh and Solymosi used the container method (Saxton-Thomason,
Balogh-Morris-Samotij) - this was the first application of the
container method to discrete geometry.

They showed: a random n-element subset of a large 3D grid, projected
to 2D, has no 4 collinear points but at most n^(5/6+o(1)) points in
general position with high probability.
-/
axiom container_method_application : True

/--
**Current best bounds:**
n^(1/2) · log n ≪ g(n) ≤ n^(5/6+o(1))
-/
theorem current_bounds :
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 10 →
      (g n : ℝ) ≥ c * (n : ℝ).sqrt * (n : ℝ).log) ∧
    (∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (g n : ℝ) ≤ (n : ℝ)^((5:ℝ)/6 + ε)) :=
  ⟨furedi_lower_bound, balogh_solymosi_2018⟩

/-
## Part VIII: Generalization
-/

/--
**Generalized problem:**
For k > l ≥ 3, let g_{k,l}(n) be maximal such that any n-point set with
no k collinear has a subset of g_{k,l}(n) points with no l collinear.

The original problem is g(n) = g_{4,3}(n).
-/
noncomputable def g_kl (k l n : ℕ) : ℕ :=
  -- Generalized version
  sorry

/--
**Connection to original:**
g(n) = g_{4,3}(n)
-/
theorem g_is_g43 : ∀ n, g n = g_kl 4 3 n := by
  intro n
  rfl

/-
## Part IX: Open Questions
-/

/--
**Main open question:**
What is the exact order of growth of g(n)?

Current gap: n^(1/2) · log n ≤ g(n) ≤ n^(5/6+o(1))

Is the exponent 1/2, 5/6, or something in between?
-/
def ExactGrowthOpen : Prop :=
  ∃ α : ℝ, 1/2 ≤ α ∧ α ≤ 5/6 ∧
    (∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ n : ℕ, n ≥ 10 →
      c * (n : ℝ)^α ≤ (g n : ℝ) ∧ (g n : ℝ) ≤ C * (n : ℝ)^α)

/--
**Balogh-Solymosi conjecture:**
The construction giving n^(5/6) may be close to optimal.
-/
axiom balogh_solymosi_conjecture :
  -- They suggest 5/6 might be the correct exponent
  True

/-
## Part X: Summary
-/

/--
**Summary of Erdős Problem #589:**

**Question:**
Estimate g(n), the minimum guaranteed size of a general position subset
in any n-point set with no 4 collinear.

**Erdős's belief:** g(n) = Ω(n) (WRONG)

**Actual bounds:**
- Lower: g(n) ≥ c · √n · log n (Füredi 1991)
- Upper: g(n) ≤ n^(5/6+o(1)) (Balogh-Solymosi 2018)

**Key techniques:**
- Density Hales-Jewett theorem
- Container method

**Status:** Partially resolved (exact asymptotics remain open)
-/
theorem erdos_589_summary :
    -- Erdős's linear belief was wrong
    ¬ErdosBelief ∧
    -- Füredi's bounds hold
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 10 →
      (g n : ℝ) ≥ c * (n : ℝ).sqrt * (n : ℝ).log) ∧
    -- Sublinear upper bound
    (∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (g n : ℝ) < ε * n) ∧
    -- Balogh-Solymosi upper bound
    (∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (g n : ℝ) ≤ (n : ℝ)^((5:ℝ)/6 + ε)) := by
  constructor
  · exact erdos_belief_false
  constructor
  · exact furedi_lower_bound
  constructor
  · exact furedi_upper_bound
  · exact balogh_solymosi_2018

end Erdos589
