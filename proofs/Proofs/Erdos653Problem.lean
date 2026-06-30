/-
Erdős Problem #653: Distinct Distance Counts in the Plane

Source: https://erdosproblems.com/653
Status: OPEN

Statement:
Let x₁, ..., xₙ ∈ ℝ² be n points in the plane. Define R(xᵢ) as the number of
distinct distances from xᵢ to other points:
  R(xᵢ) = #{|xⱼ - xᵢ| : j ≠ i}

Order points so that R(x₁) ≤ ... ≤ R(xₙ). Let g(n) be the maximum number of
distinct values the R(xᵢ) can take.

Conjecture: g(n) ≥ (1 - o(1))n

Known bounds:
- Lower: g(n) > (7/10)n (Csizmadia)
- Lower: g(n) > (3/8)n (Erdős-Fishburn)
- Upper: g(n) < n - cn^(2/3) for some c > 0

References:
- [Er97e] Erdős original problem
- Erdős-Fishburn: 3/8 lower bound
- Csizmadia: 7/10 lower bound
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic

open Set Finset Real

namespace Erdos653

/-
## Part I: Point Configuration
-/

/--
**Euclidean Distance:**
The standard distance between two points in ℝ².
-/
noncomputable def euclidDist (p q : Fin 2 → ℝ) : ℝ :=
  Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2)

/--
**Point Configuration:**
A finite set of distinct points in the plane.
-/
def PointConfig (n : ℕ) := { S : Finset (Fin 2 → ℝ) // S.card = n }

/-
## Part II: Distinct Distance Count
-/

/--
**Distance Set from a Point:**
The set of all distances from point p to other points in S.
-/
noncomputable def distanceSet (S : Finset (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : Finset ℝ :=
  (S.filter (· ≠ p)).image (euclidDist p)

/--
**R(xᵢ) - Distinct Distance Count:**
The number of distinct distances from xᵢ to other points.
-/
noncomputable def distinctDistCount (S : Finset (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : ℕ :=
  (distanceSet S p).card

/-
## Part III: The Function g(n)
-/

/--
**R-Value Set:**
The set of all R(xᵢ) values for points in S.
-/
noncomputable def rValueSet (S : Finset (Fin 2 → ℝ)) : Finset ℕ :=
  S.image (distinctDistCount S)

/--
**Number of Distinct R-Values:**
How many different values R(xᵢ) takes across all points.
-/
noncomputable def numDistinctRValues (S : Finset (Fin 2 → ℝ)) : ℕ :=
  (rValueSet S).card

/--
**g(n) - Maximum Distinct R-Values:**
The maximum number of distinct R-values achievable by any n-point configuration.
-/
noncomputable def g (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset (Fin 2 → ℝ), S.card = n ∧ numDistinctRValues S = k }

/-
## Part IV: Known Bounds
-/

/-
**Erdős-Fishburn Lower Bound:**
g(n) > (3/8)n for all sufficiently large n.
(Documentary note: not formalized — only the sharper Csizmadia bound is axiomatized below.)
-/
/--
**Csizmadia Lower Bound:**
g(n) > (7/10)n for all sufficiently large n.
This improves the Erdős-Fishburn bound.
-/
axiom csizmadia_bound :
  ∀ n : ℕ, n ≥ 10 → g n > 7 * n / 10

/--
**Upper Bound:**
g(n) < n - cn^(2/3) for some constant c > 0.
This shows g(n) cannot equal n for large n.
-/
axiom upper_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (g n : ℝ) < n - c * (n : ℝ)^(2/3 : ℝ)

/-
## Part V: The Conjecture
-/

/--
**Erdős Problem #653 Conjecture:**
For any ε > 0, there exists N such that for all n ≥ N:
  g(n) ≥ (1 - ε)n

Equivalently: g(n)/n → 1 as n → ∞.
-/
def erdos653Conjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (g n : ℝ) ≥ (1 - ε) * n

/-
## Part VI: Basic Properties
-/

/- **Trivial Lower Bound:**
g(n) ≥ 1 for n ≥ 2 (at least one R-value exists).
(Documentary note: the formalized theorem `g_ge_one` lives in `Erdos653LowerBound.lean`.) -/
/--
**Trivial Upper Bound:**
g(n) ≤ n (can't have more distinct values than points).

Discharged from an axiom to a theorem (Axiom Integrity Policy): the R-value set
`rValueSet S = S.image (distinctDistCount S)` is the image of `S` under a map, so
`numDistinctRValues S = (rValueSet S).card ≤ S.card = n` by `Finset.card_image_le`,
and `g n` is the supremum of these counts (`csSup_le'`). This reuses the exact
proof vocabulary of the sharper `g_le_n_sub_one` below; unlike that lemma it needs
no `n ≥ 2` hypothesis, so it remains the all-`n` bound cited by `erdos_653_summary`.
-/
theorem g_le_n : ∀ n : ℕ, g n ≤ n := by
  intro n
  unfold g
  apply csSup_le'
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  obtain ⟨S, hcard, rfl⟩ := hk
  calc numDistinctRValues S
      = (rValueSet S).card := rfl
    _ = (S.image (distinctDistCount S)).card := rfl
    _ ≤ S.card := Finset.card_image_le
    _ = n := hcard

/-
**Monotonicity:**
g is non-decreasing in n.
(Documentary note: not formalized in this development.)
-/

/--
**Sharp Elementary Upper Bound:** `g(n) ≤ n - 1` for `n ≥ 2`.

This is strictly sharper than `g_le_n` and is the genuine elementary ceiling:
the deep `n - c·n^{2/3}` gap (`upper_bound`) lives in the `n^{2/3}` term, not in
the strict inequality `g(n) < n`, which is elementary.

Proof: every R-value `R(p) = distinctDistCount S p` for a point `p` in an
`n`-point configuration `S` lies in the interval `[1, n-1]`:
- `R(p) ≤ n - 1` because `distanceSet S p` is the image of `S.filter (· ≠ p) ⊆ S.erase p`
  (card `n - 1`) under `euclidDist p`, and `Finset.card_image_le` does not increase card;
- `R(p) ≥ 1` because for `n ≥ 2` there is another point `q ≠ p`, so `distanceSet S p`
  is nonempty.

Hence `rValueSet S ⊆ Finset.Icc 1 (n-1)`, whose cardinality is `n - 1`, and
`g n` is the supremum of these counts.
-/
theorem g_le_n_sub_one : ∀ n : ℕ, 2 ≤ n → g n ≤ n - 1 := by
  intro n hn
  unfold g
  apply csSup_le'
  intro k hk
  simp only [Set.mem_setOf_eq] at hk
  obtain ⟨S, hcard, rfl⟩ := hk
  have hsub : rValueSet S ⊆ Finset.Icc 1 (n - 1) := by
    intro m hm
    unfold rValueSet at hm
    rw [Finset.mem_image] at hm
    obtain ⟨p, hpS, rfl⟩ := hm
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · -- 1 ≤ distinctDistCount S p
      have h1 : 1 < S.card := by rw [hcard]; omega
      obtain ⟨q, hqS, hqp⟩ := Finset.exists_mem_ne h1 p
      have hne : (distanceSet S p).Nonempty := by
        refine ⟨euclidDist p q, ?_⟩
        unfold distanceSet
        exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hqS, hqp⟩, rfl⟩
      have hpos : 0 < distinctDistCount S p := by
        unfold distinctDistCount; exact Finset.card_pos.mpr hne
      omega
    · -- distinctDistCount S p ≤ n - 1
      have hsubE : S.filter (· ≠ p) ⊆ S.erase p := by
        intro x hx
        rw [Finset.mem_filter] at hx
        exact Finset.mem_erase.mpr ⟨hx.2, hx.1⟩
      unfold distinctDistCount distanceSet
      calc ((S.filter (· ≠ p)).image (euclidDist p)).card
          ≤ (S.filter (· ≠ p)).card := Finset.card_image_le
        _ ≤ (S.erase p).card := Finset.card_le_card hsubE
        _ = n - 1 := by rw [Finset.card_erase_of_mem hpS, hcard]
  calc numDistinctRValues S
      = (rValueSet S).card := rfl
    _ ≤ (Finset.Icc 1 (n - 1)).card := Finset.card_le_card hsub
    _ = n - 1 := by rw [Nat.card_Icc]; omega

/-
## Part VII: Special Configurations
-/

/--
**Collinear Points:**
For n collinear points, what is the R-value distribution?
If points are equally spaced, the R-values form a specific pattern.
-/
def IsCollinear (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∃ a b : Fin 2 → ℝ, a ≠ b ∧ ∀ p ∈ S, ∃ t : ℝ, p = fun i => a i + t * (b i - a i)

/--
**Regular Polygon:**
Points forming a regular n-gon have specific R-value structure.
For odd n, all vertices have the same R-value = ⌊n/2⌋.
-/
def IsRegularPolygon (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∃ center : Fin 2 → ℝ, ∃ r : ℝ, r > 0 ∧
    ∀ p ∈ S, euclidDist p center = r

/-
**Regular Polygon R-Values:**
In a regular n-gon, all points have the same R-value (for n ≥ 3).
(Documentary note: not formalized in this development.)
-/
/-
## Part VIII: Extremal Configurations
-/

/--
**High R-Diversity Configuration:**
A configuration achieving g(n) distinct R-values.
-/
def IsOptimalConfig (S : Finset (Fin 2 → ℝ)) : Prop :=
  numDistinctRValues S = g S.card

/-
**Existence of Optimal Configurations:**
For each n, there exists a configuration achieving g(n).
(Documentary note: not formalized in this development.)
-/
/-
## Part IX: Asymptotic Analysis
-/

/-
**Asymptotic Gap:**
The gap n - g(n) grows as Ω(n^(2/3)).
(Documentary note: not formalized in this development.)
-/
/- **Combined Bound:**
cn^(2/3) ≤ n - g(n) ≤ (3/10)n for large n.
(Documentary note: not formalized in this development.) -/
/-
## Part X: Connection to Unit Distance Problem
-/

/--
**Unit Distance Connection:**
The problem is related to the unit distance problem.
If many pairs are at unit distance, it affects R-value distribution.
-/
noncomputable def unitDistPairs (S : Finset (Fin 2 → ℝ)) : ℕ :=
  (S.filter fun p => (S.filter fun q => euclidDist p q = 1).card > 0).card

/--
**Distinct Distances Connection:**
Related to Erdős distinct distances problem.
More distinct distances generally means more diverse R-values.
-/
noncomputable def totalDistinctDistances (S : Finset (Fin 2 → ℝ)) : ℕ :=
  (Finset.biUnion S (distanceSet S)).card

/-
## Part XI: Summary
-/

/--
**Erdős Problem #653: Summary**

1. g(n) is the max number of distinct R-values for n points in ℝ²
2. Best lower bound: g(n) > 0.7n (Csizmadia)
3. Upper bound: g(n) < n - cn^(2/3)
4. Conjecture: g(n) ≥ (1 - o(1))n
5. Status: OPEN
-/
theorem erdos_653_summary :
    -- g(n) > 0.7n for large n
    (∀ n ≥ 10, g n > 7 * n / 10) ∧
    -- g(n) ≤ n always
    (∀ n, g n ≤ n) ∧
    -- There exists an upper bound gap
    (∃ c > 0, ∀ n ≥ 2, (g n : ℝ) < n - c * (n : ℝ)^(2/3 : ℝ)) :=
  ⟨csizmadia_bound, g_le_n, upper_bound⟩

/-- **Erdős Problem #653:**
Combines Csizmadia lower bound, trivial upper bound, and nontrivial upper gap. -/
theorem erdos_653 :
    (∀ n ≥ 10, g n > 7 * n / 10) ∧
    (∀ n, g n ≤ n) ∧
    (∃ c > 0, ∀ n ≥ 2, (g n : ℝ) < n - c * (n : ℝ)^(2/3 : ℝ)) :=
  erdos_653_summary

end Erdos653
