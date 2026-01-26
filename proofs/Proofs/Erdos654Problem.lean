/-!
# Erdős Problem #654 — Distinct Distances with No Four Concyclic

Given n points x₁, ..., xₙ ∈ ℝ² with no four points on a circle,
must there exist some xᵢ with at least (1 - o(1))n distinct distances
to the other points?

**Status: OPEN.**

Known: Every point has at least (n-1)/3 distinct distances.
Weaker variant (Erdős–Pach): under general position (no 3 collinear),
does some point have ≥ (1/3 + c)n distinct distances?

Reference: https://erdosproblems.com/654
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- A point configuration in the plane. -/
def PointConfig (n : ℕ) := Fin n → ℝ × ℝ

/-- No four points lie on a common circle. -/
def NoFourConcyclic (P : PointConfig n) : Prop :=
  ∀ i₁ i₂ i₃ i₄ : Fin n,
    i₁ ≠ i₂ → i₁ ≠ i₃ → i₁ ≠ i₄ → i₂ ≠ i₃ → i₂ ≠ i₄ → i₃ ≠ i₄ →
    ¬∃ (c : ℝ × ℝ) (r : ℝ), r > 0 ∧
      dist (P i₁) c = r ∧ dist (P i₂) c = r ∧
      dist (P i₃) c = r ∧ dist (P i₄) c = r

/-- The number of distinct distances from point xᵢ to all other points. -/
noncomputable def distinctDistances (P : PointConfig n) (i : Fin n) : ℕ :=
  ((Finset.univ.filter (· ≠ i)).image (fun j => dist (P i) (P j))).card

/-- The maximum number of distinct distances from any single point. -/
noncomputable def maxDistinctDistances (P : PointConfig n) : ℕ :=
  Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩ (distinctDistances P)

/-! ## Known Lower Bound -/

/-- Every point has at least (n-1)/3 distinct distances when
    no four are concyclic. -/
axiom known_lower_bound (n : ℕ) (hn : 4 ≤ n) (P : PointConfig n)
    (hP : NoFourConcyclic P) (i : Fin n) :
    (n - 1) / 3 ≤ distinctDistances P i

/-! ## The Main Conjecture -/

/-- **Erdős Problem #654**: Under the no-four-concyclic condition,
    some point must determine (1 - o(1))n distinct distances.
    Formally: for every ε > 0, for large enough n, some xᵢ has
    ≥ (1 - ε)n distinct distances. -/
axiom erdos_654_conjecture :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∀ P : PointConfig n, NoFourConcyclic P →
        ∃ i : Fin n, (1 - ε) * (n : ℝ) ≤ (distinctDistances P i : ℝ)

/-! ## Erdős–Pach Weaker Variant -/

/-- General position: no three points are collinear. -/
def NoThreeCollinear (P : PointConfig n) : Prop :=
  ∀ i₁ i₂ i₃ : Fin n, i₁ ≠ i₂ → i₂ ≠ i₃ → i₁ ≠ i₃ →
    ¬∃ (a b c : ℝ), (a, b) ≠ (0, 0) ∧
      a * (P i₁).1 + b * (P i₁).2 = c ∧
      a * (P i₂).1 + b * (P i₂).2 = c ∧
      a * (P i₃).1 + b * (P i₃).2 = c

/-- Erdős–Pach weaker conjecture: under general position,
    does some point have ≥ (1/3 + c)n distinct distances for
    some absolute constant c > 0? -/
axiom erdos_pach_weaker :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
      ∀ P : PointConfig n, NoThreeCollinear P →
        ∃ i : Fin n, ((1 : ℝ)/3 + c) * n ≤ (distinctDistances P i : ℝ)

/-! ## Context: Erdős Distinct Distances Problem -/

/-- Without any restriction, the Guth–Katz theorem (2015) gives
    Ω(n/log n) distinct distances in total. Problem #654 asks for
    near-n distinct distances from a SINGLE point, under geometric
    restrictions on the configuration. -/
axiom guth_katz_context (n : ℕ) (hn : 2 ≤ n) (P : PointConfig n) :
    ∃ c > 0, c * (n : ℝ) / Real.log n ≤
      ((Finset.univ.product Finset.univ).filter (fun (i, j) => i < j)
        |>.image (fun (i, j) => dist (P i) (P j))).card

/-- On a circle, at most 2 points determine each distance from
    the center. So the no-four-concyclic condition prevents
    many repeated distances from a single point. -/
axiom circle_distance_bound (P : PointConfig n) (hP : NoFourConcyclic P)
    (i : Fin n) (d : ℝ) (hd : 0 < d) :
    ((Finset.univ.filter (fun j => j ≠ i ∧ dist (P i) (P j) = d)).card) ≤ 3
