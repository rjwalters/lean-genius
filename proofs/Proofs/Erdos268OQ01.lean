/-
  Erdős #268 Open Question 1: Optimal Ball Radius in X_d

  Source: Follow-up to Erdős Problem #268
  Status: OPEN

  Question:
  What is the largest open ball contained in X_d for each dimension d?
  How does the optimal radius decay with d?

  Background:
  - Kovač-Tao (2024) proved X_d has nonempty interior for all d ≥ 1
  - Kovač (2024) gave explicit ball construction for d = 3
  - The optimal radius R(d) = sup{r : ∃ c, B(c,r) ⊆ X_d} is well-defined
  - Basic monotonicity: R(d) should decrease with d (more constraints)

  What we formalize:
  1. Definition of optimal radius R(d)
  2. R(d) > 0 (from Kovač-Tao main theorem)
  3. R(d₁) ≥ R(d₂) for d₁ ≤ d₂ (dimension monotonicity)
  4. Upper bounds: R(d) ≤ sup coordinate value

  Tags: analysis, harmonic-series, topology, number-theory, open-problem
-/

import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

namespace Erdos268OQ01

open Set Filter Topology

/-! ## Definitions from Erdős #268 -/

/-- A subset A ⊆ ℕ has a convergent harmonic subseries. -/
def HasConvergentHarmonicSubseries (A : Set ℕ) : Prop :=
  Summable (fun n : A => (1 : ℝ) / n)

/-- The shifted harmonic subseries sum. -/
noncomputable def shiftedHarmonicSum (A : Set ℕ) (k : ℕ) : ℝ :=
  ∑' n : A, (1 : ℝ) / (n + k)

/-- The d-dimensional harmonic point. -/
noncomputable def harmonicPoint (d : ℕ) (A : Set ℕ) : Fin d → ℝ :=
  fun i => shiftedHarmonicSum A i.val

/-- The set X_d ⊆ ℝ^d of all harmonic subseries points. -/
def harmonicPointSet (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ A : Set ℕ, A.Infinite ∧ HasConvergentHarmonicSubseries A ∧
    x = harmonicPoint d A}

/-! ## The Main Axiom (from Erdős #268) -/

/-- The Kovač-Tao theorem: X_d has nonempty interior for all d. -/
axiom erdos_268_interior (d : ℕ) :
    (interior (harmonicPointSet d)).Nonempty

/-! ## Part I: The Optimal Radius -/

/-- The set of radii for which a ball of that radius fits inside X_d. -/
def admissibleRadii (d : ℕ) : Set ℝ :=
  {r | r > 0 ∧ ∃ c : Fin d → ℝ, Metric.ball c r ⊆ harmonicPointSet d}

/-- The optimal radius R(d): supremum of radii of inscribed balls.
    This is the central quantity of interest for OQ-01. -/
noncomputable def optimalRadius (d : ℕ) : ℝ :=
  sSup (admissibleRadii d)

/-- Alternative: the inscribed ball radius using infimum distance to complement. -/
noncomputable def inscribedRadius (d : ℕ) (c : Fin d → ℝ)
    (hc : c ∈ interior (harmonicPointSet d)) : ℝ :=
  sInf {r : ℝ | r > 0 ∧ ¬(Metric.ball c r ⊆ harmonicPointSet d)}

/-! ## Part II: Basic Properties -/

/-- There exists a ball of positive radius inside X_d. -/
theorem exists_inscribed_ball (d : ℕ) :
    ∃ (c : Fin d → ℝ) (r : ℝ), r > 0 ∧
      Metric.ball c r ⊆ harmonicPointSet d := by
  have h := erdos_268_interior d
  obtain ⟨x, hx⟩ := h
  rw [mem_interior] at hx
  obtain ⟨U, hU, hopen, hxU⟩ := hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen x hxU
  exact ⟨x, r, hr, fun y hy => hU (hball hy)⟩

/-- The set of admissible radii is nonempty. -/
theorem admissibleRadii_nonempty (d : ℕ) :
    (admissibleRadii d).Nonempty := by
  obtain ⟨c, r, hr, hball⟩ := exists_inscribed_ball d
  exact ⟨r, hr, c, hball⟩

/-- Admissible radii are bounded above (X_d is bounded since all coordinates
    are positive but finite sums). -/
theorem admissibleRadii_bddAbove (d : ℕ) (hd : d ≥ 1) :
    BddAbove (admissibleRadii d) := by
  sorry

/-- The optimal radius is positive: R(d) > 0. -/
theorem optimalRadius_pos (d : ℕ) : optimalRadius d > 0 := by
  sorry

/-! ## Part III: Dimension Monotonicity -/

/-- Projection map from ℝ^{d₂} to ℝ^{d₁} for d₁ ≤ d₂. -/
def projectionMap (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) : (Fin d₂ → ℝ) → (Fin d₁ → ℝ) :=
  fun x => fun i => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/-- Projection preserves harmonicPointSet membership. -/
theorem projection_preserves (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) :
    projectionMap d₁ d₂ h '' harmonicPointSet d₂ ⊆ harmonicPointSet d₁ := by
  intro x ⟨y, hy, hxy⟩
  obtain ⟨A, hA_inf, hA_conv, hA_eq⟩ := hy
  refine ⟨A, hA_inf, hA_conv, ?_⟩
  subst hxy; subst hA_eq
  ext i; simp [projectionMap, harmonicPoint]

/-- The optimal radius is non-increasing in d:
    R(d₁) ≥ R(d₂) when d₁ ≤ d₂. -/
theorem optimalRadius_antitone (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) :
    optimalRadius d₁ ≥ optimalRadius d₂ := by
  sorry

/-! ## Part IV: Upper Bounds -/

/-- All points in X_d have positive coordinates. -/
theorem harmonicPoint_coords_pos (d : ℕ) (A : Set ℕ)
    (hA : A.Nonempty) (hconv : HasConvergentHarmonicSubseries A) (i : Fin d) :
    harmonicPoint d A i > 0 := by
  simp only [harmonicPoint, shiftedHarmonicSum]
  obtain ⟨n, hn⟩ := hA
  apply tsum_pos
  · exact Summable.of_nonneg_of_le
      (fun m => div_nonneg one_nonneg (by positivity))
      (fun ⟨m, hm⟩ => div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast Nat.le_add_right m i.val))
      hconv
  · intro m; exact div_nonneg one_nonneg (by positivity)
  · exact div_pos one_pos (by positivity)

/-- The harmonic subseries sum is always positive for nonempty A. -/
theorem harmonicSum_pos (A : Set ℕ) (hA : A.Nonempty)
    (hconv : HasConvergentHarmonicSubseries A) :
    ∑' n : A, (1 : ℝ) / n > 0 := by
  obtain ⟨n, hn⟩ := hA
  exact tsum_pos hconv (fun m => div_nonneg one_nonneg (by positivity))
    ⟨n, hn⟩ (div_pos one_pos (by positivity))

/-! ## Part V: Geometric Constraints -/

/-- X_d lies in the positive orthant. -/
theorem harmonicPointSet_in_positive_orthant (d : ℕ) :
    harmonicPointSet d ⊆ {x : Fin d → ℝ | ∀ i, x i > 0} := by
  intro x ⟨A, hA_inf, hA_conv, hA_eq⟩
  subst hA_eq
  intro i
  exact harmonicPoint_coords_pos d A hA_inf.nonempty hA_conv i

/-- X_d lies in a cone: coordinates are strictly decreasing. -/
theorem harmonicPointSet_in_cone (d : ℕ) :
    harmonicPointSet d ⊆
      {x : Fin d → ℝ | ∀ i j : Fin d, i.val < j.val → x j < x i} := by
  intro x ⟨A, hA_inf, hA_conv, hA_eq⟩
  subst hA_eq
  intro i j hij
  simp only [harmonicPoint, shiftedHarmonicSum]
  apply tsum_lt_tsum
  · intro ⟨n, hn⟩
    apply div_le_div_of_nonneg_left (by positivity : (0:ℝ) < 1) (by positivity) (by positivity)
    exact_mod_cast Nat.add_le_add_left (Nat.le_of_lt hij) n
  · obtain ⟨n, hn⟩ := hA_inf.nonempty
    exact ⟨⟨n, hn⟩, div_lt_div_of_pos_left (by positivity : (0:ℝ) < 1) (by positivity)
      (by exact_mod_cast Nat.add_lt_add_left hij n)⟩
  · exact Summable.of_nonneg_of_le
      (fun m => div_nonneg one_nonneg (by positivity))
      (fun ⟨m, hm⟩ => div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by exact_mod_cast Nat.le_add_right m i.val))
      hA_conv

/-- Upper bound on optimal radius: R(d) is at most the supremum of the
    first coordinate over all points in X_d divided by d.
    (Intuition: the ball can't extend beyond the cone constraints.) -/
theorem optimalRadius_upper_bound (d : ℕ) (hd : d ≥ 1) :
    ∀ r ∈ admissibleRadii d, r ≤ sSup {x 0 | x ∈ harmonicPointSet d} := by
  sorry

end Erdos268OQ01
