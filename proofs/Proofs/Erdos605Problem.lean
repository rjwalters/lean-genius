/-
  Erdős Problem #605: Repeated Distances on a Sphere

  Source: https://erdosproblems.com/605
  Status: SOLVED (affirmatively)

  Statement:
  Is there a function f(n) → ∞ as n → ∞ such that n distinct points can be
  placed on a 2-sphere with at least f(n)·n pairs at the same distance?

  Answer: YES

  Key Results:
  - Erdős-Hickerson-Pach (1989): u_D(n) ≫ n·log*n for all D > 1
  - For D = √2: u(n) ≈ n^{4/3}
  - Swanepoel-Valtr (2004): u_D(n) ≫ n·√(log n)
  - Upper bound: u_D(n) ≪ n^{4/3} for all D

  References:
  [EHP89] Erdős-Hickerson-Pach, "A problem of Leo Moser about repeated distances" (1989)
  [SwVa04] Swanepoel-Valtr, "The unit distance problem on spheres" (2004)

  Tags: geometry, distances, discrete-geometry, sphere
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace Erdos605

open Real Finset

/-! ## Part I: Points on a Sphere -/

/-- A sphere of radius r centered at the origin in ℝ³. -/
def Sphere (r : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ‖p‖ = r}

/-- The unit sphere S². -/
def UnitSphere : Set (EuclideanSpace ℝ (Fin 3)) := Sphere 1

/-- The sphere of radius √2 (special case with known tight bounds). -/
noncomputable def SqrtTwoSphere : Set (EuclideanSpace ℝ (Fin 3)) := Sphere (Real.sqrt 2)

/-- A configuration of n points on a sphere. -/
structure SphereConfiguration (r : ℝ) (n : ℕ) where
  points : Fin n → EuclideanSpace ℝ (Fin 3)
  on_sphere : ∀ i, points i ∈ Sphere r
  distinct : Function.Injective points

/-! ## Part II: Distance Pairs -/

/-- The distance between two points. -/
noncomputable def pointDistance (p q : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  dist p q

/-- A pair of distinct indices. -/
def DistinctPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The set of all distinct pairs. -/
def allPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.filter (fun p => p.1 < p.2) Finset.univ

/-- Count pairs at a specific distance d in a configuration. -/
noncomputable def countPairsAtDistance {r : ℝ} {n : ℕ}
    (config : SphereConfiguration r n) (d : ℝ) : ℕ :=
  (allPairs n).filter (fun p => pointDistance (config.points p.1) (config.points p.2) = d) |>.card

/-- The maximum number of pairs at the same distance. -/
noncomputable def maxRepeatedPairs {r : ℝ} {n : ℕ}
    (config : SphereConfiguration r n) : ℕ :=
  Finset.univ.sup fun d : ℝ => countPairsAtDistance config d

/-! ## Part III: The Function u_D(n) -/

/-- u_D(n) = maximum pairs at distance 1 among n points on sphere of radius D. -/
noncomputable def u (D : ℝ) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ config : SphereConfiguration D n,
    ∃ d : ℝ, countPairsAtDistance config d = k}

/-- The maximum repeated distance count over all configurations. -/
noncomputable def maxRepeatedDistance (D : ℝ) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ config : SphereConfiguration D n, maxRepeatedPairs config = k}

/-! ## Part IV: The Main Question -/

/-- **Erdős Problem #605**

    Does there exist f : ℕ → ℝ with f(n) → ∞ such that for all n,
    we can place n points on a sphere with ≥ f(n)·n pairs at the same distance?
-/
def Erdos605Statement : Prop :=
  ∃ f : ℕ → ℝ, (Filter.Tendsto f Filter.atTop Filter.atTop) ∧
    ∀ D > (1 : ℝ), ∀ n : ℕ, n > 0 → (u D n : ℝ) ≥ f n * n

/-! ## Part V: Known Results -/

/-- The iterated logarithm log*(n). -/
noncomputable def iteratedLog : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 => if Real.log (n + 2) ≤ 1 then 0 else 1 + iteratedLog ⌊Real.log (n + 2)⌋₊

/-- **Erdős-Hickerson-Pach (1989)**

    For any D > 1, u_D(n) ≫ n · log*(n).
    This was the first proof that f(n) → ∞ exists.
-/
axiom ehp_lower_bound (D : ℝ) (hD : D > 1) :
    ∃ c > 0, ∀ n ≥ 2, (u D n : ℝ) ≥ c * n * iteratedLog n

/-- **Swanepoel-Valtr (2004)**

    Improved lower bound: u_D(n) ≫ n · √(log n) for all D > 1.
-/
axiom swanepoel_valtr_bound (D : ℝ) (hD : D > 1) :
    ∃ c > 0, ∀ n ≥ 2, (u D n : ℝ) ≥ c * n * Real.sqrt (Real.log n)

/-- **Upper bound**

    For all D, u_D(n) ≪ n^{4/3}.
-/
axiom upper_bound (D : ℝ) (hD : D > 0) :
    ∃ C > 0, ∀ n : ℕ, (u D n : ℝ) ≤ C * (n : ℝ) ^ (4/3 : ℝ)

/-- **Special case D = √2**

    For the sphere of radius √2, u(n) ≈ n^{4/3} (tight bound).
-/
axiom sqrt2_tight_bound :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ n ≥ 2, c * (n : ℝ) ^ (4/3 : ℝ) ≤ u (Real.sqrt 2) n ∧
               (u (Real.sqrt 2) n : ℝ) ≤ C * (n : ℝ) ^ (4/3 : ℝ)

/-! ## Part VI: Main Theorem -/

/-- The main theorem: Erdős Problem #605 is solved affirmatively. -/
theorem erdos_605_solved : Erdos605Statement := by
  use fun n => Real.sqrt (Real.log n)
  constructor
  · -- f(n) → ∞
    sorry
  · -- Lower bound holds
    intro D hD n hn
    obtain ⟨c, hc, hbound⟩ := swanepoel_valtr_bound D hD
    specialize hbound n (by omega)
    linarith

/-! ## Part VII: The Unit Distance Problem Connection -/

/-- The unit distance problem on spheres asks for the maximum number of
    pairs at distance exactly 1 among n points on a sphere of radius D. -/
def unitDistanceProblem (D : ℝ) (n : ℕ) : ℕ := u D n

/-- For D = 1/2, points can only be at distance ≤ 1, limiting configurations. -/
theorem small_sphere_constraint (n : ℕ) :
    u (1/2) n ≤ n * (n - 1) / 2 := by
  sorry

/-! ## Part VIII: Geometric Constructions -/

/-- Points on a great circle achieve many repeated distances. -/
def greatCircleConfig (n : ℕ) : SphereConfiguration 1 n where
  points := fun i => ![Real.cos (2 * Real.pi * i / n),
                       Real.sin (2 * Real.pi * i / n), 0]
  on_sphere := by sorry
  distinct := by sorry

/-- Regular polyhedra vertices give good configurations. -/
axiom regular_polyhedra_bound (n : ℕ) (hn : n ∈ ({4, 6, 8, 12, 20} : Set ℕ)) :
    ∃ config : SphereConfiguration 1 n, maxRepeatedPairs config ≥ n

/-! ## Part IX: Asymptotic Notation -/

/-- f ≫ g means f(n) ≥ c·g(n) for some c > 0 and large n. -/
def asymptoticallyAtLeast (f g : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, f n ≥ c * g n

/-- f ≈ g means f ≫ g and g ≫ f. -/
def asymptoticallyEqual (f g : ℕ → ℝ) : Prop :=
  asymptoticallyAtLeast f g ∧ asymptoticallyAtLeast g f

/-- The √2 sphere has u(n) ≈ n^{4/3}. -/
theorem sqrt2_asymptotic :
    asymptoticallyEqual (fun n => (u (Real.sqrt 2) n : ℝ))
                        (fun n => (n : ℝ) ^ (4/3 : ℝ)) := by
  constructor
  · obtain ⟨c, C, hc, _, hlower, _⟩ := sqrt2_tight_bound
    exact ⟨c, hc, 2, fun n hn => hlower n hn⟩
  · obtain ⟨c, C, _, hC, _, hupper⟩ := sqrt2_tight_bound
    exact ⟨1/C, by positivity, 2, fun n hn => by
      have := hupper n hn
      linarith⟩

/-! ## Part X: Open Questions -/

/-- Is the √(log n) bound optimal, or can it be improved? -/
def openQuestion_optimal_growth : Prop :=
  ∃ f : ℕ → ℝ, (∀ n, f n ≥ Real.sqrt (Real.log n)) ∧
    asymptoticallyAtLeast (fun n => (u 2 n : ℝ)) (fun n => n * f n)

/-- What happens for spheres of radius exactly 1? -/
def openQuestion_unit_sphere : Prop :=
  ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
    ∀ n ≥ 2, (u 1 n : ℝ) ≥ f n * n

end Erdos605

/-!
## Summary

This file formalizes Erdős Problem #605 on repeated distances on spheres.

**The Problem**: Can n points be placed on a sphere with ≥ f(n)·n pairs
at the same distance, where f(n) → ∞?

**Answer**: YES (solved affirmatively)

**Key Results**:
1. Erdős-Hickerson-Pach (1989): u_D(n) ≫ n·log*(n) for D > 1
2. Swanepoel-Valtr (2004): u_D(n) ≫ n·√(log n) for D > 1
3. For D = √2: u(n) ≈ n^{4/3} (tight bound)
4. Upper bound: u_D(n) ≪ n^{4/3} for all D

**What We Formalize**:
1. Spheres and point configurations in ℝ³
2. Distance pairs and counting
3. The function u_D(n)
4. Main problem statement
5. Known bounds as axioms
6. Asymptotic notation
7. Connection to unit distance problem

**Geometric Insight**: The special radius √2 allows inscribed cubes,
which give particularly good configurations with many repeated distances.

**Open Questions**:
- Is √(log n) the right growth rate?
- What happens for the unit sphere (D = 1)?
- Can the n^{4/3} bound be achieved for all D?
-/
