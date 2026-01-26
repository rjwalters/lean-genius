/-!
# Erdős Problem #1120 — Shortest Path in Polynomial Sublevel Sets

Let f ∈ ℂ[z] be monic of degree n with all roots in the unit disk.
Define E = {z : |f(z)| ≤ 1}. What is the shortest path in E
connecting z = 0 to |z| = 1?

For f(z) = z^n, the path length is 1 (the segment [0,1]).

Erdős conjectured the minimum path length tends to ∞ with n,
but not too fast.

Status: OPEN
Reference: https://erdosproblems.com/1120
Halász Problem 4.22
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Nat.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A monic polynomial of degree n with roots in the closed unit disk. -/
structure UnitRootedPoly (n : ℕ) where
  roots : Fin n → ℂ
  roots_in_disk : ∀ i, Complex.abs (roots i) ≤ 1

/-- The sublevel set E = {z ∈ ℂ : |f(z)| ≤ 1}. -/
def sublevelSet (p : UnitRootedPoly n) : Set ℂ :=
  {z : ℂ | Complex.abs (Finset.univ.prod (fun i => z - p.roots i)) ≤ 1}

/-- The shortest path length in E from the origin to the unit circle. -/
noncomputable def shortestPathLength (p : UnitRootedPoly n) : ℝ :=
  sInf {L : ℝ | ∃ γ : Set.Icc (0 : ℝ) 1 → ℂ,
    γ ⟨0, le_refl 0, zero_le_one⟩ = 0 ∧
    Complex.abs (γ ⟨1, zero_le_one, le_refl 1⟩) = 1 ∧
    (∀ t, (γ t) ∈ sublevelSet p) ∧
    L ≥ 0}  -- simplified; full definition needs arc length

/-- The worst-case shortest path for degree n. -/
noncomputable def worstCasePathLength (n : ℕ) : ℝ :=
  sSup {shortestPathLength p | p : UnitRootedPoly n}

/-! ## Main Problem -/

/-- **Erdős Problem #1120**: the worst-case shortest path length tends
    to ∞ with n. That is, for large n, any monic polynomial with roots
    in the disk forces a long path in E from 0 to |z| = 1. -/
axiom erdos_1120_conjecture :
  ∀ M : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, worstCasePathLength n ≥ M

/-! ## Known Results -/

/-- **Trivial Lower Bound**: for f(z) = z^n, E contains the closed
    unit disk, so the path length is 1. -/
axiom trivial_lower : ∀ n : ℕ, n > 0 → worstCasePathLength n ≥ 1

/-- **Clunie–Netanyahu**: such a path always exists in E. The sublevel
    set is connected enough to contain a path from 0 to the unit circle. -/
axiom clunie_netanyahu_existence (n : ℕ) (p : UnitRootedPoly n) :
  ∃ L : ℝ, L > 0 ∧ shortestPathLength p ≤ L

/-- **Growth Conjecture**: Erdős conjectured the growth is slow —
    "tending to infinity, but not too fast." -/
axiom slow_growth_conjecture :
  ∃ f : ℕ → ℝ, (∀ n, f n ≤ n) ∧
    ∀ n : ℕ, n > 0 → worstCasePathLength n ≤ f n

/-! ## Observations -/

/-- **Connection to Problem #1041**: Problem #1041 concerns related
    questions about polynomial sublevel sets and covering by disks. -/
axiom connection_1041 : True

/-- **Lemniscate Geometry**: E is a lemniscate — a level set of |f|.
    Its topology depends on the root configuration. When roots cluster,
    E can have thin necks forcing longer paths. -/
axiom lemniscate_geometry : True
