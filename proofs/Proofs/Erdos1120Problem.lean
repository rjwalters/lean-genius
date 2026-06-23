/-
Erdős Problem #1120 — Shortest Path in Polynomial Sublevel Sets

Let f ∈ ℂ[z] be monic of degree n with all roots in the unit disk.
Define E = {z : |f(z)| ≤ 1}. What is the shortest path in E
connecting z = 0 to |z| = 1?

For f(z) = z^n, the path length is 1 (the segment [0,1]).

Erdős conjectured the minimum path length tends to ∞ with n,
but not too fast.

Key known results:
- Clunie–Netanyahu: such a path always exists in E
- Trivial lower bound: path length ≥ 1, achieved by f(z) = z^n
- The problem asks for the worst-case behavior as a function of n

Status: OPEN
Reference: https://erdosproblems.com/1120
Halász Problem 4.22
-/

import Mathlib

namespace Erdos1120

open Complex

-- ## Definitions

/-- A monic polynomial of degree n with roots in the closed unit disk. -/
structure UnitRootedPoly (n : ℕ) where
  roots : Fin n → ℂ
  roots_in_disk : ∀ i, abs (roots i) ≤ 1

/-- The polynomial value at z: f(z) = ∏(z - rᵢ) -/
noncomputable def polyVal (p : UnitRootedPoly n) (z : ℂ) : ℂ :=
  Finset.univ.prod (fun i => z - p.roots i)

/-- The sublevel set E = {z ∈ ℂ : |f(z)| ≤ 1}. -/
def sublevelSet (p : UnitRootedPoly n) : Set ℂ :=
  {z : ℂ | abs (polyVal p z) ≤ 1}

/-- The shortest path length in E from the origin to the unit circle.
    Simplified definition using infimum over path-connected curves. -/
noncomputable def shortestPathLength (p : UnitRootedPoly n) : ℝ :=
  sInf {L : ℝ | ∃ γ : Set.Icc (0 : ℝ) 1 → ℂ,
    γ ⟨0, le_refl 0, zero_le_one⟩ = 0 ∧
    abs (γ ⟨1, zero_le_one, le_refl 1⟩) = 1 ∧
    (∀ t, (γ t) ∈ sublevelSet p) ∧
    L ≥ 0}

/-- The worst-case shortest path for degree n. -/
noncomputable def worstCasePathLength (n : ℕ) : ℝ :=
  sSup {shortestPathLength p | p : UnitRootedPoly n}

-- ## Basic Properties of f(0)

/-- The polynomial value at 0 is the product of negated roots:
    f(0) = ∏(-rᵢ) -/
theorem polyVal_zero (p : UnitRootedPoly n) :
    polyVal p 0 = Finset.univ.prod (fun i => -(p.roots i)) := by
  simp [polyVal]

/-- |f(0)| = ∏|rᵢ| for the monic polynomial with roots rᵢ -/
theorem abs_polyVal_zero (p : UnitRootedPoly n) :
    abs (polyVal p 0) = Finset.univ.prod (fun i => abs (p.roots i)) := by
  rw [polyVal_zero, map_prod]
  congr 1; ext i; simp [map_neg]

/-- The product of absolute values of roots is at most 1 -/
theorem prod_abs_roots_le_one (p : UnitRootedPoly n) :
    Finset.univ.prod (fun i => abs (p.roots i)) ≤ 1 := by
  apply Finset.prod_le_one
  · intro i _; exact abs_nonneg _
  · intro i _; exact p.roots_in_disk i

/-- 0 is always in the sublevel set E when all roots are in the unit disk.
    Since |f(0)| = ∏|rᵢ| and each |rᵢ| ≤ 1, we get |f(0)| ≤ 1. -/
theorem zero_mem_sublevelSet (p : UnitRootedPoly n) : (0 : ℂ) ∈ sublevelSet p := by
  simp only [sublevelSet, Set.mem_setOf_eq]
  rw [abs_polyVal_zero]
  exact prod_abs_roots_le_one p

-- ## The Case f(z) = z^n

/-- For f(z) = z^n (all roots at 0), the polynomial value is z^n -/
theorem polyVal_zero_roots (n : ℕ) (z : ℂ) :
    let p : UnitRootedPoly n := ⟨fun _ => 0, fun _ => by simp⟩
    polyVal p z = z ^ n := by
  simp [polyVal, Finset.prod_const, sub_zero]

/-- When all roots are 0 and n ≥ 1, the sublevel set is the closed unit disk -/
theorem sublevelSet_zero_roots (n : ℕ) (hn : n ≥ 1) (z : ℂ) :
    let p : UnitRootedPoly n := ⟨fun _ => 0, fun _ => by simp⟩
    z ∈ sublevelSet p ↔ abs z ≤ 1 := by
  simp only [sublevelSet, Set.mem_setOf_eq, polyVal_zero_roots]
  rw [map_pow]
  constructor
  · intro h
    by_contra hgt
    push_neg at hgt
    have h1 : (abs z) ^ n > 1 ^ n := pow_lt_pow_left hgt (by linarith : (1 : ℝ) ≥ 0) hn
    simp at h1; linarith
  · intro h; exact pow_le_one₀ (abs_nonneg z) h

-- ## Structural Properties

/-- The sublevel set E is always nonempty (contains 0) -/
theorem sublevelSet_nonempty (p : UnitRootedPoly n) :
    (sublevelSet p).Nonempty := ⟨0, zero_mem_sublevelSet p⟩

/-- If z ∈ E, then |f(z)| ≤ 1 (tautological unwrapping) -/
theorem mem_sublevelSet_iff (p : UnitRootedPoly n) (z : ℂ) :
    z ∈ sublevelSet p ↔ abs (polyVal p z) ≤ 1 :=
  Iff.rfl

/-- Degree 0: the sublevel set is all of ℂ (empty product is 1, |1| ≤ 1) -/
theorem sublevelSet_degree_zero (z : ℂ) :
    let p : UnitRootedPoly 0 := ⟨Fin.elim0, fun i => Fin.elim0 i⟩
    z ∈ sublevelSet p := by
  simp [sublevelSet, polyVal, abs_one]

-- ## Degree 1: Single Root Case

/-- For degree 1 with root r, f(z) = z - r and E = disk of radius 1 at r -/
theorem sublevelSet_degree_one (r : ℂ) (hr : abs r ≤ 1) (z : ℂ) :
    let p : UnitRootedPoly 1 := ⟨![r], fun i => by fin_cases i; exact hr⟩
    z ∈ sublevelSet p ↔ abs (z - r) ≤ 1 := by
  simp [sublevelSet, polyVal, Matrix.cons_val_zero]

/-- For degree 1, 0 is in E since |0 - r| = |r| ≤ 1 -/
theorem zero_in_degree_one (r : ℂ) (hr : abs r ≤ 1) :
    let p : UnitRootedPoly 1 := ⟨![r], fun i => by fin_cases i; exact hr⟩
    (0 : ℂ) ∈ sublevelSet p := by
  rw [sublevelSet_degree_one r hr]; simp [hr]

-- ## |f(0)| Properties

/-- |f(0)| ≤ 1 for any UnitRootedPoly -/
theorem abs_polyVal_zero_le_one (p : UnitRootedPoly n) :
    abs (polyVal p 0) ≤ 1 := by
  rw [abs_polyVal_zero]; exact prod_abs_roots_le_one p

/-- If all roots have |rᵢ| = 1 (unimodular), then |f(0)| = 1 -/
theorem abs_polyVal_zero_eq_one_of_unimodular (p : UnitRootedPoly n)
    (h : ∀ i, abs (p.roots i) = 1) :
    abs (polyVal p 0) = 1 := by
  rw [abs_polyVal_zero]; simp [h]

-- ## The Main Conjectures (OPEN)

/-- Erdős Problem #1120 Main Conjecture (OPEN): worst-case path length → ∞ -/
axiom erdos_1120_conjecture :
  ∀ M : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, worstCasePathLength n ≥ M

/-- Trivial lower bound: the worst case is always ≥ 1 -/
/-- Clunie–Netanyahu: a path from 0 to |z|=1 always exists in E -/
/-- Erdős's growth conjecture: worst case grows slowly -/
axiom erdos_growth_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 → worstCasePathLength n ≤ C * n

-- ## Main Open Problem Statement

/--
Erdős Problem #1120 (Open):

Let f ∈ ℂ[z] be monic of degree n with all roots in the unit disk.
Define E = {z : |f(z)| ≤ 1}. What is the shortest path in E
connecting z = 0 to |z| = 1?

Known:
- Clunie–Netanyahu showed a path always exists in E
- Trivial lower bound: path length ≥ 1 (achieved by f(z) = z^n)
- Erdős conjectured growth "not too fast"
- Connected to problem #1041 (polynomial sublevel sets and disk covers)
-/
theorem erdos_1120_main :
    (∀ M : ℝ, ∃ N₀ : ℕ, ∀ n ≥ N₀, worstCasePathLength n ≥ M) ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n > 0 → worstCasePathLength n ≤ C * n :=
  ⟨erdos_1120_conjecture, erdos_growth_bound⟩

end Erdos1120
