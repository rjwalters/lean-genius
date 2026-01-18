/-
  Erdős Problem #202: Disjoint Covering Systems

  Source: https://erdosproblems.com/202
  Status: OPEN (asymptotic behavior not fully determined)

  Statement:
  Let n₁ < ⋯ < n_r ≤ N with associated residues a_i (mod n_i) such that the
  congruence classes are disjoint (every integer satisfies at most one
  congruence). How large can r be in terms of N?

  Define f(N) = maximum such r.

  Known Results:
  - Erdős-Stein Conjecture: f(N) = o(N) [PROVED by Erdős-Szemerédi 1968]
  - Erdős-Szemerédi (1968): N/exp((log N)^{1/2+ε}) ≪ f(N) < N/(log N)^c
  - Croot (2003): N/L(N)^{√2+o(1)} < f(N) < N/L(N)^{1/6-o(1)}
  - Chen (2005), de la Bretèche-Ford-Vandehey (2013):
      N/L(N)^{1+o(1)} < f(N) < N/L(N)^{√3/2+o(1)}
    where L(N) = exp(√(log N · log log N))

  The lower bound is conjectured to be the truth.

  Tags: number-theory, covering-systems, combinatorics
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos202

open Finset Real

/- ## Part I: Congruence Classes -/

/-- A congruence class: residue a modulo n. -/
structure CongruenceClass where
  residue : ℤ
  modulus : ℕ
  modulus_pos : modulus > 0

/-- An integer x belongs to congruence class (a, n) if x ≡ a (mod n). -/
def CongruenceClass.contains (c : CongruenceClass) (x : ℤ) : Prop :=
  x ≡ c.residue [ZMOD c.modulus]

/-- Two congruence classes are disjoint if no integer belongs to both. -/
def AreDisjoint (c₁ c₂ : CongruenceClass) : Prop :=
  ∀ x : ℤ, ¬(c₁.contains x ∧ c₂.contains x)

/- ## Part II: Disjoint Systems -/

/-- A disjoint system: a finite set of pairwise disjoint congruence classes. -/
structure DisjointSystem where
  classes : Finset CongruenceClass
  pairwise_disjoint : ∀ c₁ ∈ classes, ∀ c₂ ∈ classes, c₁ ≠ c₂ → AreDisjoint c₁ c₂

/-- The moduli of a disjoint system. -/
def DisjointSystem.moduli (S : DisjointSystem) : Finset ℕ :=
  S.classes.image CongruenceClass.modulus

/-- A disjoint system has moduli bounded by N. -/
def DisjointSystem.boundedBy (S : DisjointSystem) (N : ℕ) : Prop :=
  ∀ c ∈ S.classes, c.modulus ≤ N

/-- The size of a disjoint system. -/
def DisjointSystem.size (S : DisjointSystem) : ℕ :=
  S.classes.card

/- ## Part III: The Function f(N) -/

/-- f(N) = maximum size of a disjoint system with moduli ≤ N. -/
noncomputable def f (N : ℕ) : ℕ :=
  sSup {r : ℕ | ∃ S : DisjointSystem, S.boundedBy N ∧ S.size = r}

/-- f is monotone: larger N allows more classes. -/
theorem f_mono {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) : f N₁ ≤ f N₂ := by
  sorry

/- ## Part IV: Basic Bounds -/

/-- Trivial upper bound: f(N) ≤ N since moduli must be distinct positive integers ≤ N. -/
theorem f_le_N (N : ℕ) : f N ≤ N := by
  sorry

/-- The Chinese Remainder Theorem gives a lower bound construction. -/
theorem f_lower_trivial (N : ℕ) (hN : N ≥ 2) : f N ≥ 1 := by
  sorry

/- ## Part V: The L Function -/

/-- L(N) = exp(√(log N · log log N)), the key function in the bounds. -/
noncomputable def L (N : ℕ) : ℝ :=
  if N ≤ 2 then 1 else
    Real.exp (Real.sqrt (Real.log N * Real.log (Real.log N)))

/-- L is monotonically increasing for large N. -/
theorem L_mono {N₁ N₂ : ℕ} (hN₁ : N₁ ≥ 3) (h : N₁ ≤ N₂) : L N₁ ≤ L N₂ := by
  sorry

/-- L grows slower than any power of N. -/
theorem L_subpolynomial (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ N in Filter.atTop, L N < (N : ℝ) ^ ε := by
  sorry

/-- L grows faster than any power of log N. -/
theorem L_superlogarithmic (c : ℝ) :
    ∀ᶠ N in Filter.atTop, (Real.log N) ^ c < L N := by
  sorry

/- ## Part VI: The Erdős-Stein Conjecture (PROVED) -/

/-- Erdős-Stein Conjecture: f(N) = o(N).

This was proved by Erdős and Szemerédi in 1968.
-/
theorem erdos_stein_conjecture :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop, (f N : ℝ) < ε * N := by
  sorry

/-- Erdős-Szemerédi (1968): f(N) < N / (log N)^c for some c > 0. -/
theorem erdos_szemeredi_upper :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in Filter.atTop,
      (f N : ℝ) < N / (Real.log N) ^ c := by
  sorry

/- ## Part VII: Modern Bounds -/

/-- Current best upper bound (de la Bretèche-Ford-Vandehey 2013):
    f(N) < N / L(N)^{√3/2 - o(1)}. -/
theorem upper_bound_BFV :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (f N : ℝ) < N / (L N) ^ (Real.sqrt 3 / 2 - ε) := by
  sorry

/-- Current best lower bound (Chen 2005, de la Bretèche-Ford-Vandehey 2013):
    f(N) > N / L(N)^{1 + o(1)}. -/
theorem lower_bound_BFV :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (f N : ℝ) > N / (L N) ^ (1 + ε) := by
  sorry

/-- The conjectured truth: f(N) = N / L(N)^{1 + o(1)}. -/
def ExactAsymptoticConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ N in Filter.atTop,
    N / (L N) ^ (1 + ε) < (f N : ℝ) ∧ (f N : ℝ) < N / (L N) ^ (1 - ε)

/- ## Part VIII: Historical Bounds -/

/-- Croot (2003) lower bound: f(N) > N / L(N)^{√2 + o(1)}. -/
theorem croot_lower :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (f N : ℝ) > N / (L N) ^ (Real.sqrt 2 + ε) := by
  sorry

/-- Croot (2003) upper bound: f(N) < N / L(N)^{1/6 - o(1)}. -/
theorem croot_upper :
    ∀ ε > 0, ∀ᶠ N in Filter.atTop,
      (f N : ℝ) < N / (L N) ^ (1/6 - ε) := by
  sorry

/- ## Part IX: Examples -/

/-- For N = 6, we can achieve r = 3 with classes 0 mod 2, 1 mod 4, 3 mod 6.
    These cover 0,2,4,... and 1,5,9,... and 3,9,15,... which are disjoint. -/
theorem example_N6 : f 6 ≥ 3 := by
  sorry

/-- The density of covered integers in a disjoint system. -/
noncomputable def coveringDensity (S : DisjointSystem) : ℝ :=
  (S.classes.sum fun c => (1 : ℝ) / c.modulus)

/-- A disjoint system can cover at most density 1. -/
theorem covering_density_le_one (S : DisjointSystem) :
    coveringDensity S ≤ 1 := by
  sorry

end Erdos202

/-
  ## Summary

  This file formalizes Erdős Problem #202 on disjoint covering systems.

  **Status**: OPEN (exact asymptotics not determined)

  **The Problem**: For moduli n₁ < ⋯ < n_r ≤ N with disjoint congruence
  classes, how large can r be?

  **Key Results**:
  - Erdős-Stein Conjecture: f(N) = o(N) [PROVED]
  - Erdős-Szemerédi (1968): First proof of the conjecture
  - Croot (2003): N/L(N)^{√2+o(1)} < f(N) < N/L(N)^{1/6-o(1)}
  - BFV (2013): N/L(N)^{1+o(1)} < f(N) < N/L(N)^{√3/2+o(1)}

  where L(N) = exp(√(log N · log log N))

  **Conjecture**: The lower bound is tight: f(N) = N/L(N)^{1+o(1)}

  **What we formalize**:
  1. Congruence classes and disjoint systems
  2. The function f(N)
  3. The L(N) function and its growth properties
  4. The Erdős-Stein conjecture (as a theorem)
  5. Historical bounds: Erdős-Szemerédi, Croot, BFV

  **Key sorries**:
  - `erdos_stein_conjecture`: The 1968 result
  - `lower_bound_BFV`, `upper_bound_BFV`: Current best bounds
  - `covering_density_le_one`: Density constraint

  **Open question**: Close the gap between L(N)^{1+o(1)} and L(N)^{√3/2+o(1)}
-/
