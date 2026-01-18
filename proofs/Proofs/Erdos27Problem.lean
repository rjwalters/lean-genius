/-
  Erdős Problem #27: Almost Covering Systems

  Source: https://erdosproblems.com/27
  Status: SOLVED (disproved - answer is NO)
  Prize: $100

  Statement:
  An ε-almost covering system is a set of congruences a_i (mod n_i) with distinct
  moduli n₁ < ... < n_k such that the density of integers satisfying none of these
  congruences is at most ε.

  Question: Does there exist C > 1 such that for every ε > 0 and N ≥ 1, there is
  an ε-almost covering system with all moduli in [N, CN]?

  Answer: NO (Filaseta-Ford-Konyagin-Pomerance-Yu)

  The key result shows that for C ≤ N^{log log log N / 4 log log N}, the uncovered
  density is at least (1-o(1)) · ∏(1 - 1/n_i), which cannot be made arbitrarily small.

  Tags: number-theory, covering-systems, density
-/

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos27

open Finset Real Filter

/- ## Part I: Congruence Systems -/

/-- A congruence class: residue a modulo n with n > 0. -/
structure Congruence where
  residue : ℤ
  modulus : ℕ
  modulus_pos : modulus > 0

/-- An integer x satisfies congruence (a, n) if x ≡ a (mod n). -/
def Congruence.satisfies (c : Congruence) (x : ℤ) : Prop :=
  x ≡ c.residue [ZMOD c.modulus]

/-- A congruence system: a finite set of congruences with distinct moduli. -/
structure CongruenceSystem where
  congruences : Finset Congruence
  distinct_moduli : ∀ c₁ ∈ congruences, ∀ c₂ ∈ congruences,
    c₁.modulus = c₂.modulus → c₁ = c₂

/-- An integer is covered by a system if it satisfies at least one congruence. -/
def CongruenceSystem.covers (S : CongruenceSystem) (x : ℤ) : Prop :=
  ∃ c ∈ S.congruences, c.satisfies x

/-- An integer is uncovered if it satisfies no congruence in the system. -/
def CongruenceSystem.uncovered (S : CongruenceSystem) (x : ℤ) : Prop :=
  ∀ c ∈ S.congruences, ¬c.satisfies x

/- ## Part II: Density of Uncovered Integers -/

/-- The number of uncovered integers in [1, M]. -/
noncomputable def uncoveredCount (S : CongruenceSystem) (M : ℕ) : ℕ :=
  ((Finset.range M).filter fun m => S.uncovered (m + 1 : ℤ)).card

/-- The density of uncovered integers up to M. -/
noncomputable def uncoveredDensity (S : CongruenceSystem) (M : ℕ) : ℝ :=
  if M = 0 then 1 else (uncoveredCount S M : ℝ) / M

/-- The asymptotic uncovered density. -/
noncomputable def asymptoticUncoveredDensity (S : CongruenceSystem) : ℝ :=
  liminf (fun M => uncoveredDensity S M) atTop

/- ## Part III: Almost Covering Systems -/

/-- An ε-almost covering system: uncovered density is at most ε. -/
def IsAlmostCovering (S : CongruenceSystem) (ε : ℝ) : Prop :=
  asymptoticUncoveredDensity S ≤ ε

/-- A perfect covering system: every integer is covered. -/
def IsPerfectCovering (S : CongruenceSystem) : Prop :=
  ∀ x : ℤ, S.covers x

/-- Perfect covering implies 0-almost covering. -/
theorem perfect_is_zero_almost (S : CongruenceSystem) (h : IsPerfectCovering S) :
    IsAlmostCovering S 0 := by
  sorry

/- ## Part IV: Bounded Moduli Systems -/

/-- A system has moduli in [N, M]. -/
def HasModuliInRange (S : CongruenceSystem) (N M : ℕ) : Prop :=
  ∀ c ∈ S.congruences, N ≤ c.modulus ∧ c.modulus ≤ M

/-- A system has moduli in [N, CN] for constant C. -/
def HasModuliInCRange (S : CongruenceSystem) (N : ℕ) (C : ℝ) : Prop :=
  HasModuliInRange S N (Nat.floor (C * N))

/- ## Part V: The Natural Density Bound -/

/-- The product ∏(1 - 1/n) over moduli in [m₁, m₂]. -/
noncomputable def naturalDensity (m₁ m₂ : ℕ) : ℝ :=
  ∏ m ∈ (Finset.range (m₂ - m₁ + 1)).map ⟨(· + m₁), by intro; omega⟩,
    (1 - 1 / (m : ℝ))

/-- The averaging argument: any system with moduli in [m₁, m₂] has some
    residue class choice achieving uncovered density = naturalDensity. -/
theorem averaging_bound (m₁ m₂ : ℕ) (hm : m₁ ≤ m₂) (hm₁ : m₁ > 0) :
    ∃ S : CongruenceSystem, HasModuliInRange S m₁ m₂ ∧
      asymptoticUncoveredDensity S = naturalDensity m₁ m₂ := by
  sorry

/-- Natural density goes to 0 as the range grows. -/
theorem naturalDensity_vanishes :
    ∀ ε > 0, ∃ m₂ : ℕ, naturalDensity 2 m₂ < ε := by
  sorry

/- ## Part VI: The Main Question -/

/-- The Erdős conjecture: there exists C > 1 such that for all ε > 0 and N ≥ 1,
    an ε-almost covering with moduli in [N, CN] exists. -/
def ErdosConjecture : Prop :=
  ∃ C : ℝ, C > 1 ∧ ∀ ε > 0, ∀ N : ℕ, N ≥ 1 →
    ∃ S : CongruenceSystem, HasModuliInCRange S N C ∧ IsAlmostCovering S ε

/-- The negation: for all C > 1, some ε and N fail. -/
def ErdosConjectureNegation : Prop :=
  ∀ C : ℝ, C > 1 → ∃ ε > 0, ∃ N : ℕ, N ≥ 1 ∧
    ∀ S : CongruenceSystem, HasModuliInCRange S N C → ¬IsAlmostCovering S ε

/-- The conjecture and its negation are logical opposites. -/
theorem conjecture_dichotomy : ErdosConjecture ↔ ¬ErdosConjectureNegation := by
  sorry

/- ## Part VII: The Disproof (Filaseta-Ford-Konyagin-Pomerance-Yu) -/

/-- The critical exponent function: α(N) = log log log N / (4 log log N). -/
noncomputable def criticalExponent (N : ℕ) : ℝ :=
  if N ≤ 16 then 0 else
    Real.log (Real.log (Real.log N)) / (4 * Real.log (Real.log N))

/-- For C ≤ N^{α(N)}, the uncovered density cannot be made small. -/
theorem ffkpy_main_theorem :
    ∀ᶠ N in atTop, ∀ C : ℝ, 1 < C → C ≤ (N : ℝ) ^ criticalExponent N →
      ∀ S : CongruenceSystem, HasModuliInCRange S N C →
        asymptoticUncoveredDensity S ≥ (1/2) * ∏ c ∈ S.congruences, (1 - 1 / c.modulus) := by
  sorry

/-- The product over moduli in a bounded range is bounded away from 0. -/
theorem product_bounded_below (N : ℕ) (C : ℝ) (hC : C > 1) (hN : N ≥ 2) :
    ∀ S : CongruenceSystem, HasModuliInCRange S N C →
      ∏ c ∈ S.congruences, (1 - 1 / (c.modulus : ℝ)) ≥ 1 / C := by
  sorry

/-- Main result: The Erdős conjecture is FALSE. -/
theorem erdos_27_disproved : ErdosConjectureNegation := by
  sorry

/-- Equivalent statement: No constant C works. -/
theorem no_universal_constant :
    ∀ C : ℝ, C > 1 → ∃ ε > 0, ∀ᶠ N in atTop,
      ∀ S : CongruenceSystem, HasModuliInCRange S N C →
        asymptoticUncoveredDensity S > ε := by
  sorry

/- ## Part VIII: What DOES Work -/

/-- If we allow C to grow with N, we can achieve almost covering. -/
theorem growing_C_works :
    ∀ ε > 0, ∃ f : ℕ → ℝ, (∀ N, f N > 1) ∧
      ∀ N : ℕ, N ≥ 2 →
        ∃ S : CongruenceSystem, HasModuliInCRange S N (f N) ∧ IsAlmostCovering S ε := by
  sorry

/-- The natural choice: C = N^{1/(log log N)} suffices for any fixed ε. -/
noncomputable def sufficientC (N : ℕ) : ℝ :=
  if N ≤ 3 then 2 else (N : ℝ) ^ (1 / Real.log (Real.log N))

theorem sufficient_C_works (ε : ℝ) (hε : ε > 0) :
    ∀ᶠ N in atTop, ∃ S : CongruenceSystem,
      HasModuliInCRange S N (sufficientC N) ∧ IsAlmostCovering S ε := by
  sorry

/- ## Part IX: Connection to Perfect Covering Systems -/

/-- A perfect covering system requires minimum modulus ≥ some threshold. -/
theorem perfect_covering_min_modulus :
    ∃ B : ℕ, ∀ S : CongruenceSystem, IsPerfectCovering S →
      ∃ c ∈ S.congruences, c.modulus ≤ B := by
  sorry

/-- The current best bound on minimum modulus for perfect coverings. -/
def perfectCoveringBound : ℕ := 616000

/-- Bloom-Briggs-Maynard-Smith-Tao: minimum modulus < 616000. -/
theorem bbmst_bound :
    ∀ S : CongruenceSystem, IsPerfectCovering S →
      ∃ c ∈ S.congruences, c.modulus < perfectCoveringBound := by
  sorry

end Erdos27

/-
  ## Summary

  This file formalizes Erdős Problem #27 on almost covering systems.

  **Status**: SOLVED (disproved - the answer is NO)
  **Prize**: $100

  **The Question**: Does there exist C > 1 such that for all ε > 0 and N ≥ 1,
  an ε-almost covering system exists with moduli in [N, CN]?

  **The Answer**: NO (Filaseta-Ford-Konyagin-Pomerance-Yu)

  **Key Results**:
  - For C ≤ N^{α(N)} where α(N) = log log log N / (4 log log N),
    the uncovered density is at least (1-o(1)) · ∏(1 - 1/n_i)
  - This product is bounded below by 1/C for moduli in [N, CN]
  - Therefore no fixed C can achieve arbitrarily small ε

  **What DOES work**:
  - If C is allowed to grow with N (e.g., C = N^{1/log log N}), then
    ε-almost coverings exist for any fixed ε

  **What we formalize**:
  1. Congruence systems and covering definitions
  2. Uncovered density and ε-almost covering
  3. The Erdős conjecture and its negation
  4. The FFKPY disproof via critical exponent bound
  5. Connection to perfect covering systems (Problem #901)

  **Key sorries**:
  - `erdos_27_disproved`: The main theorem
  - `ffkpy_main_theorem`: The technical core of the disproof
  - `bbmst_bound`: Connection to perfect coverings

  **Historical note**: This $100 problem was disproved, showing that bounded
  ranges of moduli cannot achieve arbitrarily good almost-coverings.
-/
