/-
  Erdős Problem #109 Open Question 1:
  Can we find B, C with specific gap conditions?

  The Moreira-Richter-Robertson proof (2019) shows that for any A ⊆ ℕ
  with positive upper density, A contains B + C with B, C infinite.
  The stronger version (also proved) shows B can have arbitrarily large gaps.

  This file explores:
  1. Syndetic sumsets: can B be chosen to be syndetic (bounded gaps)?
  2. The gap function for the sumset decomposition
  3. Specific gap conditions and their implications
  4. Connection to IP sets and Hindman's theorem

  References:
  - Moreira, Richter, Robertson (2019): proved the conjecture
  - Hindman (1974): IP sets and infinite sumsets
  - Parent: Erdos109Problem.lean
-/

import Mathlib

open Finset BigOperators

namespace Erdos109OQ01

/-
## Part I: Preliminaries (from parent, restated for import independence)
-/

noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => ((A ∩ Set.Icc 1 N).ncard : ℝ) / N) Filter.atTop

def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < upperDensity A

def Sumset (B C : Set ℕ) : Set ℕ :=
  { n | ∃ b ∈ B, ∃ c ∈ C, n = b + c }

scoped notation:65 B " +ₛ " C => Sumset B C

/-
## Part II: Gap Conditions
-/

/-- A set S ⊆ ℕ is syndetic if the gaps between consecutive elements are bounded.
    Formally: there exists g such that for all n, S ∩ [n, n+g] ≠ ∅. -/
def IsSyndetic (S : Set ℕ) : Prop :=
  ∃ g : ℕ, ∀ n : ℕ, ∃ m ∈ S, n ≤ m ∧ m ≤ n + g

/-- A set S ⊆ ℕ is thick if it contains arbitrarily long runs.
    Formally: for all g, there exists n such that [n, n+g] ⊆ S. -/
def IsThick (S : Set ℕ) : Prop :=
  ∀ g : ℕ, ∃ n : ℕ, ∀ m : ℕ, n ≤ m → m ≤ n + g → m ∈ S

/-- A set is piecewise syndetic if it is the intersection of a
    syndetic set and a thick set. Equivalently, it has bounded gaps
    along arbitrarily long intervals. -/
def IsPiecewiseSyndetic (S : Set ℕ) : Prop :=
  ∃ T : Set ℕ, IsSyndetic T ∧ IsThick (S ∩ T)

/-- Any set of positive upper density is piecewise syndetic.
    (This is a standard result in additive combinatorics.) -/
theorem posUpperDensity_piecewiseSyndetic (A : Set ℕ) (h : HasPositiveUpperDensity A) :
    IsPiecewiseSyndetic A := by
  sorry

/-- Syndetic sets are infinite. -/
theorem syndetic_infinite (S : Set ℕ) (hS : IsSyndetic S) : S.Infinite := by
  obtain ⟨g, hg⟩ := hS
  rw [Set.infinite_coe_iff]
  intro hfin
  -- If S is finite, let M = max S. Then S ∩ [M+1, M+1+g] = ∅, contradiction.
  sorry

/-
## Part III: Sumset Gap Strengthening
-/

/-- **Gap-controlled sumset conjecture**: If A has positive upper density,
    then for any gap function f : ℕ → ℕ, there exist infinite B, C with
    B + C ⊆ A and the elements of B have gaps at least f.

    This is stated in the parent as `StrongerSumsetConjecture` and was
    proved by Moreira-Richter-Robertson. -/
def GapControlledSumset : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∀ f : ℕ → ℕ, (∀ n, f n > 0) →
      ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ A ∧
        ∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → b₁ < b₂ → b₂ - b₁ ≥ f b₁

/-- **Syndetic sumset question (OPEN)**: Can B be chosen to be syndetic?
    If true, this would mean the sumset decomposition can be found with
    bounded gaps in both B and C.

    Note: This is likely FALSE in general. A set of positive density
    can have density < 1, so it has large gaps, and B + C ⊆ A forces
    B and C to "fit" within A's structure. -/
def SyndeticSumsetQuestion : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∃ B C : Set ℕ, IsSyndetic B ∧ C.Infinite ∧ (B +ₛ C) ⊆ A

/-- If A has positive density, B is syndetic, and B + C ⊆ A,
    then C cannot have density larger than A. -/
theorem sumset_density_constraint (A B C : Set ℕ)
    (hA : HasPositiveUpperDensity A)
    (hB : IsSyndetic B) (hBC : (B +ₛ C) ⊆ A) :
    upperDensity C ≤ upperDensity A := by
  sorry

/-
## Part IV: Connection to IP Sets (Hindman's Theorem)
-/

/-- An IP set is a set containing all finite sums from some infinite sequence.
    FS(x₁, x₂, ...) = { xᵢ₁ + xᵢ₂ + ... + xᵢₖ : i₁ < i₂ < ... < iₖ }. -/
def IsIPSet (S : Set ℕ) : Prop :=
  ∃ x : ℕ → ℕ, (∀ i, 0 < x i) ∧ StrictMono x ∧
    ∀ F : Finset ℕ, F.Nonempty → (∑ i ∈ F, x i) ∈ S

/-- **Hindman's theorem** (1974): In any finite coloring of ℕ,
    one color class contains an IP set.
    This is stronger than the sumset conjecture in some ways. -/
axiom hindman_theorem (k : ℕ) (coloring : ℕ → Fin k) :
    ∃ c : Fin k, IsIPSet { n | coloring n = c }

/-- Any set of positive upper density contains an IP set.
    This follows from Hindman's theorem applied to the characteristic
    function of A (restricted to the dense part). -/
theorem posUpperDensity_contains_IP (A : Set ℕ) (h : HasPositiveUpperDensity A) :
    ∃ S : Set ℕ, IsIPSet S ∧ S ⊆ A := by
  sorry

/-- An IP set B generates a sumset: B + B ⊆ B.
    More precisely, the FS set is closed under certain sums. -/
theorem ip_set_sumset_structure (S : Set ℕ) (hS : IsIPSet S) :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ S := by
  sorry

/-
## Part V: Summary
-/

/-
## What's Proved
- Gap conditions (syndetic, thick, piecewise syndetic) defined
- Gap-controlled sumset conjecture stated (matching parent's StrongerSumsetConjecture)
- Syndetic sumset question stated (OPEN — likely false)
- IP set definition and Hindman's theorem (axiomatized)
- Connection between density, IP sets, and sumset decomposition

## Axioms: 1 (Hindman's theorem)
## Sorries: 5 (density→piecewise syndetic, syndetic infinite, density constraint,
##              density→IP, IP→sumset structure)

## Mathematical Status
- The Moreira-Richter-Robertson proof uses ergodic theory (measure-preserving
  systems, Furstenberg correspondence). The proof techniques are deep and
  currently beyond Lean formalization.
- The specific gap conditions question (OQ-01) remains partially open:
  arbitrary gap functions YES (proved), syndetic B unclear (likely NO).
-/

end Erdos109OQ01
