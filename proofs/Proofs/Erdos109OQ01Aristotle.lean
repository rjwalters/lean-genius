/-
  Aristotle targets for Erdos109OQ01
  Routine supporting lemmas for automated proof search.
  See Erdos109OQ01.lean for the main formalization.

  Targets:
  - syndetic_infinite: A syndetic set is infinite
    Key: for every n, the gap condition gives m ∈ S with m ≥ n+1,
    so S is unbounded above, hence infinite (Set.infinite_of_not_bddAbove).
  - syndetic_nonempty: Immediate from gap condition at n=0.
  - thick_nonempty: Immediate from run condition at g=0.

  Not targeted (too deep for automated search):
  - posUpperDensity_piecewiseSyndetic: requires ergodic theory
  - sumset_density_constraint: requires density comparison
  - posUpperDensity_contains_IP: requires Hindman's theorem
  - ip_set_sumset_structure: requires FS set construction
-/
import Mathlib

namespace Erdos109OQ01

/-- A set S ⊆ ℕ is syndetic if the gaps between consecutive elements are bounded. -/
def IsSyndetic (S : Set ℕ) : Prop :=
  ∃ g : ℕ, ∀ n : ℕ, ∃ m ∈ S, n ≤ m ∧ m ≤ n + g

/-- A set S ⊆ ℕ is thick if it contains arbitrarily long runs. -/
def IsThick (S : Set ℕ) : Prop :=
  ∀ g : ℕ, ∃ n : ℕ, ∀ m : ℕ, n ≤ m → m ≤ n + g → m ∈ S

/-- A syndetic set is nonempty. -/
theorem syndetic_nonempty (S : Set ℕ) (hS : IsSyndetic S) : S.Nonempty := by
  obtain ⟨g, hg⟩ := hS
  obtain ⟨m, hm, _, _⟩ := hg 0
  exact ⟨m, hm⟩

/-- A thick set is nonempty. -/
theorem thick_nonempty (S : Set ℕ) (hS : IsThick S) : S.Nonempty := by
  obtain ⟨n, hn⟩ := hS 0
  exact ⟨n, hn n (le_refl n) (by omega)⟩

/-- Syndetic sets are infinite.
    Key: for every n, the syndetic gap condition gives m ∈ S with m ≥ n+1,
    so S is not bounded above, hence infinite. -/
theorem syndetic_infinite (S : Set ℕ) (hS : IsSyndetic S) : S.Infinite := by
  obtain ⟨g, hg⟩ := hS
  apply Set.infinite_of_not_bddAbove
  rw [not_bddAbove_iff]
  intro n
  obtain ⟨m, hm, hnm, _⟩ := hg n
  exact ⟨m, hm, hnm⟩

end Erdos109OQ01
