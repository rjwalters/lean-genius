/-
  Aristotle targets for Erdős Problem #357
  Routine supporting lemmas for automated proof search.
  See Erdos357Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (f(n) = o(n))
  - NOT the deep results (Weisenberg, Hegyvári — axiomatized in main file)
  - Routine supporting facts: monotonicity of f/g/h, logical implications,
    set containment arguments
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos357Aristotle

open Nat Filter Asymptotics Finset

/-- A sequence has distinct consecutive sums: all contiguous interval sums differ. -/
def HasDistinctSums' (a : Fin k → ℤ) : Prop :=
  ∀ I J : Finset (Fin k), I.val.toFinset.OrdConnected → J.val.toFinset.OrdConnected →
    (∑ i ∈ I, a i) = (∑ j ∈ J, a j) → I = J

/-- A valid sequence for f(n): strictly increasing integers in [1, n] with distinct sums. -/
def IsValidSequence (n k : ℕ) (a : Fin k → ℤ) : Prop :=
  (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
  (∀ i j : Fin k, i < j → a i < a j) ∧
  HasDistinctSums' a

/-- f(n) = maximum k for strictly increasing sequence in [1, n] with distinct sums. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, IsValidSequence n k a}

/-- g(n) = maximum k for any sequence (not necessarily increasing) in [1, n]. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ,
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧ HasDistinctSums' a}

/-- h(n) = maximum k for weakly increasing sequence in [1, n]. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ,
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
    (∀ i j : Fin k, i ≤ j → a i ≤ a j) ∧
    HasDistinctSums' a}

/-- Distinct subset sums: the sum function is injective over all subsets. -/
def HasDistinctSubsetSums (a : Fin k → ℤ) : Prop :=
  Function.Injective (fun S : Finset (Fin k) => ∑ i ∈ S, a i)

/-- Erdős Problem #357 conjecture. -/
def Erdos357Conjecture : Prop :=
  (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ))

/-- Alternative formulation: f(n)/n → 0. -/
def Erdos357ConjectureAlt : Prop :=
  Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 0)

-- Routine: g(n) ≥ f(n)
-- Every f-valid sequence (strictly increasing, range, distinct sums) also satisfies
-- the g constraint (range, distinct sums), so the feasible sets satisfy f-set ⊆ g-set.
theorem g_ge_f (n : ℕ) : g n ≥ f n := by
  sorry

-- Routine: h(n) ≥ f(n)
-- Strictly increasing implies weakly increasing: i < j → a i < a j gives i ≤ j → a i ≤ a j.
theorem h_ge_f (n : ℕ) : h n ≥ f n := by
  sorry

-- Routine: f(n) is nondecreasing.
-- Any sequence with values in [1, n₁] also has values in [1, n₂] for n₁ ≤ n₂.
theorem f_mono {n₁ n₂ : ℕ} (hn : n₁ ≤ n₂) : f n₁ ≤ f n₂ := by
  sorry

-- Routine: Distinct subset sums implies distinct consecutive sums.
-- Contiguous intervals are a special case of all subsets.
theorem subset_sums_implies_consecutive {k : ℕ} (a : Fin k → ℤ)
    (h : HasDistinctSubsetSums a) : HasDistinctSums' a := by
  sorry

-- Routine: The two conjecture formulations are equivalent.
-- isLittleO f g at atTop ↔ f/g → 0 (standard Mathlib equivalence).
theorem conjecture_equiv : Erdos357Conjecture ↔ Erdos357ConjectureAlt := by
  sorry

end Erdos357Aristotle
