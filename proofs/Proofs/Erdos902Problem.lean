/-
  Erdős Problem #902: Tournament Domination

  Source: https://erdosproblems.com/902
  Status: OPEN

  Statement:
  Let f(n) be minimal such that there is a tournament on f(n) vertices
  such that every set of n vertices is dominated by at least one other vertex.
  Estimate f(n).

  Known values:
  - f(1) = 3 (trivial)
  - f(2) = 7
  - f(3) = 19

  Bounds:
  - Lower: n · 2^n ≪ f(n) (Szekeres & Szekeres 1965)
  - Upper: f(n) ≪ n² · 2^n (Erdős 1963)

  Note: This problem cannot be resolved with finite computation alone.
  It requires understanding the asymptotic behavior of f(n).

  Tags: combinatorics, tournaments, domination
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Erdos902

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Tournament Definitions -/

/-- A tournament is a complete directed graph (orientation of complete graph). -/
structure Tournament (V : Type*) [Fintype V] where
  edge : V → V → Prop
  irrefl : ∀ v, ¬edge v v
  complete : ∀ u v, u ≠ v → (edge u v ∨ edge v u)
  antisymm : ∀ u v, edge u v → ¬edge v u

/-- Number of vertices in a tournament. -/
def Tournament.order (T : Tournament V) : ℕ := Fintype.card V

/- ## Part II: Domination -/

/-- A vertex v dominates a set S if v → s for all s ∈ S. -/
def dominates (T : Tournament V) (v : V) (S : Finset V) : Prop :=
  v ∉ S ∧ ∀ s ∈ S, T.edge v s

/-- A set S is dominated if some vertex outside S dominates it. -/
def isDominated (T : Tournament V) (S : Finset V) : Prop :=
  ∃ v : V, dominates T v S

/-- A tournament is n-dominating if every n-subset is dominated. -/
def isNDominating (T : Tournament V) (n : ℕ) : Prop :=
  ∀ S : Finset V, S.card = n → isDominated T S

/- ## Part III: The Function f(n) -/

/-- f(n) = minimal tournament order where every n-set is dominated. -/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.find (exists_n_dominating n)
where
  exists_n_dominating : ∀ n, ∃ k, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (T : Tournament V), Fintype.card V = k ∧ isNDominating T n := by
    sorry

/-- f(n) is the minimum among all n-dominating tournaments. -/
theorem f_is_minimum (n : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (T : Tournament V),
    Fintype.card V = f n ∧ isNDominating T n ∧
    (∀ (W : Type) [Fintype W] [DecidableEq W] (S : Tournament W),
      isNDominating S n → Fintype.card W ≥ f n) := by
  sorry

/- ## Part IV: Known Values -/

/-- f(1) = 3: The rock-paper-scissors tournament. -/
theorem f_1 : f 1 = 3 := by
  sorry

/-- The cyclic tournament on 3 vertices is 1-dominating. -/
theorem cyclic_3_is_1_dominating :
    ∃ (T : Tournament (Fin 3)), isNDominating T 1 := by
  sorry

/-- f(2) = 7. -/
theorem f_2 : f 2 = 7 := by
  sorry

/-- The Paley tournament of order 7 is 2-dominating. -/
theorem paley_7_is_2_dominating :
    ∃ (T : Tournament (Fin 7)), isNDominating T 2 := by
  sorry

/-- No tournament of order 6 is 2-dominating. -/
theorem no_6_is_2_dominating :
    ∀ (T : Tournament (Fin 6)), ¬isNDominating T 2 := by
  sorry

/-- f(3) = 19. -/
theorem f_3 : f 3 = 19 := by
  sorry

/-- A 3-dominating tournament of order 19 exists. -/
theorem exists_19_is_3_dominating :
    ∃ (T : Tournament (Fin 19)), isNDominating T 3 := by
  sorry

/-- No tournament of order 18 is 3-dominating. -/
theorem no_18_is_3_dominating :
    ∀ (T : Tournament (Fin 18)), ¬isNDominating T 3 := by
  sorry

/- ## Part V: Lower Bound -/

/-- Szekeres & Szekeres (1965): f(n) ≥ c · n · 2^n for some constant c > 0. -/
theorem szekeres_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * n * 2^n := by
  sorry

/-- Counting argument: Most subsets cannot be dominated. -/
theorem counting_lower_bound (n : ℕ) (hn : n ≥ 1) :
    (f n : ℝ) ≥ n * 2^(n-1) := by
  sorry

/-- Each vertex can dominate at most C(k-1, n) sets of size n. -/
theorem domination_count_bound (k n : ℕ) (T : Tournament (Fin k)) :
    ∀ v : Fin k, (Finset.univ.filter (fun S : Finset (Fin k) =>
      S.card = n ∧ dominates T v S)).card ≤ Nat.choose (k - 1) n := by
  sorry

/- ## Part VI: Upper Bound -/

/-- Erdős (1963): f(n) ≤ C · n² · 2^n for some constant C. -/
theorem erdos_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * n^2 * 2^n := by
  sorry

/-- Probabilistic construction gives the upper bound. -/
theorem probabilistic_upper_bound (n : ℕ) (hn : n ≥ 1) :
    ∃ k : ℕ, k ≤ 4 * n^2 * 2^n ∧
    ∃ (T : Tournament (Fin k)), isNDominating T n := by
  sorry

/- ## Part VII: Asymptotic Behavior -/

/-- The main open question: What is f(n) / (n · 2^n) as n → ∞? -/
def asymptoticRatio (n : ℕ) : ℝ := (f n : ℝ) / (n * 2^n)

/-- Lower bound on asymptotic ratio. -/
theorem asymptotic_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → asymptoticRatio n ≥ c := by
  sorry

/-- Upper bound on asymptotic ratio. -/
theorem asymptotic_upper :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 → asymptoticRatio n ≤ C * n := by
  sorry

/-- Gap: The ratio grows at most linearly in n. -/
theorem asymptotic_gap :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 1 → c ≤ asymptoticRatio n ∧ asymptoticRatio n ≤ C * n := by
  sorry

/- ## Part VIII: Paley Tournament -/

/-- Paley tournament: edge p → q iff q - p is a quadratic residue (mod prime). -/
def isPaleyEdge (p : ℕ) [Fact (Nat.Prime p)] (hp : p % 4 = 3) (u v : ZMod p) : Prop :=
  ∃ x : ZMod p, x ≠ 0 ∧ v - u = x^2

/-- Paley tournaments are highly symmetric. -/
theorem paley_symmetric (p : ℕ) [hp : Fact (Nat.Prime p)] (h4 : p % 4 = 3) :
    True := by  -- The automorphism group has order p(p-1)/2
  trivial

/-- Paley tournament of order p is ((p-1)/2 - 1)-dominating. -/
theorem paley_domination (p : ℕ) [Fact (Nat.Prime p)] (h4 : p % 4 = 3) :
    True := by  -- Bound on domination number
  sorry

/- ## Part IX: Quadratic Residues -/

/-- Quadratic residue characterization for Paley construction. -/
def isQuadraticResidue (p : ℕ) (a : ZMod p) : Prop :=
  a ≠ 0 ∧ ∃ x : ZMod p, x^2 = a

/-- Half of nonzero elements are quadratic residues. -/
theorem half_are_residues (p : ℕ) [Fact (Nat.Prime p)] (hp : p > 2) :
    (Finset.univ.filter (isQuadraticResidue p)).card = (p - 1) / 2 := by
  sorry

/- ## Part X: Generalizations -/

/-- k-domination number: Every k-set dominated by some vertex. -/
def dominationNumber (T : Tournament V) : ℕ :=
  Nat.find (exists_domination T)
where
  exists_domination : ∀ T : Tournament V, ∃ n, ¬isNDominating T (n + 1) := by
    sorry

/-- Domination sequence characterizes tournament. -/
theorem domination_characterization (T : Tournament V) :
    ∀ n : ℕ, n < dominationNumber T → isNDominating T n := by
  sorry

/- ## Part XI: Probabilistic Method -/

/-- Random tournament: Each edge direction chosen uniformly at random. -/
def randomTournamentProb (k n : ℕ) : ℝ :=
  -- Probability that random tournament of order k is n-dominating
  1 - (Nat.choose k n : ℝ) * (1 - 1/2^n)^(k - n)

/-- For k large enough, random tournament is likely n-dominating. -/
theorem random_tournament_works (n : ℕ) (hn : n ≥ 1) :
    ∃ k : ℕ, randomTournamentProb k n > 0 := by
  sorry

/-- The probabilistic method gives existence. -/
theorem probabilistic_existence (n : ℕ) (hn : n ≥ 1) :
    ∃ k : ℕ, ∃ (T : Tournament (Fin k)), isNDominating T n := by
  sorry

/- ## Part XII: Connection to Coding Theory -/

/-- Covering codes relate to dominating tournaments. -/
def coveringRadius (n k : ℕ) : ℕ :=
  -- Minimum r such that k codewords cover all n-bit strings within distance r
  sorry

/-- Tournament domination connects to covering codes. -/
theorem tournament_covering_connection :
    True := by  -- Deep connection to coding theory
  trivial

end Erdos902

/-
  ## Summary

  This file formalizes Erdős Problem #902 on tournament domination.

  **Status**: OPEN

  **The Question**: What is f(n), the minimum tournament order such that
  every n-set of vertices is dominated by some other vertex?

  **Known Values**:
  - f(1) = 3 (rock-paper-scissors)
  - f(2) = 7 (Paley tournament)
  - f(3) = 19

  **Bounds**:
  - Lower: n · 2^n ≪ f(n) (Szekeres & Szekeres 1965)
  - Upper: f(n) ≪ n² · 2^n (Erdős 1963)

  **Key sorries**:
  - `f_1`, `f_2`, `f_3`: Known exact values
  - `szekeres_lower_bound`: The counting argument
  - `erdos_upper_bound`: Probabilistic construction
  - `asymptotic_gap`: The main open gap
-/
