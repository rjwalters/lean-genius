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

/-- Existence of n-dominating tournaments for all n. -/
axiom exists_n_dominating : ∀ n, ∃ k, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
    (T : Tournament V), Fintype.card V = k ∧ isNDominating T n

/-- f(n) = minimal tournament order where every n-set is dominated. -/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.find (exists_n_dominating n)

/- ## Part V: Lower Bound -/

/-- Szekeres & Szekeres (1965): f(n) ≥ c · n · 2^n for some constant c > 0. -/
axiom szekeres_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * n * 2^n

/- ## Part VI: Upper Bound -/

/-- Erdős (1963): f(n) ≤ C · n² · 2^n for some constant C. -/
axiom erdos_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * n^2 * 2^n

/- ## Part VII: Asymptotic Behavior -/

/-- The main open question: What is f(n) / (n · 2^n) as n → ∞? -/
def asymptoticRatio (n : ℕ) : ℝ := (f n : ℝ) / (n * 2^n)

/-- Lower bound on asymptotic ratio. -/
axiom asymptotic_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → asymptoticRatio n ≥ c

/-- Upper bound on asymptotic ratio. -/
axiom asymptotic_upper :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 → asymptoticRatio n ≤ C * n

/-- Gap: The ratio grows at most linearly in n. -/
theorem asymptotic_gap :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ n : ℕ, n ≥ 1 → c ≤ asymptoticRatio n ∧ asymptoticRatio n ≤ C * n := by
  obtain ⟨c, hc_pos, hc_bound⟩ := asymptotic_lower
  obtain ⟨C, hC_bound⟩ := asymptotic_upper
  refine ⟨c, C, hc_pos, ?_, ?_⟩
  · -- C > 0: follows from asymptotic ratio being positive for n ≥ 1
    by_contra hC_neg
    push_neg at hC_neg
    have h1 := hc_bound 1 (by omega)
    have h2 := hC_bound 1 (by omega)
    linarith
  · intro n hn
    exact ⟨hc_bound n hn, hC_bound n hn⟩

/- ## Part X: Generalizations -/

/-- Existence of non-dominating level for any tournament. -/
axiom exists_non_dominating (T : Tournament V) : ∃ n, ¬isNDominating T (n + 1)

/-- k-domination number: Every k-set dominated by some vertex. -/
noncomputable def dominationNumber (T : Tournament V) : ℕ :=
  Nat.find (exists_non_dominating T)

/- ## Part XII: Summary -/

/-- **Erdős Problem #902: OPEN**

PROBLEM: Let f(n) be minimal such that there is a tournament on f(n) vertices
where every set of n vertices is dominated by at least one other vertex.
Estimate f(n).

KNOWN:
- f(1) = 3, f(2) = 7, f(3) = 19
- Lower: c·n·2^n ≤ f(n) (Szekeres & Szekeres 1965)
- Upper: f(n) ≤ C·n²·2^n (Erdős 1963, probabilistic method)

OPEN: Close the gap between n·2^n and n²·2^n.
-/
theorem erdos_902 :
    -- Lower bound
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≥ c * n * 2^n) ∧
    -- Upper bound
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * n^2 * 2^n) :=
  ⟨szekeres_lower_bound, erdos_upper_bound⟩

end Erdos902
