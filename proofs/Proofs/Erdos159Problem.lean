/-!
# Erdős Problem 159: Ramsey Numbers for C₄ and Complete Graphs

Determine whether there exists a constant `c > 0` such that
`R(C₄, Kₙ) ≪ n^{2-c}`.

Known bounds:
- Upper: `R(C₄, Kₙ) ≪ n² / (log n)²` (Szemerédi)
- Lower: `R(C₄, Kₙ) ≫ n^{3/2} / (log n)^{3/2}` (Spencer)

*Reference:* [erdosproblems.com/159](https://www.erdosproblems.com/159)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open SimpleGraph

/-! ## Graph predicates -/

/-- A simple graph contains a 4-cycle `C₄` if there exist four distinct
vertices forming a cycle `a-b-c-d-a`. -/
def HasC4 {V : Type*} (G : SimpleGraph V) : Prop :=
    ∃ (a b c d : V),
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A simple graph contains a complete subgraph on `n` vertices if there
exist `n` distinct vertices that are pairwise adjacent. -/
def HasClique {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
    ∃ (S : Finset V), S.card = n ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-! ## Ramsey number R(C₄, Kₙ) -/

/-- `R(C₄, Kₙ)` is the smallest `N` such that every 2-colouring of `K_N`
contains either a red `C₄` or a blue `Kₙ`. Equivalently, every graph on
`N` vertices either contains `C₄` or has independence number `≥ n`. -/
axiom ramseyC4Kn : ℕ → ℕ

/-- The Ramsey number is the threshold: below it, a counterexample
exists. -/
axiom ramseyC4Kn_spec (n : ℕ) (hn : 1 ≤ n) :
    (∀ (G : SimpleGraph (Fin (ramseyC4Kn n))),
      HasC4 G ∨ HasClique Gᶜ n) ∧
    (∀ N : ℕ, N < ramseyC4Kn n →
      ∃ (G : SimpleGraph (Fin N)),
        ¬HasC4 G ∧ ¬HasClique Gᶜ n)

/-! ## Known bounds -/

/-- Szemerédi's upper bound: `R(C₄, Kₙ) ≤ C · n² / (log n)²` for some
constant `C > 0` and sufficiently large `n`. -/
axiom szemeredi_upper :
    ∃ C : ℝ, 0 < C ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ 2 / (Real.log n) ^ 2

/-- Spencer's lower bound: `R(C₄, Kₙ) ≥ c · n^{3/2} / (log n)^{3/2}`
for some constant `c > 0` and sufficiently large `n`. -/
axiom spencer_lower :
    ∃ c : ℝ, 0 < c ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c * (n : ℝ) ^ (3/2 : ℝ) / (Real.log n) ^ (3/2 : ℝ) ≤ (ramseyC4Kn n : ℝ)

/-! ## Main conjecture -/

/-- Erdős Problem 159: Does there exist `c > 0` such that
`R(C₄, Kₙ) ≤ C · n^{2-c}` for some constant `C` and all large `n`?

This asks whether the upper bound can be improved from `n²/(log n)²`
to a genuine power saving `n^{2-c}`. -/
def ErdosProblem159 : Prop :=
    ∃ (c : ℝ), 0 < c ∧
      ∃ (C : ℝ), 0 < C ∧
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c)

/-! ## Basic properties -/

/-- `R(C₄, Kₙ)` is monotone in `n`: larger complete graphs require at
least as many vertices. -/
axiom ramseyC4Kn_mono (m n : ℕ) (h : m ≤ n) :
    ramseyC4Kn m ≤ ramseyC4Kn n

/-- Trivial lower bound: `R(C₄, Kₙ) ≥ n` since `K_{n-1}` has no `C₄`
(for `n ≤ 4`) or the complement has clique number `< n`. -/
axiom ramseyC4Kn_ge (n : ℕ) (hn : 1 ≤ n) : n ≤ ramseyC4Kn n
