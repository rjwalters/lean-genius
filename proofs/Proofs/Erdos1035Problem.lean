/-!
# Erdős Problem 1035: Hypercube Subgraphs in Dense Graphs

Is there a constant `c > 0` such that every graph on `2^n` vertices with
minimum degree greater than `(1 - c) * 2^n` contains the `n`-dimensional
hypercube `Q_n` as a subgraph?

If the conjecture is false, two alternatives: find the smallest `m > 2^n`
such that min degree `> (1 - c) * 2^n` on `m` vertices forces `Q_n`, or
find `u_n` such that min degree `> 2^n - u_n` on `2^n` vertices forces `Q_n`.

*Reference:* [erdosproblems.com/1035](https://www.erdosproblems.com/1035)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open SimpleGraph Finset

/-! ## Hypercube graph -/

/-- The `n`-dimensional hypercube graph `Q_n` on `Fin (2^n)` vertices, where two
vertices are adjacent iff their XOR has exactly one bit set. -/
def hypercubeAdj (n : ℕ) (u v : Fin (2 ^ n)) : Prop :=
    u ≠ v ∧ ∃ k : Fin n, u.val ^^^ v.val = 2 ^ k.val

/-- The hypercube graph `Q_n` as a SimpleGraph. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin (2 ^ n)) where
  Adj := hypercubeAdj n
  symm := by
    intro u v ⟨hne, k, hk⟩
    exact ⟨hne.symm, k, by rw [Nat.xor_comm]; exact hk⟩
  loopless := by
    intro v ⟨hne, _⟩
    exact hne rfl

/-! ## Minimum degree -/

/-- A simple graph on `Fin N` has minimum degree at least `d` if every vertex
has at least `d` neighbours. -/
def HasMinDegree (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (d : ℕ) : Prop :=
    ∀ v : Fin N, d ≤ (univ.filter (G.Adj v)).card

/-! ## Subgraph containment -/

/-- Graph `H` on `Fin M` is a subgraph of `G` on `Fin N` (via an injective
vertex map preserving adjacency). -/
def ContainsAsSubgraph (G : SimpleGraph (Fin N)) (H : SimpleGraph (Fin M)) : Prop :=
    ∃ f : Fin M → Fin N, Function.Injective f ∧
      ∀ u v : Fin M, H.Adj u v → G.Adj (f u) (f v)

/-! ## Main conjecture -/

/-- Erdős Problem 1035: There exists `c > 0` such that every graph on `2^n`
vertices with min degree `> (1-c) * 2^n` contains `Q_n`. -/
def ErdosProblem1035 : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
        HasMinDegree G ⌈((1 - c) * (2 ^ n : ℝ))⌉₊ →
          ContainsAsSubgraph G (hypercubeGraph n)

/-! ## Alternative questions -/

/-- If the conjecture fails: what is the smallest `m > 2^n` such that
min degree `> (1-c) * 2^n` on `m` vertices forces `Q_n`? -/
def ErdosProblem1035_alt1 (c : ℝ) (hc : 0 < c) : Prop :=
    ∀ n : ℕ, 0 < n →
      ∃ m : ℕ, 2 ^ n < m ∧
        ∀ (G : SimpleGraph (Fin m)) [DecidableRel G.Adj],
          HasMinDegree G ⌈((1 - c) * (2 ^ n : ℝ))⌉₊ →
            ContainsAsSubgraph G (hypercubeGraph n)

/-- If the conjecture fails: find `u_n` such that min degree `> 2^n - u_n`
on `2^n` vertices forces `Q_n`. -/
def ErdosProblem1035_alt2 : Prop :=
    ∃ u : ℕ → ℕ, (∀ n, 0 < u n) ∧
      ∀ n : ℕ, 0 < n →
        ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
          HasMinDegree G (2 ^ n - u n) →
            ContainsAsSubgraph G (hypercubeGraph n)

/-! ## Basic properties -/

/-- The hypercube `Q_n` is a subgraph of itself. -/
axiom hypercube_self_subgraph (n : ℕ) :
    ContainsAsSubgraph (hypercubeGraph n) (hypercubeGraph n)

/-- The complete graph on `2^n` vertices contains `Q_n`. -/
axiom complete_contains_hypercube (n : ℕ) :
    ∀ (G : SimpleGraph (Fin (2 ^ n))),
      (∀ u v : Fin (2 ^ n), u ≠ v → G.Adj u v) →
        ContainsAsSubgraph G (hypercubeGraph n)

/-- `Q_1` is the single edge graph on 2 vertices. -/
axiom hypercube_one_is_edge :
    ∀ u v : Fin (2 ^ 1), (hypercubeGraph 1).Adj u v ↔ u ≠ v
