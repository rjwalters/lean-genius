/-!
# Erdős Problem #750 — Almost Bipartite Graphs with Infinite Chromatic Number

For f(m) → ∞, does there exist a graph G with χ(G) = ∞ such that every
m-vertex subgraph has an independent set of size ≥ m/2 − f(m)?

A graph satisfying the independent-set condition is "almost bipartite":
bipartite graphs achieve exactly ⌈m/2⌉, so f(m) measures the local
deviation from bipartiteness.

## Known Results
- Erdős–Hajnal (1967): proved for f(m) = cm, c > 1/4
- Erdős–Hajnal–Szemerédi (1982): proved for f(m) = εm, any ε > 0

## Open
- Sublinear f(m) = o(m) with f(m) → ∞ remains open
- Specific cases: f(m) = √m, f(m) = log m

Status: OPEN
Reference: https://erdosproblems.com/750
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open SimpleGraph

/-! ## Definitions -/

/-- A graph has infinite chromatic number if no finite coloring is proper. -/
def HasInfiniteChromatic {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ¬∃ c : V → Fin k, ∀ v w, G.Adj v w → c v ≠ c w

/-- Maximum independent set size in the induced subgraph on S. -/
noncomputable def maxIndSetSize {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (S.powerset.filter (fun I => ∀ v ∈ I, ∀ w ∈ I, v ≠ w → ¬G.Adj v w)).sup Finset.card

/-- G is (f, m₀)-almost bipartite: every subgraph on m ≥ m₀ vertices has
    an independent set of size ≥ m/2 − f(m). -/
def AlmostBipartite {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (f : ℕ → ℕ) (m₀ : ℕ) : Prop :=
  ∀ S : Finset V, S.card ≥ m₀ →
    maxIndSetSize G S ≥ S.card / 2 - f S.card

/-! ## The Main Conjecture -/

/-- **Erdős Problem #750**: For any f : ℕ → ℕ with f(m) → ∞, there exists
    an infinite-chromatic f-almost-bipartite graph. -/
axiom erdos_750_conjecture :
  ∀ f : ℕ → ℕ,
    (∀ k : ℕ, ∃ m₀ : ℕ, ∀ m ≥ m₀, f m > k) →
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      HasInfiniteChromatic G ∧ ∀ m₀ : ℕ, AlmostBipartite G f m₀

/-! ## Known Results -/

/-- **Erdős–Hajnal (1967)**: for c > 1/4 there is an infinite-chromatic
    graph with independent sets ≥ (1/2 − c)m in every m-vertex subgraph. -/
axiom erdos_hajnal_1967 (c : ℚ) (hc : c > 1/4) :
  ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
    HasInfiniteChromatic G ∧
    ∀ S : Finset V, (maxIndSetSize G S : ℚ) ≥ (1/2 - c) * S.card

/-- **Erdős–Hajnal–Szemerédi (1982)**: extends the 1967 result to all ε > 0.
    Resolves Problem #750 for linear deviation functions f(m) = εm. -/
axiom erdos_hajnal_szemeredi_1982 (ε : ℚ) (hε : ε > 0) :
  ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
    HasInfiniteChromatic G ∧
    ∀ S : Finset V, (maxIndSetSize G S : ℚ) ≥ (1/2 - ε) * S.card

/-! ## Open Cases -/

/-- **Open: Square Root Case** — Is there an infinite-chromatic graph where
    every m-vertex subgraph has an independent set of size ≥ m/2 − √m? -/
axiom sqrt_case :
  ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
    HasInfiniteChromatic G ∧
    ∀ S : Finset V, maxIndSetSize G S ≥ S.card / 2 - Nat.sqrt S.card

/-- **Open: Logarithmic Case** — with deviation C · log₂ m. -/
axiom log_case (C : ℕ) :
  ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
    HasInfiniteChromatic G ∧
    ∀ S : Finset V, S.card > 1 →
      maxIndSetSize G S ≥ S.card / 2 - C * Nat.log2 S.card

/-! ## Connections and Observations -/

/-- **Problem #75 Connection**: asks for χ(G) = ℵ₁ with independent sets
    > n^{1−ε}. Stronger than #750; shares the local-vs-global theme. -/
axiom problem_75_connection :
  ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
    HasInfiniteChromatic G ∧
    ∀ ε : ℚ, ε > 0 →
      ∃ n₀ : ℕ, ∀ S : Finset V, S.card ≥ n₀ →
        (maxIndSetSize G S : ℚ) > S.card ^ ((1 : ℚ) - ε)

/-- **Bipartite Benchmark**: bipartite graphs on m vertices have maximum
    independent set ⌈m/2⌉. The deviation f(m) measures local non-bipartiteness. -/
axiom bipartite_benchmark :
  ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V),
    G.IsBipartite →
    ∀ S : Finset V, maxIndSetSize G S ≥ S.card / 2
