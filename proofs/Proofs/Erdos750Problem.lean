/-
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
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open SimpleGraph

/- ## Definitions -/

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

/- ## The Main Conjecture (OPEN) -/

/-- **Erdős Problem #750** (OPEN): For any f : ℕ → ℕ with f(m) → ∞, there exists
    an infinite-chromatic graph G (on some vertex set) such that every m-vertex
    induced subgraph has an independent set of size ≥ m/2 − f(m) for all m ≥ m₀. -/
axiom erdos_750 :
    ∀ f : ℕ → ℕ,
    Filter.Tendsto (fun m => (f m : ℝ)) Filter.atTop Filter.atTop →
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V) (m₀ : ℕ),
      HasInfiniteChromatic G ∧ AlmostBipartite G f m₀

/- ## Known Results -/

/- Erdős–Hajnal (1967): for c > 1/4 there is an infinite-chromatic
   graph with independent sets ≥ (1/2 − c)m in every m-vertex subgraph. -/
/- Erdős–Hajnal–Szemerédi (1982): extends the 1967 result to all ε > 0.
   Resolves Problem #750 for linear deviation functions f(m) = εm. -/

/- ## Open Cases -/

/- Open: Square Root Case — Is there an infinite-chromatic graph where
   every m-vertex subgraph has an independent set of size ≥ m/2 − √m? -/
/- Open: Logarithmic Case — with deviation C · log₂ m. -/

/- ## Auxiliary -/

/-- In Fin 2, the only nonzero element is 1. -/
private theorem fin2_ne_zero_eq_one : ∀ (i : Fin 2), i ≠ 0 → i = 1 := by decide

/-- **Bipartite Benchmark**: bipartite graphs on m vertices have maximum
    independent set ≥ ⌊m/2⌋. The deviation f(m) measures local non-bipartiteness. -/
theorem bipartite_benchmark :
    ∀ (V : Type) [DecidableEq V] (G : SimpleGraph V),
      G.IsBipartite →
      ∀ S : Finset V, maxIndSetSize G S ≥ S.card / 2 := by
  intro V _ G hbip S
  -- Extract 2-coloring from IsBipartite = Colorable 2
  obtain ⟨c⟩ := hbip
  classical
  -- Define the two color classes within S
  set A := S.filter (fun v => c v = (0 : Fin 2)) with hA_def
  set B := S.filter (fun v => c v ≠ (0 : Fin 2)) with hB_def
  -- A and B are complementary filters, so |A| + |B| = |S|
  have hpart : A.card + B.card = S.card :=
    Finset.filter_card_add_filter_neg_card_eq_card S (fun v => c v = (0 : Fin 2))
  -- Both color classes are independent sets
  have hA_indep : ∀ v ∈ A, ∀ w ∈ A, v ≠ w → ¬G.Adj v w := by
    intro v hv w hw _ hadj
    simp only [hA_def, Finset.mem_filter] at hv hw
    -- c maps adjacent vertices to different colors; but v, w have same color 0
    exact (c.map_rel' hadj) (hv.2 ▸ hw.2)
  have hB_indep : ∀ v ∈ B, ∀ w ∈ B, v ≠ w → ¬G.Adj v w := by
    intro v hv w hw _ hadj
    simp only [hB_def, Finset.mem_filter] at hv hw
    -- c v ≠ 0 and c w ≠ 0 ⟹ both = 1 in Fin 2, so same color
    exact (c.map_rel' hadj) (by rw [fin2_ne_zero_eq_one _ hv.2, fin2_ne_zero_eq_one _ hw.2])
  -- Both are in the filtered powerset (independent subsets of S)
  have hA_mem : A ∈ S.powerset.filter
      (fun I => ∀ v ∈ I, ∀ w ∈ I, v ≠ w → ¬G.Adj v w) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, hA_indep⟩
  have hB_mem : B ∈ S.powerset.filter
      (fun I => ∀ v ∈ I, ∀ w ∈ I, v ≠ w → ¬G.Adj v w) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, hB_indep⟩
  -- The larger class has ≥ S.card / 2 elements
  by_cases h : S.card / 2 ≤ A.card
  · exact le_trans h (Finset.le_sup hA_mem)
  · exact le_trans (by omega : S.card / 2 ≤ B.card) (Finset.le_sup hB_mem)
