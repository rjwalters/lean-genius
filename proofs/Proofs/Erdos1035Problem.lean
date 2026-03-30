/-
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

/- ## Hypercube graph -/

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

/- ## Minimum degree -/

/-- A simple graph on `Fin N` has minimum degree at least `d` if every vertex
has at least `d` neighbours. -/
def HasMinDegree (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (d : ℕ) : Prop :=
    ∀ v : Fin N, d ≤ (univ.filter (G.Adj v)).card

/- ## Subgraph containment -/

/-- Graph `H` on `Fin M` is a subgraph of `G` on `Fin N` (via an injective
vertex map preserving adjacency). -/
def ContainsAsSubgraph (G : SimpleGraph (Fin N)) (H : SimpleGraph (Fin M)) : Prop :=
    ∃ f : Fin M → Fin N, Function.Injective f ∧
      ∀ u v : Fin M, H.Adj u v → G.Adj (f u) (f v)

/- ## Main conjecture -/

/-- Erdős Problem 1035: There exists `c > 0` such that every graph on `2^n`
vertices with min degree `> (1-c) * 2^n` contains `Q_n`. -/
def ErdosProblem1035 : Prop :=
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 0 < n →
      ∀ (G : SimpleGraph (Fin (2 ^ n))) [DecidableRel G.Adj],
        HasMinDegree G ⌈((1 - c) * (2 ^ n : ℝ))⌉₊ →
          ContainsAsSubgraph G (hypercubeGraph n)

/- ## Alternative questions -/

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

/- ## Basic properties -/

/-- The hypercube `Q_n` is a subgraph of itself (via the identity embedding). -/
theorem hypercube_self_subgraph (n : ℕ) :
    ContainsAsSubgraph (hypercubeGraph n) (hypercubeGraph n) :=
  ⟨id, Function.injective_id, fun _ _ h => h⟩

/-- The complete graph on `2^n` vertices contains `Q_n` (via the identity map,
    since every non-diagonal pair is adjacent in a complete graph). -/
theorem complete_contains_hypercube (n : ℕ) :
    ∀ (G : SimpleGraph (Fin (2 ^ n))),
      (∀ u v : Fin (2 ^ n), u ≠ v → G.Adj u v) →
        ContainsAsSubgraph G (hypercubeGraph n) := by
  intro G hG
  exact ⟨id, Function.injective_id, fun u v huv => hG u v huv.1⟩

/-- `Q_1` is the complete graph on `Fin 2`: two vertices are adjacent iff distinct.
    Proved by case analysis on `Fin 2`. -/
theorem hypercube_one_is_edge :
    ∀ u v : Fin (2 ^ 1), (hypercubeGraph 1).Adj u v ↔ u ≠ v := by
  intro u v
  constructor
  · exact fun h => h.1
  · intro hne
    refine ⟨hne, ⟨0, by omega⟩, ?_⟩
    simp [Pow.pow]
    fin_cases u <;> fin_cases v <;> simp_all

/- ## Decidability -/

/-- Decidability of `hypercubeAdj`: enables `decide` and `native_decide` for
    computational verification of Q_n properties. -/
instance hypercubeAdjDecidable (n : ℕ) (u v : Fin (2 ^ n)) :
    Decidable (hypercubeAdj n u v) :=
  inferInstance

instance hypercubeGraphDecidableAdj (n : ℕ) : DecidableRel (hypercubeGraph n).Adj :=
  fun u v => hypercubeAdjDecidable n u v

/- ## Q_n structural properties -/

/-- Q_2 is the 4-cycle: edges are 0-1, 0-2, 1-3, 2-3. Verified computationally.
    The vertices {00, 01, 10, 11} are adjacent when they differ in exactly one bit. -/
theorem hypercube_two_edges :
    (hypercubeGraph 2).Adj (0 : Fin 4) (1 : Fin 4) ∧
    (hypercubeGraph 2).Adj (0 : Fin 4) (2 : Fin 4) ∧
    ¬(hypercubeGraph 2).Adj (0 : Fin 4) (3 : Fin 4) ∧
    (hypercubeGraph 2).Adj (1 : Fin 4) (3 : Fin 4) ∧
    (hypercubeGraph 2).Adj (2 : Fin 4) (3 : Fin 4) ∧
    ¬(hypercubeGraph 2).Adj (1 : Fin 4) (2 : Fin 4) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> {
    simp only [hypercubeGraph, hypercubeAdj]
    decide
  }

/-- Each vertex of Q_1 has exactly 1 neighbor (Q_1 is 1-regular). -/
theorem hypercube_one_regular :
    ∀ v : Fin (2 ^ 1),
      (Finset.univ.filter (fun w => (hypercubeGraph 1).Adj v w)).card = 1 := by
  intro v; fin_cases v <;> native_decide

/-- Each vertex of Q_2 has exactly 2 neighbors (Q_2 is 2-regular). -/
theorem hypercube_two_regular :
    ∀ v : Fin (2 ^ 2),
      (Finset.univ.filter (fun w => (hypercubeGraph 2).Adj v w)).card = 2 := by
  intro v; fin_cases v <;> native_decide

/-- Q_2 has exactly 4 edges (each of the 4 vertices has degree 2, and 4·2/2 = 4). -/
theorem hypercube_two_edge_count :
    (Finset.univ.filter (fun p : Fin 4 × Fin 4 =>
      (hypercubeGraph 2).Adj p.1 p.2)).card = 8 := by
  native_decide

/-- Each vertex of Q_3 has exactly 3 neighbors (Q_3 is 3-regular). -/
theorem hypercube_three_regular :
    ∀ v : Fin (2 ^ 3),
      (Finset.univ.filter (fun w => (hypercubeGraph 3).Adj v w)).card = 3 := by
  intro v; fin_cases v <;> native_decide

/-- The total number of directed edges in Q_3 is 24 (= 8 vertices × 3 neighbors).
    So Q_3 has 12 undirected edges. -/
theorem hypercube_three_edge_count :
    (Finset.univ.filter (fun p : Fin 8 × Fin 8 =>
      (hypercubeGraph 3).Adj p.1 p.2)).card = 24 := by
  native_decide

/- ## Adjacency characterization -/

/-- Adjacent vertices in Q_n differ in exactly one bit position. Restates
    the definition in terms of explicit bit positions. -/
theorem hypercube_adj_iff (n : ℕ) (u v : Fin (2 ^ n)) :
    (hypercubeGraph n).Adj u v ↔ u ≠ v ∧ ∃ k : Fin n, u.val ^^^ v.val = 2 ^ k.val :=
  Iff.rfl

/-- XOR with a power of 2 gives a distinct value (flipping a nonzero bit).
    For any v and k, v XOR 2^k ≠ v since 2^k > 0. -/
theorem xor_pow2_ne_self (v k : ℕ) : v ^^^ 2 ^ k ≠ v := by
  intro h
  have : v ^^^ v ^^^ 2 ^ k = v ^^^ v := by rw [h]
  simp [Nat.xor_self, Nat.zero_xor] at this

/- Q_n is n-regular: every vertex has exactly n neighbors.
   This follows from the fact that flipping any one of the n bit positions
   gives a distinct neighbor, and these are exactly all neighbors.
   Verified computationally for n ≤ 3 (see hypercube_one_regular,
   hypercube_two_regular, hypercube_three_regular above). -/
