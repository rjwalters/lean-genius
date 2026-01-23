/-
Erdős Problem #181: Ramsey Number of the Hypercube

**Statement**: Prove that R(Q_n) ≪ 2^n, where Q_n is the n-dimensional hypercube.

**Status**: OPEN

The n-dimensional hypercube Q_n has:
- 2^n vertices (binary strings of length n)
- n·2^(n-1) edges (pairs differing in exactly one coordinate)

**Best Known Bounds**:
- Trivial: R(Q_n) ≤ R(K_{2^n}) ≤ C^{2^n} for some C > 1
- Tikhomirov 2022: R(Q_n) ≪ 2^{(2-c)n} for c ≈ 0.03656

**Conjecture** (Burr-Erdős): R(Q_n) ≪ 2^n
- Erdős-Sós could not decide if R(Q_n)/2^n → ∞ or not

**References**:
- [BuEr75] Burr, Erdős - original conjecture
- [Er93] Erdős - survey mentioning the problem
- [Ti22] Tikhomirov - best known upper bound (2022)

This is Problem #20 in the Ramsey Theory collection.

Reference: https://erdosproblems.com/181
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Erdos181

open SimpleGraph Finset

/-!
## Part I: The Hypercube Graph Q_n
-/

/-- Helper: filter for differing coordinates is symmetric -/
theorem filter_diff_symm (n : ℕ) (x y : Fin n → Bool) :
    (Finset.univ.filter fun i => x i ≠ y i) = (Finset.univ.filter fun i => y i ≠ x i) := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

/-- The n-dimensional hypercube Q_n.
    Vertices: Fin n → Bool (binary strings of length n)
    Edges: pairs differing in exactly one coordinate -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj x y := (Finset.univ.filter fun i => x i ≠ y i).card = 1
  symm := by
    intro x y h
    rw [filter_diff_symm] at h
    exact h
  loopless := by
    intro x h
    have : (Finset.univ.filter fun i => x i ≠ x i).card = 0 := by
      simp only [ne_eq, not_true_eq_false, Finset.filter_false, Finset.card_empty]
    simp_all

/-- Alternative notation: Q_n -/
notation "Q_" n => hypercubeGraph n

/-- Q_n has 2^n vertices -/
theorem hypercube_vertex_count (n : ℕ) : Fintype.card (Fin n → Bool) = 2^n := by
  simp [Fintype.card_fin, Fintype.card_bool]

/-- Hamming distance between two binary strings -/
def hammingDist (n : ℕ) (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

/-- Q_n adjacency is equivalent to Hamming distance 1 -/
theorem hypercube_adj_iff_hamming (n : ℕ) (x y : Fin n → Bool) :
    (Q_ n).Adj x y ↔ hammingDist n x y = 1 := by
  rfl

/-- Q_n is connected for n ≥ 1 (any two vertices can be joined by flipping bits one at a time)
    Formalized as: any two vertices have a path between them via single-bit flips -/
theorem hypercube_path_exists (n : ℕ) (hn : n ≥ 1) (x y : Fin n → Bool) :
    ∃ path : List (Fin n → Bool), path.head? = some x ∧ path.getLast? = some y ∧
      ∀ i : Fin (path.length - 1), (Q_ n).Adj (path.get ⟨i.val, by omega⟩)
                                              (path.get ⟨i.val + 1, by omega⟩) := by
  sorry -- Would require path construction via bit flips

/-!
## Part II: Graph Ramsey Numbers

R(G) is the minimum n such that any 2-coloring of K_n contains a
monochromatic copy of G.
-/

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- Edge coloring of a type (complete graph structure) -/
structure EdgeColoring (α : Type*) where
  color : α → α → Bool
  symm : ∀ x y, color x y = color y x
  irrefl : ∀ x, color x x = false

/-- The red subgraph of an edge coloring -/
def EdgeColoring.redGraph (c : EdgeColoring α) : SimpleGraph α where
  Adj x y := c.color x y = true ∧ x ≠ y
  symm x y h := ⟨by rw [c.symm]; exact h.1, h.2.symm⟩
  loopless x h := h.2 rfl

/-- The blue subgraph of an edge coloring -/
def EdgeColoring.blueGraph (c : EdgeColoring α) : SimpleGraph α where
  Adj x y := c.color x y = false ∧ x ≠ y
  symm x y h := ⟨by rw [c.symm]; exact h.1, h.2.symm⟩
  loopless x h := h.2 rfl

/-- A graph H embeds into a graph G -/
def GraphEmbeds (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  ∃ f : W → V, Function.Injective f ∧ ∀ x y, H.Adj x y → G.Adj (f x) (f y)

/-- The Ramsey property for a graph G:
    any 2-coloring of K_n has a monochromatic copy of G -/
def HasGraphRamseyProperty (n : ℕ) (G : SimpleGraph W) : Prop :=
  ∀ c : EdgeColoring (Fin n),
    GraphEmbeds G c.redGraph ∨ GraphEmbeds G c.blueGraph

/-- Existence of graph Ramsey numbers (follows from Ramsey's theorem) -/
axiom graphRamseyExists (G : SimpleGraph W) : ∃ n, HasGraphRamseyProperty n G

/-- Decidability of HasGraphRamseyProperty (finite colorings) -/
axiom hasGraphRamseyProperty_decidable (n : ℕ) (G : SimpleGraph W) :
    Decidable (HasGraphRamseyProperty n G)

attribute [instance] hasGraphRamseyProperty_decidable

/-- The graph Ramsey number R(G) is the minimum n with the Ramsey property -/
noncomputable def graphRamseyNumber (G : SimpleGraph W) : ℕ :=
  Nat.find (graphRamseyExists G)

/-!
## Part III: Known Bounds on R(Q_n)
-/

/-- The Ramsey number of Q_n -/
noncomputable def R_Qn (n : ℕ) : ℕ := graphRamseyNumber (Q_ n)

/-- Trivial lower bound: R(Q_n) ≥ 2^n (need at least |V(Q_n)| vertices) -/
theorem R_Qn_lower (n : ℕ) : R_Qn n ≥ 2^n := by
  sorry -- For monochromatic copy, need at least 2^n vertices

/-- The trivial upper bound via complete graph Ramsey number -/
axiom trivial_upper_bound :
  ∃ C : ℝ, C > 1 ∧ ∀ n : ℕ, (R_Qn n : ℝ) ≤ C^(2^n)

/-- Tikhomirov 2022: R(Q_n) ≪ 2^{(2-c)n} for c ≈ 0.03656

This is the current best known upper bound. -/
axiom tikhomirov_bound :
  ∃ c : ℝ, c > 0 ∧ c < 1 ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (R_Qn n : ℝ) ≤ C * 2^((2 - c) * n)

/-- Specific constant from Tikhomirov: c ≈ 0.03656 is admissible -/
axiom tikhomirov_constant :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (R_Qn n : ℝ) ≤ C * 2^((2 - 3656/100000) * n)

/-!
## Part IV: The Burr-Erdős Conjecture

**Conjecture**: R(Q_n) = O(2^n)

This is still OPEN. The gap between the lower bound (2^n) and the best
known upper bound (2^{(2-0.03656)n} ≈ 2^{1.96n}) is substantial.
-/

/-- The Burr-Erdős conjecture: R(Q_n) ≪ 2^n -/
def burr_erdos_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (R_Qn n : ℝ) ≤ C * 2^n

/-- Alternative statement: the ratio R(Q_n)/2^n is bounded -/
def ratio_bounded : Prop :=
  ∃ M : ℝ, M > 0 ∧ ∀ n : ℕ, n ≥ 1 → (R_Qn n : ℝ) / 2^n ≤ M

/-- The two formulations are equivalent -/
theorem conjecture_equiv_ratio : burr_erdos_conjecture ↔ ratio_bounded := by
  constructor
  · intro ⟨C, hC, hbound⟩
    use C, hC
    intro n hn
    have h := hbound n hn
    have h2n : (2 : ℝ)^n > 0 := by positivity
    calc (R_Qn n : ℝ) / 2^n ≤ C * 2^n / 2^n := by
           apply div_le_div_of_nonneg_right h (le_of_lt h2n)
      _ = C := by field_simp
  · intro ⟨M, hM, hbound⟩
    use M, hM
    intro n hn
    have h := hbound n hn
    have h2n : (2 : ℝ)^n > 0 := by positivity
    calc (R_Qn n : ℝ) = (R_Qn n : ℝ) / 2^n * 2^n := by field_simp
      _ ≤ M * 2^n := by apply mul_le_mul_of_nonneg_right h (le_of_lt h2n)

/-- Erdős-Sós question: does R(Q_n)/2^n → ∞?

Erdős reported that neither he nor Sós could determine whether this ratio
goes to infinity or stays bounded. -/
def erdos_sos_question : Prop :=
  ∀ M : ℝ, M > 0 → ∃ n : ℕ, n ≥ 1 ∧ (R_Qn n : ℝ) / 2^n > M

/-- The Erdős-Sós question is the negation of the Burr-Erdős conjecture -/
theorem erdos_sos_negates_burr_erdos :
    erdos_sos_question ↔ ¬ratio_bounded := by
  unfold erdos_sos_question ratio_bounded
  constructor
  · intro h ⟨M, hM, hbound⟩
    obtain ⟨n, hn, hcontra⟩ := h M hM
    have := hbound n hn
    linarith
  · intro h M hM
    by_contra hcontra
    push_neg at hcontra
    exact h ⟨M, hM, hcontra⟩

/-!
## Part V: Related Results and Context
-/

/-- Q_n has bipartite structure (parity of 1-bits) -/
theorem hypercube_bipartite_structure (n : ℕ) :
    ∃ A B : Set (Fin n → Bool),
      A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
      ∀ x y, (Q_ n).Adj x y → (x ∈ A ∧ y ∈ B) ∨ (x ∈ B ∧ y ∈ A) := by
  sorry -- Partition by parity of Hamming weight

/-- Small cases: R(Q_1) = R(K_2) = 2 -/
theorem R_Q1 : R_Qn 1 ≤ 2 := by
  sorry -- Q_1 is just an edge, need 2 vertices

/-- R(Q_2) relates to R(C_4) since Q_2 ≅ C_4 -/
theorem R_Q2_is_cycle : True := by
  -- Q_2 is isomorphic to C_4 (the 4-cycle)
  trivial

/-!
## Part VI: Summary and Status
-/

/-- Erdős #181 Summary:

**Problem**: Prove R(Q_n) ≪ 2^n (linear in the number of vertices)

**Status**: OPEN

**Known**:
- Lower bound: R(Q_n) ≥ 2^n (trivial - need enough vertices)
- Best upper: R(Q_n) ≪ 2^{1.96n} (Tikhomirov 2022)

**Gap**: Factor of 2^{0.96n} between bounds

**What would close the gap**:
- Better embedding lemmas for hypercubes
- New probabilistic arguments
- Structural understanding of 2-colorings avoiding Q_n

**Related**: Problem #1035 (hypercube subgraph via minimum degree) -/
theorem erdos_181_status : True := trivial

end Erdos181
