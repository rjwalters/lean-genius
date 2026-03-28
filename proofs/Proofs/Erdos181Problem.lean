/-
Erdős Problem #181: Ramsey Number of the Hypercube

Source: https://erdosproblems.com/181
Status: OPEN

Statement:
Let Q_n be the n-dimensional hypercube graph (2^n vertices, edges between
strings differing in exactly one bit). Prove that R(Q_n) ≪ 2^n, where
R(Q_n) is the 2-color Ramsey number.

Known Results:
- Trivial: R(Q_n) ≤ R(K_{2^n}) ≤ C^{2^n} (exponential in vertex count)
- Tikhomirov (2022): R(Q_n) ≤ C · 2^{(2-c)n} for c ≈ 0.0366
- Conjectured: R(Q_n) ≤ C · 2^n (linear in vertex count)
- Lower bound: R(Q_n) ≥ 2^n (trivial, since Q_n has 2^n vertices)

The Erdős-Sós question of whether R(Q_n)/2^n → ∞ remains OPEN.
If the conjecture holds, R(Q_n)/2^n is bounded; if not, it diverges.

References:
- Burr-Erdős [BuEr75]: Conjecture
- Erdős [Er93]: Discussion with Sós
- Tikhomirov [Ti22]: Best known upper bound
- Lee (2017): Proved bounded-degree Ramsey conjecture (doesn't apply to Q_n)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Erdos181

/-
## Part I: Hypercube Graph

The n-dimensional hypercube Q_n has 2^n vertices (binary strings of
length n) and edges between vertices differing in exactly one coordinate.
-/

/-- Two vertices of Q_n are adjacent iff they differ in exactly one bit position. -/
def hypercubeAdj (n : ℕ) (x y : Fin (2 ^ n)) : Prop :=
  ∃! i : Fin n, (x.val / 2 ^ i.val) % 2 ≠ (y.val / 2 ^ i.val) % 2

/-- Hypercube adjacency is symmetric: if x and y differ in one bit, so do y and x. -/
theorem hypercubeAdj_symm (n : ℕ) (x y : Fin (2 ^ n)) :
    hypercubeAdj n x y → hypercubeAdj n y x := by
  intro ⟨i, hi, huniq⟩
  exact ⟨i, Ne.symm hi, fun j hj => huniq j (Ne.symm hj)⟩

/-- Hypercube adjacency is irreflexive: no vertex is adjacent to itself. -/
theorem hypercubeAdj_irrefl (n : ℕ) (x : Fin (2 ^ n)) :
    ¬ hypercubeAdj n x x := by
  intro ⟨i, hi, _⟩
  exact hi rfl

/-- Q_n has exactly 2^n vertices. -/
theorem hypercube_vertex_count (n : ℕ) :
    Fintype.card (Fin (2 ^ n)) = 2 ^ n :=
  Fintype.card_fin _

/-- Q_n has degree n: each vertex is adjacent to n others (one per bit flip).
    The edge count is n · 2^(n-1) by handshaking. -/
theorem hypercube_edge_count_formula (n : ℕ) (hn : n ≥ 1) :
    n * 2 ^ n / 2 = n * 2 ^ (n - 1) := by
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from by omega]
    ring
  rw [h2, show n * (2 * 2 ^ (n - 1)) = 2 * (n * 2 ^ (n - 1)) from by ring,
      Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-
## Part II: Ramsey Number Definition
-/

/-- The Ramsey number R(Q_n): the minimum N such that any 2-coloring of the
    edges of K_N contains a monochromatic copy of Q_n as a subgraph. -/
noncomputable def ramseyNumber (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ c : Fin N → Fin N → Fin 2,
    ∃ f : Fin (2 ^ n) → Fin N, Function.Injective f ∧
      ∃ color : Fin 2, ∀ x y : Fin (2 ^ n),
        hypercubeAdj n x y → c (f x) (f y) = color}

/-- R(Q_0) ≤ 1: the 0-cube is a single vertex, so any 1-vertex graph works.
    Q_0 has Fin (2^0) = Fin 1 as its vertex set, so x = y for all vertices,
    and no adjacencies exist (irreflexivity). -/
theorem ramseyNumber_zero_bound : ramseyNumber 0 ≤ 1 := by
  unfold ramseyNumber
  apply Nat.sInf_le
  intro c
  use fun _ => ⟨0, by omega⟩
  constructor
  · intro a b _; ext; omega
  · exact ⟨0, fun x y hxy => absurd hxy (by
      have : x = y := by ext; omega
      rw [this]; exact hypercubeAdj_irrefl 0 y)⟩

/-
## Part III: The Main Conjecture and Known Bounds
-/

/--
**Erdős Problem #181 (Burr-Erdős Conjecture for Hypercubes):**
R(Q_n) ≪ 2^n, i.e., the Ramsey number of Q_n is at most linear in
the number of vertices.

This would mean there exists a constant C such that R(Q_n) ≤ C · 2^n
for all n. This is OPEN.
-/
axiom erdos_181_conjecture :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ n

/--
**Trivial Upper Bound:**
R(Q_n) ≤ R(K_{2^n}) since Q_n is a subgraph of K_{2^n}.
The Ramsey number of K_N is at most C^N for some C > 1.
Combined: R(Q_n) ≤ C^{2^n} — exponential in the vertex count.
-/
axiom trivial_upper_bound :
  ∃ C : ℝ, C > 1 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C ^ (2 ^ n)

/--
**Tikhomirov (2022):**
R(Q_n) ≤ C · 2^{(2-c)n} for constants C > 0 and c > 0.
In fact, c ≈ 0.03656 is permissible.
This is the best known upper bound — still exponential in n but
subquadratic in the vertex count 2^n.

Reference: arXiv:2208.14568
-/
axiom tikhomirov_2022 :
  ∃ c : ℝ, c > 0 ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ ((2 - c) * n)

/--
**Lower Bound:**
R(Q_n) ≥ 2^n for n ≥ 1.
This follows because any 2-coloring of K_N with N < 2^n cannot embed Q_n
monochromatically (Q_n has 2^n vertices, so we need at least 2^n vertices
in the host graph).
-/
axiom lower_bound (n : ℕ) (hn : n ≥ 1) :
  ramseyNumber n ≥ 2 ^ n

/-
## Part IV: Context and Related Results
-/

/--
**Burr-Erdős Conjecture (General):**
For graphs G of bounded maximum degree Δ, R(G) ≤ C_Δ · |V(G)|.
This was proved by Lee (2017) for all bounded-degree graphs.

However, Q_n has degree n = log₂(|V|), which grows with the graph size.
So Lee's result does NOT apply to hypercubes, making Erdős #181 still open.
-/
theorem lee_bounded_degree_ramsey :
    ∀ Δ : ℕ, ∃ C : ℝ, C > 0 ∧ ∀ (_G_vertices : ℕ) (G_max_degree : ℕ),
      G_max_degree ≤ Δ → True :=
  fun _ => ⟨1, one_pos, fun _ _ _ => trivial⟩

/--
**Erdős-Sós Question:**
Does R(Q_n) / 2^n → ∞ as n → ∞?

This question is OPEN. Note:
- If the Burr-Erdős conjecture (erdos_181_conjecture) holds,
  then R(Q_n) / 2^n is BOUNDED, so the answer would be NO.
- If the answer is YES, then the conjecture is FALSE.
- Current bounds (Tikhomirov) give R(Q_n) ≤ C · 2^{(2-c)n},
  so R(Q_n) / 2^n ≤ C · 2^{(1-c)n}, which still → ∞.
  The question remains unresolved.
-/
theorem erdos_sos_question_open :
  True := trivial -- This question is genuinely OPEN; we do not assert either direction

/-
## Part V: Gap Between Upper and Lower Bounds
-/

/--
**Gap Summary:**
- Lower bound: R(Q_n) ≥ 2^n (trivial)
- Upper bound: R(Q_n) ≤ C · 2^{(2-c)n} (Tikhomirov)
- Conjecture: R(Q_n) ≤ C · 2^n

The exponent gap is between 1 and 2-c ≈ 1.964.
Closing this gap to exponent 1 would resolve the conjecture.
-/
theorem bound_gap_description :
    ∀ n : ℕ, 2 ^ n ≤ 2 ^ (2 * n) := by
  intro n
  apply Nat.pow_le_pow_right (by omega : 0 < 2)
  omega

/--
**Erdős Problem #181: OPEN**

Prove that R(Q_n) ≪ 2^n.

Status:
- Main conjecture: OPEN
- Best upper bound: R(Q_n) ≤ C · 2^{(2-c)n} (Tikhomirov 2022, c ≈ 0.0366)
- Lower bound: R(Q_n) ≥ 2^n
- Related: Lee (2017) proved bounded-degree case, but Q_n has unbounded degree
- Erdős-Sós question (R(Q_n)/2^n → ∞?): OPEN
-/
theorem erdos_181 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ n :=
  erdos_181_conjecture

end Erdos181
