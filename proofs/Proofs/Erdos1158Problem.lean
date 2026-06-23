/-
Erdős Problem #1158: Hypergraph Turán Lower Bound for K_t(r)

Source: https://erdosproblems.com/1158
Status: OPEN (only known for t=2 with r=2,3)

Statement:
Is it true that ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)}?

Here K_t(r) is the complete t-partite t-uniform hypergraph with r vertices
in each class, and ex_t(n, K_t(r)) is the hypergraph Turán number.

Known Results:
- Upper bound: ex_t(n, K_t(r)) ≤ O(n^{t - r^{1-t}}) [Erdős 1964]
- Lower bound: ex_t(n, K_t(r)) ≥ n^{t - O(r^{1-t})} [Erdős 1964]
- t=2: Reduces to the Zarankiewicz problem (Erdős #714)
  * r=2: Solved via projective planes (Kővári-Sós-Turán tight)
  * r=3: Solved by Brown (1966), Erdős-Rényi-Sós (1966)
  * r≥4: Open
- t≥3: All cases open

References:
- [Er64f] Erdős (1964): On extremal problems of graphs and generalized graphs
- [Va99, 3.65] Verstraëte survey
- See Problem #714 for the t=2 specialization
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos1158

/-
## Part I: t-Uniform Hypergraphs

A t-uniform hypergraph on vertex set V is a collection of t-element subsets
of V (called hyperedges).
-/

/--
A t-uniform hypergraph on vertex set V, represented as a set of t-element
subsets of V (stored as Finsets of exactly t elements).
-/
structure UniformHypergraph (V : Type*) [Fintype V] [DecidableEq V] (t : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = t

/-- The number of hyperedges in a t-uniform hypergraph. -/
def UniformHypergraph.edgeCount {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (H : UniformHypergraph V t) : ℕ :=
  H.edges.card

/-
## Part II: Complete Multipartite Hypergraphs K_t(r)

K_t(r) is the complete t-partite t-uniform hypergraph with r vertices per class.
It consists of all t-element sets that take exactly one vertex from each of the
t classes of size r. The total number of vertices is t·r, and the number of
hyperedges is r^t.
-/

/--
A t-uniform hypergraph H on vertex set V contains K_t(r) as a sub-hypergraph
if there exist t disjoint sets A₁, ..., A_t each of size r such that every
transversal (one vertex from each Aᵢ) forms a hyperedge of H.
-/
def containsKtr {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (H : UniformHypergraph V t) (r : ℕ) : Prop :=
  ∃ (parts : Fin t → Finset V),
    -- Each part has exactly r vertices
    (∀ i, (parts i).card = r) ∧
    -- Parts are pairwise disjoint
    (∀ i j, i ≠ j → Disjoint (parts i) (parts j)) ∧
    -- Every transversal is a hyperedge
    (∀ (f : Fin t → V), (∀ i, f i ∈ parts i) →
      (Finset.image f Finset.univ) ∈ H.edges)

/--
A t-uniform hypergraph is K_t(r)-free if it does not contain K_t(r).
-/
def isKtrFree {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}
    (H : UniformHypergraph V t) (r : ℕ) : Prop :=
  ¬containsKtr H r

/-
## Part III: The Hypergraph Turán Number

ex_t(n, K_t(r)) is the maximum number of hyperedges in a K_t(r)-free
t-uniform hypergraph on n vertices.
-/

/--
The hypergraph Turán number ex_t(n, K_t(r)):
the maximum number of edges in a K_t(r)-free t-uniform hypergraph on n vertices.
-/
noncomputable def exHypergraph (t n r : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    ∃ (H : @UniformHypergraph V ‹Fintype V› ‹DecidableEq V› t),
      @Fintype.card V ‹Fintype V› = n ∧
      @isKtrFree V ‹Fintype V› ‹DecidableEq V› t H r ∧
      @UniformHypergraph.edgeCount V ‹Fintype V› ‹DecidableEq V› t H = m}

/-
## Part IV: Known Upper Bound

Erdős [Er64f] established:
  ex_t(n, K_t(r)) ≤ C · n^{t - r^{1-t}}

for some constant C depending on t and r. This generalizes the
Kővári-Sós-Turán theorem to hypergraphs.
-/

/--
The conjectured exponent for the hypergraph Turán number:
  t - r^{1-t}

For t=2: this gives 2 - r^{-1} = 2 - 1/r (the KST exponent).
For t=3, r=2: this gives 3 - 2^{-2} = 3 - 1/4 = 11/4 = 2.75.
-/
noncomputable def hypergraphExponent (t r : ℕ) : ℝ :=
  (t : ℝ) - (r : ℝ)^(1 - (t : ℝ))

/--
Upper bound (Erdős 1964):
  ex_t(n, K_t(r)) ≤ C · n^{t - r^{1-t}}

This is the generalization of the Kővári-Sós-Turán theorem to
t-uniform hypergraphs.
-/
/-
## Part V: Known Lower Bound (Weaker)

Erdős also showed a weaker lower bound:
  ex_t(n, K_t(r)) ≥ n^{t - O(r^{1-t})}

The O(·) hides a constant depending on t. This lower bound is established
via probabilistic methods but the constant in the exponent is not tight.
-/

/--
Erdős's lower bound (1964):
  ex_t(n, K_t(r)) ≥ c · n^{t - C·r^{1-t}}

for constants c, C > 0 depending on t. The key gap with the upper bound
is the constant multiplying r^{1-t} in the exponent.
-/
/-
## Part VI: The Conjecture (Erdős Problem #1158)

The conjecture asks whether the upper bound is tight:
  ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)}

We formalize this as: for every ε > 0, there exists c > 0 such that
  ex_t(n, K_t(r)) ≥ c · n^{t - r^{1-t} - ε}
for all sufficiently large n.
-/

/--
**Erdős Problem #1158 (Conjecture):**
For all t ≥ 2 and r ≥ 2:
  ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)}

Formalized: for every ε > 0 there exists c > 0 and N₀ such that
  ex_t(n, K_t(r)) ≥ c · n^{t - r^{1-t} - ε}
for all n ≥ N₀.
-/
def erdos1158Conjecture (t r : ℕ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ (c : ℝ) (N₀ : ℕ), c > 0 ∧ ∀ n : ℕ, n ≥ N₀ →
      (exHypergraph t n r : ℝ) ≥ c * (n : ℝ) ^ (hypergraphExponent t r - ε)

/-
## Part VII: Reduction to the Graph Case (t = 2)

When t = 2, a 2-uniform hypergraph is simply a graph, K_2(r) = K_{r,r},
and ex_2(n, K_2(r)) = ex(n; K_{r,r}).

The conjecture becomes: ex(n; K_{r,r}) ≥ n^{2 - 1/r - o(1)}.
This is exactly Erdős Problem #714.
-/

/--
The t=2 exponent simplifies to the Kővári-Sós-Turán exponent:
  hypergraphExponent 2 r = 2 - 1/r
-/
theorem exponent_t2 (r : ℕ) (_hr : r ≥ 1) :
    hypergraphExponent 2 r = 2 - (r : ℝ)⁻¹ := by
  unfold hypergraphExponent
  have h : (1 : ℝ) - (↑(2 : ℕ) : ℝ) = -1 := by norm_num
  rw [h, Real.rpow_neg_one]
  push_cast; ring

/--
For t=2, r=2: the exponent is 3/2 (the Zarankiewicz exponent for C₄).
-/
theorem exponent_t2_r2 : hypergraphExponent 2 2 = 3 / 2 := by
  rw [exponent_t2 2 (by norm_num)]; norm_num

/--
For t=2, r=3: the exponent is 5/3 (Brown's exponent for K_{3,3}).
-/
theorem exponent_t2_r3 : hypergraphExponent 2 3 = 5 / 3 := by
  rw [exponent_t2 3 (by norm_num)]; norm_num

/-
## Part VIII: Known Cases of the Conjecture

The conjecture is only known when t = 2 and r ∈ {2, 3}.
-/

/--
**t=2, r=2 (Solved):**
ex(n; K_{2,2}) ≥ c · n^{3/2} for some c > 0.
Follows from projective plane constructions.
This confirms erdos1158Conjecture for t=2, r=2.
-/
axiom conjecture_t2_r2 : erdos1158Conjecture 2 2

/--
**t=2, r=3 (Solved):**
ex(n; K_{3,3}) ≥ c · n^{5/3} for some c > 0.
Proved by Brown (1966) and Erdős-Rényi-Sós (1966).
This confirms erdos1158Conjecture for t=2, r=3.
-/
axiom conjecture_t2_r3 : erdos1158Conjecture 2 3

/-
## Part IX: The Gap for t ≥ 3

For t ≥ 3, the best known lower bounds use the "stepping-up" lemma
of Erdős and Hajnal, but these give exponents strictly less than
t - r^{1-t}. The gap between upper and lower bounds grows with t.
-/

/--
**Stepping-up lemma (Erdős-Hajnal):**
If ex_{t-1}(n, K_{t-1}(r)) ≥ n^α then ex_t(n, K_t(r)) ≥ n^{α+1-o(1)}.

This converts (t-1)-uniform lower bounds to t-uniform ones,
but with a loss that compounds across uniformities.
-/
/-
## Part X: Summary
-/

/--
**Erdős Problem #1158 Status Summary:**

1. Conjecture: ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)} for all t, r ≥ 2
2. Upper bound: ex_t(n, K_t(r)) ≤ O(n^{t - r^{1-t}}) (Erdős 1964) ✓
3. Weaker lower bound: ex_t(n, K_t(r)) ≥ n^{t - Cr^{1-t}} for some C > 1 ✓
4. t=2, r=2: SOLVED (projective planes)
5. t=2, r=3: SOLVED (Brown 1966, Erdős-Rényi-Sós 1966)
6. t=2, r≥4: OPEN (see Problem #714)
7. t≥3, all r: OPEN
-/
theorem erdos_1158_known_cases :
    erdos1158Conjecture 2 2 ∧ erdos1158Conjecture 2 3 := by
  exact ⟨conjecture_t2_r2, conjecture_t2_r3⟩

/-
## Part XI: Structural Properties of the Exponent
-/

/--
The hypergraph exponent is strictly less than t for any r ≥ 2.
This follows because r^{1-t} > 0 for positive r, so subtracting it gives less than t.
-/
theorem exponent_lt_t (t r : ℕ) (_ht : t ≥ 2) (hr : r ≥ 2) :
    hypergraphExponent t r < (t : ℝ) := by
  unfold hypergraphExponent
  linarith [Real.rpow_pos_of_pos (show (0 : ℝ) < (r : ℝ) by positivity) ((1 : ℝ) - (t : ℝ))]

/--
The hypergraph exponent is at least t - 1 for r ≥ 1, t ≥ 1.
Since r ≥ 1 and 1 - t ≤ 0, we have r^{1-t} ≤ r^0 = 1, giving t - r^{1-t} ≥ t - 1.
-/
theorem exponent_ge_t_sub_one (t r : ℕ) (ht : t ≥ 1) (hr : r ≥ 1) :
    hypergraphExponent t r ≥ (t : ℝ) - 1 := by
  unfold hypergraphExponent
  have hr_cast : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have ht_cast : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h_rpow_le : (r : ℝ) ^ ((1 : ℝ) - (t : ℝ)) ≤ 1 := by
    calc (r : ℝ) ^ ((1 : ℝ) - (t : ℝ))
        ≤ (r : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hr_cast; linarith
      _ = 1 := Real.rpow_zero _
  linarith

/--
The hypergraph exponent is positive for t ≥ 2 and r ≥ 1.
Combining t ≥ 2 with r^{1-t} ≤ 1 gives t - r^{1-t} ≥ 2 - 1 = 1 > 0.
-/
theorem exponent_pos (t r : ℕ) (ht : t ≥ 2) (hr : r ≥ 1) :
    0 < hypergraphExponent t r := by
  have h := exponent_ge_t_sub_one t r (by omega) hr
  have : (1 : ℝ) ≤ (t : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  linarith

end Erdos1158
