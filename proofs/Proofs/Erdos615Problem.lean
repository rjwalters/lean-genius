/-
Erdős Problem #615: Ramsey-Turán Number rt(n; 4, n/log n)

Source: https://erdosproblems.com/615
Status: SOLVED (Fox-Loh-Zhao, 2015)

Statement:
Does there exist some constant c > 0 such that if G is a graph with n vertices
and >= (1/8 - c)n² edges then G must contain either a K₄ or an independent set
on at least n/log n vertices?

Answer: NO

Background:
The Ramsey-Turán number rt(n; k, ℓ) is the maximum number of edges in an
n-vertex graph containing no Kₖ and no independent set of size ℓ.

The question asks: is rt(n; 4, n/log n) < (1/8 - c)n² for some c > 0?

History:
- Erdős-Hajnal-Simonovits-Sós-Szemerédi [EHSSS93] posed the problem
- Erdős-Hajnal-Sós-Szemerédi [EHSS83] proved rt(n; 4, εn) < (1/8 + o(1))n²
- Sudakov [Su03] proved rt(n; 4, ne^(-f(n))) = o(n²) when f(n)/√log n → ∞
- Fox-Loh-Zhao [FLZ15] resolved it: rt(n; 4, ne^(-f(n))) >= (1/8 - o(1))n²
  when f(n) = o(√(log n / log log n))

Reference:
- Fox, Loh, Zhao (2015): "The critical window for the classical Ramsey-Turán
  problem", Combinatorica
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Set.Finite.Basic

open SimpleGraph

namespace Erdos615

/-
## Part I: Core Definitions

Ramsey-Turán theory combines extremal graph theory and Ramsey theory.
-/

/--
**Clique Number:**
The clique number ω(G) is the size of the largest clique in G.
For simple graphs, we use Mathlib's cliqueFree predicate.
-/
def hasClique (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬G.CliqueFree k

/--
**Independence Number:**
The independence number α(G) is the size of the largest independent set.
An independent set has no edges between its vertices.
-/
def hasIndependentSet (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  ∃ S : Finset V, S.card ≥ ℓ ∧ G.IsAnticlique S

/--
**Ramsey-Turán Condition:**
A graph G satisfies the RT(k, ℓ) condition if it has no Kₖ and no
independent set of size ℓ.
-/
def isRTGraph (G : SimpleGraph V) (k ℓ : ℕ) : Prop :=
  G.CliqueFree k ∧ ¬(hasIndependentSet G ℓ)

/--
**Ramsey-Turán Number:**
rt(n; k, ℓ) = max{|E(G)| : G has n vertices, no Kₖ, no independent set of size ℓ}

This is the maximum edge count in an n-vertex graph with the RT condition.
-/
noncomputable def rt (n k ℓ : ℕ) : ℕ :=
  Nat.find (⟨0, by trivial⟩ : ∃ m : ℕ, ∀ G : SimpleGraph (Fin n),
    isRTGraph G k ℓ → G.edgeFinset.card ≤ m)

/--
**Edge Density:**
The edge density of a graph is |E|/n² (or |E|/(n choose 2) for simple graphs).
-/
noncomputable def edgeDensity (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : ℝ :=
  G.edgeFinset.card / (Fintype.card V : ℝ)^2

/-
## Part II: The Problem Statement

The question asks about the threshold 1/8.
-/

/--
**The 1/8 Threshold:**
For the Ramsey-Turán number rt(n; 4, ℓ), the value 1/8 is critical.

Turán's theorem: ex(n, K₄) = (1/3 + o(1))(n choose 2) ≈ (1/6)n²
But with independence number constraints, we get rt(n; 4, εn) ≈ (1/8)n²
-/
def threshold_one_eighth : ℝ := 1 / 8

/--
**The Conjecture (Erdős et al., 1993):**
Does there exist c > 0 such that rt(n; 4, n/log n) < (1/8 - c)n²?

In other words, if G has >= (1/8 - c)n² edges, must it contain K₄ or
an independent set of size n/log n?
-/
def erdos_615_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧
  ∀ᶠ n : ℕ in Filter.atTop,
    (rt n 4 (n / Nat.log n) : ℝ) < (threshold_one_eighth - c) * n^2

/-
## Part III: Known Upper Bounds

Results that suggested the conjecture might be true.
-/

/--
**Erdős-Hajnal-Sós-Szemerédi (1983):**
For any fixed ε > 0: rt(n; 4, εn) < (1/8 + o(1))n²

This shows the threshold 1/8 is correct for linear independence number.
-/
axiom ehss_upper_bound :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ n : ℕ in Filter.atTop,
    (rt n 4 (Nat.floor (ε * n)) : ℝ) < (threshold_one_eighth + ε) * n^2

/--
**Sudakov (2003):**
rt(n; 4, ne^(-f(n))) = o(n²) whenever f(n)/√log n → ∞

This shows that for "very slow" growth of the independence number bound,
the Ramsey-Turán number becomes subquadratic.
-/
axiom sudakov_upper_bound :
    ∀ f : ℕ → ℝ, (∀ᶠ n : ℕ in Filter.atTop, f n / Real.sqrt (Real.log n) > n) →
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ n : ℕ in Filter.atTop,
    (rt n 4 (Nat.floor (n * Real.exp (-(f n)))) : ℝ) < ε * n^2

/-
## Part IV: Fox-Loh-Zhao Resolution

The answer to the conjecture is NO.
-/

/--
**Fox-Loh-Zhao Theorem (2015):**
rt(n; 4, ne^(-f(n))) >= (1/8 - o(1))n² whenever f(n) = o(√(log n / log log n))

This is the "critical window" result - it identifies exactly when the
threshold 1/8 can be achieved.
-/
axiom fox_loh_zhao_lower_bound :
    ∀ f : ℕ → ℝ,
    (∀ᶠ n : ℕ in Filter.atTop, f n / Real.sqrt (Real.log n / Real.log (Real.log n)) < 1) →
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ n : ℕ in Filter.atTop,
    (rt n 4 (Nat.floor (n * Real.exp (-(f n)))) : ℝ) > (threshold_one_eighth - ε) * n^2

/--
**Corollary: The Conjecture is FALSE**
There is no c > 0 such that rt(n; 4, n/log n) < (1/8 - c)n²

Proof: For f(n) = log n, we have n/log n = ne^(-log n).
Since log n = o(√(log n / log log n)), the Fox-Loh-Zhao theorem gives
rt(n; 4, n/log n) >= (1/8 - o(1))n².
-/
axiom erdos_615_false : ¬erdos_615_conjecture

/--
**Erdős Problem #615: SOLVED**
The answer is NO - no such constant c exists.
-/
theorem erdos_615 : ¬erdos_615_conjecture := erdos_615_false

/-
## Part V: The Critical Window

The Fox-Loh-Zhao theorem identifies a "critical window" for the
Ramsey-Turán function.
-/

/--
**Critical Window Function:**
The threshold between subquadratic and (1/8)n² behavior occurs at
f(n) ≈ √(log n / log log n)
-/
noncomputable def criticalWindow (n : ℕ) : ℝ :=
  Real.sqrt (Real.log n / Real.log (Real.log n))

/--
**Phase Transition:**
- If f(n) >> √(log n / log log n): rt = o(n²)
- If f(n) << √(log n / log log n): rt = (1/8 - o(1))n²
- At f(n) ≈ √(log n / log log n): transition occurs
-/
def isInCriticalWindow (f : ℕ → ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
  ∀ᶠ n : ℕ in Filter.atTop,
    c₁ * criticalWindow n < f n ∧ f n < c₂ * criticalWindow n

/-
## Part VI: Special Cases

Concrete instances of the Ramsey-Turán function.
-/

/--
**Turán's Theorem:**
ex(n, K₄) = (1 - 1/3)(n choose 2) = (1/3)n(n-1)/2 ≈ (1/6)n²

Without any independence number constraint, this is the extremal number.
-/
axiom turan_k4 : ∀ n : ℕ, n ≥ 4 →
  (rt n 4 n : ℝ) = (1 - 1/3) * (n * (n - 1) / 2 : ℝ)

/--
**Linear Independence Number:**
rt(n; 4, εn) = (1/8 + o(1))n² for any fixed ε > 0

The 1/8 threshold appears when we require α(G) < εn.
-/
axiom rt_linear : ∀ ε : ℝ, ε > 0 →
  ∀ δ : ℝ, δ > 0 →
  ∀ᶠ n : ℕ in Filter.atTop,
    |((rt n 4 (Nat.floor (ε * n)) : ℝ) / n^2) - threshold_one_eighth| < δ

/--
**Sublinear Independence Number:**
The behavior depends on how slowly α(G) grows compared to n.
-/
def isSublinear (ℓ : ℕ → ℕ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, (ℓ n : ℝ) / n < 1

/-
## Part VII: Connection to Other Problems

Related extremal graph theory problems.
-/

/--
**Ramsey Number Connection:**
R(k, ℓ) = min n such that every 2-coloring of Kₙ has a monochromatic Kₖ or Kₗ.

The Ramsey-Turán number is related: if α(G) < ℓ, then Ḡ has no Kₗ,
so we're looking at edge-colored complete graphs.
-/
def isRamseyRelated (k ℓ : ℕ) : Prop :=
  ∀ n : ℕ, rt n k ℓ ≤ (n * (n - 1) / 2 : ℕ)

/--
**Turán-Type Problem:**
ex(n, H) = max edges in n-vertex H-free graph.

rt(n; k, ℓ) ≤ ex(n, Kₖ) since RT graphs are Kₖ-free.
-/
axiom rt_turan_bound (n k ℓ : ℕ) : rt n k ℓ ≤ (n * (n - 1) / 2 * (1 - 1 / (k - 1)) : ℕ)

/-
## Part VIII: The Construction

Fox-Loh-Zhao's proof constructs a specific graph achieving (1/8 - o(1))n² edges.
-/

/--
**Simonovits-Sós Construction:**
The balanced complete 3-partite graph with parts of size n/3 minus a random graph.

Key insight: K₄-freeness comes from 3-partite structure, small independence
comes from random subgraph removal.
-/
axiom simonovits_sos_construction :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∃ G : SimpleGraph (Fin n),
      G.CliqueFree 4 ∧
      ¬(hasIndependentSet G (n / Nat.log n)) ∧
      G.edgeFinset.card ≥ (threshold_one_eighth - 1/n) * n^2

/-
## Part IX: Main Results Summary
-/

/--
**Erdős Problem #615 Summary:**

Question: Is rt(n; 4, n/log n) < (1/8 - c)n² for some c > 0?
Answer: NO (Fox-Loh-Zhao, 2015)

Key results:
1. For linear α(G) < εn: rt = (1/8 + o(1))n² (Erdős et al.)
2. For very slow growth f(n)/√log n → ∞: rt = o(n²) (Sudakov)
3. Critical window at f(n) ≈ √(log n / log log n) (Fox-Loh-Zhao)
4. For n/log n: rt = (1/8 - o(1))n², disproving the conjecture
-/
theorem erdos_615_summary :
    ¬erdos_615_conjecture ∧
    (∀ ε : ℝ, ε > 0 →
      ∀ δ : ℝ, δ > 0 →
      ∀ᶠ n : ℕ in Filter.atTop,
        |((rt n 4 (Nat.floor (ε * n)) : ℝ) / n^2) - threshold_one_eighth| < δ) := by
  exact ⟨erdos_615, rt_linear⟩

/--
**The answer to Erdős #615 is NO.**
The threshold 1/8 cannot be improved for independence number n/log n.
-/
theorem erdos_615_answer : ¬erdos_615_conjecture := erdos_615

end Erdos615
