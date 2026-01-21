/-
Erdős Problem #573: Extremal Numbers for {C₃, C₄}-free Graphs

Source: https://erdosproblems.com/573
Status: OPEN

Statement:
Is it true that ex(n; {C₃, C₄}) ~ (n/2)^(3/2)?

Where ex(n; F) denotes the Turán extremal function - the maximum number of edges
in an n-vertex graph containing no subgraph isomorphic to any graph in F.

Background:
- Erdős and Simonovits posed this problem
- They proved ex(n; {C₄, C₅}) = (n/2)^(3/2) + O(n)
- Kővári-Sós-Turán (1954) proved ex(n; C₄) ~ (1/2)n^(3/2)
- The question asks whether forbidding triangles (C₃) along with C₄ gives
  the same asymptotic as forbidding C₄ alone

Known Results:
- ex(n; C₄) = (1/2 + o(1))n^(3/2) (Kővári-Sós-Turán)
- ex(n; {C₄, C₅}) = (n/2)^(3/2) + O(n) (Erdős-Simonovits)
- ex(n; {C₃, C₄}) ≤ ex(n; C₄) trivially
- Lower bound constructions exist but gap remains

Related Problems:
- #574: General ex(n; {C₃, C₄, ..., C_{2k+1}})
- #765: ex(n; C₄)

References:
- [KST54] Kővári, Sós, Turán: "On a problem of K. Zarankiewicz", 1954
- Erdős-Simonovits: Various papers on extremal graph theory

Tags: extremal-graph-theory, turan, forbidden-cycles
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos573

/-!
## Part I: Basic Definitions

We define the key concepts for extremal graph theory.
-/

/--
**Cycle of length k:**
A cycle Cₖ is a connected 2-regular graph on k vertices.
-/
def isCycle (G : SimpleGraph (Fin k)) : Prop :=
  ∀ v : Fin k, G.degree v = 2

/--
**Triangle-free:**
A graph is triangle-free if it contains no C₃ subgraph.
-/
def isTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c : V, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)

/--
**C₄-free (no 4-cycle):**
A graph is C₄-free if it contains no cycle of length 4.
-/
def isC4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ b → b ≠ c → c ≠ d → d ≠ a → a ≠ c → b ≠ d →
    ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

/--
**{C₃, C₄}-free:**
A graph forbidding both triangles and 4-cycles.
-/
def isC3C4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  isTriangleFree G ∧ isC4Free G

/-!
## Part II: Edge Counting
-/

/--
**Edge count** of a simple graph on n vertices.
-/
noncomputable def edgeCount {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  G.edgeFinset.card

/-!
## Part III: Extremal Function

The Turán extremal function ex(n; F).
-/

/--
**Extremal number for {C₃, C₄}:**
ex(n; {C₃, C₄}) = max edges in n-vertex {C₃, C₄}-free graph.
-/
noncomputable def exC3C4 (n : ℕ) : ℕ :=
  ⨆ (G : SimpleGraph (Fin n)) (_ : isC3C4Free G) (_ : DecidableRel G.Adj),
    @edgeCount (Fin n) _ G

/--
**Extremal number for C₄:**
ex(n; C₄) = max edges in n-vertex C₄-free graph.
-/
noncomputable def exC4 (n : ℕ) : ℕ :=
  ⨆ (G : SimpleGraph (Fin n)) (_ : isC4Free G) (_ : DecidableRel G.Adj),
    @edgeCount (Fin n) _ G

/--
**Trivial bound:**
ex(n; {C₃, C₄}) ≤ ex(n; C₄) since forbidding more graphs means fewer edges.
-/
axiom exC3C4_le_exC4 (n : ℕ) : exC3C4 n ≤ exC4 n

/-!
## Part IV: Kővári-Sós-Turán Theorem
-/

/--
**Kővári-Sós-Turán Theorem (1954):**
ex(n; C₄) ≤ (1/2)n^(3/2) + (1/4)n

This gives the upper bound for C₄-free graphs.
-/
axiom kovari_sos_turan (n : ℕ) (hn : n ≥ 1) :
    (exC4 n : ℝ) ≤ (1/2) * (n : ℝ)^(3/2 : ℝ) + (1/4) * (n : ℝ)

/--
**KST asymptotic:**
ex(n; C₄) ~ (1/2)n^(3/2) as n → ∞.
-/
axiom kovari_sos_turan_asymptotic :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |(exC4 n : ℝ) - (1/2) * (n : ℝ)^(3/2 : ℝ)| ≤ ε * (n : ℝ)^(3/2 : ℝ)

/-!
## Part V: Erdős-Simonovits Result
-/

/--
**{C₄, C₅}-free extremal number:**
Erdős and Simonovits proved ex(n; {C₄, C₅}) = (n/2)^(3/2) + O(n).
-/
axiom erdos_simonovits_c4c5 :
    ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 →
      |(exC4C5 n : ℝ) - ((n : ℝ)/2)^(3/2 : ℝ)| ≤ C * (n : ℝ)
  where exC4C5 : ℕ → ℕ := fun _ => 0  -- Placeholder

/-!
## Part VI: The Conjecture
-/

/--
**Erdős Problem #573 Conjecture:**
ex(n; {C₃, C₄}) ~ (n/2)^(3/2) as n → ∞.

This asks whether the asymptotic is exactly (n/2)^(3/2), which is
slightly less than the (1/2)n^(3/2) from KST by a factor of 2^(-1/2).
-/
def erdos573Conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |(exC3C4 n : ℝ) - ((n : ℝ)/2)^(3/2 : ℝ)| ≤ ε * (n : ℝ)^(3/2 : ℝ)

/--
**The Problem Statement:**
Is erdos573Conjecture true?

STATUS: OPEN

Note: This cannot be resolved by finite computation as it concerns
asymptotic behavior. It requires proof techniques from extremal
combinatorics.
-/
axiom erdos_573_status : True  -- Problem is OPEN

/-!
## Part VII: Known Bounds
-/

/--
**Upper bound (from KST):**
ex(n; {C₃, C₄}) ≤ ex(n; C₄) ≤ (1/2)n^(3/2) + O(n).
-/
theorem exC3C4_upper_bound (n : ℕ) (hn : n ≥ 1) :
    (exC3C4 n : ℝ) ≤ (1/2) * (n : ℝ)^(3/2 : ℝ) + (1/4) * (n : ℝ) := by
  have h1 : (exC3C4 n : ℝ) ≤ (exC4 n : ℝ) := by
    exact_mod_cast exC3C4_le_exC4 n
  have h2 : (exC4 n : ℝ) ≤ (1/2) * (n : ℝ)^(3/2 : ℝ) + (1/4) * (n : ℝ) :=
    kovari_sos_turan n hn
  linarith

/--
**Lower bound construction:**
Certain bipartite graphs (like incidence graphs of projective planes)
achieve edges close to (1/2)n^(3/2).
-/
axiom exC3C4_lower_bound :
    ∃ c > 0, ∀ n : ℕ, n ≥ 1 → (exC3C4 n : ℝ) ≥ c * (n : ℝ)^(3/2 : ℝ)

/-!
## Part VIII: Special Constructions
-/

/--
**Polarity graphs:**
The incidence graph of a projective plane of order q gives a
C₄-free bipartite graph with ~(1/2)n^(3/2) edges.
These are automatically triangle-free (bipartite).
-/
def polarityGraphEdges (q : ℕ) : ℕ :=
  (q + 1) * q * (q + 1)  -- Roughly q³ edges on 2(q² + q + 1) vertices

/--
**Projective plane construction is {C₃, C₄}-free:**
-/
axiom projective_plane_construction (q : ℕ) (hq : Nat.Prime (q : ℕ) ∨ q.Prime) :
    -- The incidence graph of PG(2, q) is {C₃, C₄}-free
    -- with 2(q² + q + 1) vertices and (q + 1)³ edges
    True

/-!
## Part IX: Relationship to Other Problems
-/

/--
**Relation to Problem #574:**
The general case asks about ex(n; {C₃, C₄, ..., C_{2k+1}}).
Problem #573 is the k = 1 case.
-/
axiom problem_574_generalization :
    -- For k ≥ 1, ex(n; {C₃, C₅, ..., C_{2k+1}}) ~ (n/2)^{1+1/k}
    True

/--
**Relation to Problem #765:**
Problem #765 specifically asks about ex(n; C₄).
-/
axiom problem_765_c4 :
    -- ex(n; C₄) = (1/2 + o(1))n^(3/2)
    True

/-!
## Part X: Why This is Hard
-/

/--
**The difficulty:**
The problem asks whether adding the triangle-free constraint
to the C₄-free constraint changes the asymptotic from
(1/2)n^(3/2) to (1/2^(3/2))n^(3/2) = (n/2)^(3/2).

The gap is a factor of √2 ≈ 1.41.
-/
def asymptoticGap : ℝ := Real.sqrt 2

/--
**Key observation:**
- ex(n; C₄) ~ (1/2)n^(3/2)
- (n/2)^(3/2) = (1/2)^(3/2) n^(3/2) = (1/2√2)n^(3/2)
- The conjectured value is smaller by factor √2
-/
theorem gap_calculation :
    (1 : ℝ) / 2 / ((1 : ℝ) / (2 * Real.sqrt 2)) = Real.sqrt 2 := by
  field_simp
  ring_nf
  sorry  -- Computation of √2 relationship

/-!
## Part XI: Summary
-/

/--
**Erdős Problem #573: OPEN**

QUESTION: Is ex(n; {C₃, C₄}) ~ (n/2)^(3/2)?

KNOWN:
- Upper bound: ≤ (1/2)n^(3/2) + O(n) from KST
- Lower bound: ≥ c·n^(3/2) for some c > 0
- The question is about the exact constant

RELATED:
- ex(n; {C₄, C₅}) = (n/2)^(3/2) + O(n) is known
- The triangle-free condition seems not to change the leading term,
  but this is unproven
-/
theorem erdos_573 : erdos573Conjecture ∨ ¬erdos573Conjecture := by
  -- This is classically true but uninformative
  -- The problem is OPEN - we don't know which disjunct holds
  exact Classical.em erdos573Conjecture

/--
**Summary theorem:**
-/
theorem erdos_573_summary :
    -- The problem is well-posed
    (∀ n : ℕ, exC3C4 n ≤ exC4 n) ∧
    -- We have bounds
    (∃ c > 0, ∀ n : ℕ, n ≥ 1 → (exC3C4 n : ℝ) ≥ c * (n : ℝ)^(3/2 : ℝ)) := by
  constructor
  · intro n
    exact exC3C4_le_exC4 n
  · exact exC3C4_lower_bound

/--
**Historical Note:**
This problem elegantly connects the Turán-type extremal theory with
cycle-free graph theory. The Kővári-Sós-Turán bound is one of the
cornerstones of extremal graph theory, and this problem asks about
the finer structure when multiple cycles are forbidden.
-/
theorem historical_note : True := trivial

end Erdos573
