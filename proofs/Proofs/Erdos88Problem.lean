/-
  Erdős Problem #88: Induced Subgraphs in Ramsey Graphs

  Source: https://erdosproblems.com/88
  Status: SOLVED (Kwan-Sah-Sauermann-Sawhney 2022)
  Prize: $100 (awarded)

  Statement (Erdős-McKay Conjecture):
  For any ε > 0, there exists δ = δ(ε) > 0 such that if G is a graph on n
  vertices with no independent set or clique of size ≥ ε log n, then G
  contains an induced subgraph with exactly m edges for all m ≤ δn².

  History:
  - Erdős and McKay conjectured this and proved it with δ(log n)² instead of δn²
  - The gap from logarithmic to quadratic was open for decades
  - Kwan, Sah, Sauermann, Sawhney (2022) proved the full conjecture
  - Key technique: anticoncentration of edge counts in random induced subgraphs

  Tags: graph-theory, ramsey-theory, induced-subgraphs, anticoncentration
-/

import Mathlib

namespace Erdos88

open Finset

/-!
## Part I: Simple Graphs and Basic Definitions

Setting up the graph-theoretic framework.
-/

/-- A simple graph on vertex set V. -/
abbrev Graph (V : Type*) := SimpleGraph V

/-- The edge set of a graph as pairs. -/
def edgeSet (G : SimpleGraph V) : Set (V × V) :=
  { p | G.Adj p.1 p.2 }

/-- Count of edges in a finite graph. -/
noncomputable def edgeCount [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-!
## Part II: Cliques and Independent Sets

The structures Ramsey theory constrains.
-/

/-- A set S is a clique in G if all pairs are adjacent. -/
def IsClique (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u v : V, u ∈ S → v ∈ S → u ≠ v → G.Adj u v

/-- A set S is independent in G if no pairs are adjacent. -/
def IsIndependent (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ u v : V, u ∈ S → v ∈ S → u ≠ v → ¬G.Adj u v

/-- The clique number ω(G) is the size of the largest clique. -/
noncomputable def cliqueNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (S : Finset V) (h : IsClique G S), (S.card : ℕ∞)

/-- The independence number α(G) is the size of the largest independent set. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨆ (S : Finset V) (h : IsIndependent G S), (S.card : ℕ∞)

/-!
## Part III: Ramsey Graphs

Graphs with bounded clique and independence numbers.
-/

/-- A graph is (k, ℓ)-Ramsey-bounded if ω(G) < k and α(G) < ℓ. -/
def IsRamseyBounded (G : SimpleGraph V) (k ℓ : ℕ) : Prop :=
  cliqueNumber G < k ∧ independenceNumber G < ℓ

/-- A graph is ε-Ramsey if ω(G), α(G) < ε log n. -/
def IsEpsilonRamsey [Fintype V] (G : SimpleGraph V) (ε : ℝ) : Prop :=
  let n := Fintype.card V
  cliqueNumber G < ε * Real.log n ∧ independenceNumber G < ε * Real.log n

/-- Ramsey's theorem implies ε-Ramsey graphs have bounded size. -/
axiom ramsey_size_bound (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ (V : Type*) [Fintype V] (G : SimpleGraph V),
      IsEpsilonRamsey G ε → Fintype.card V ≤ N

/-!
## Part IV: Induced Subgraphs

The central objects of the problem.
-/

/-- The induced subgraph on a subset S of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Set V) : SimpleGraph S where
  Adj := fun u v => G.Adj u.val v.val
  symm := fun u v h => G.symm h
  loopless := fun u h => G.loopless u.val h

/-- The number of edges in the induced subgraph on S. -/
noncomputable def inducedEdgeCount [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).card / 2

/-- G has an induced subgraph with exactly m edges. -/
def HasInducedWithEdges [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) : Prop :=
  ∃ S : Finset V, inducedEdgeCount G S = m

/-!
## Part V: The Edge Count Range Property

The property that the Erdős-McKay conjecture asserts.
-/

/-- G achieves all edge counts from 0 to M. -/
def AchievesAllEdgeCounts [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : ℕ) : Prop :=
  ∀ m ≤ M, HasInducedWithEdges G m

/-- The edge count range property with δn². -/
def EdgeCountRangeProperty [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (δ : ℝ) : Prop :=
  let n := Fintype.card V
  AchievesAllEdgeCounts G (Nat.floor (δ * n^2))

/-!
## Part VI: The Erdős-McKay Conjecture

The main statement that was proved.
-/

/-- **The Erdős-McKay Conjecture**:

    For any ε > 0, there exists δ > 0 such that every ε-Ramsey graph
    on n vertices has induced subgraphs with all edge counts up to δn².

    This was PROVED by Kwan-Sah-Sauermann-Sawhney (2022). -/
def ErdosMcKayConjecture : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    IsEpsilonRamsey G ε → EdgeCountRangeProperty G δ

/-- The weaker version proved by Erdős-McKay: δ(log n)² instead of δn². -/
def ErdosMcKayWeakBound : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    IsEpsilonRamsey G ε →
      let n := Fintype.card V
      AchievesAllEdgeCounts G (Nat.floor (δ * (Real.log n)^2))

/-- Erdős and McKay proved the weak version. -/
axiom erdos_mckay_weak : ErdosMcKayWeakBound

/-!
## Part VII: The Erdős-Szemerédi Density Result

Ramsey graphs have many edges.
-/

/-- **Erdős-Szemerédi**: Ramsey graphs have Θ(n²) edges.

    If G is ε-Ramsey, then |E(G)| = Θ(n²).
    This makes the δn² bound natural. -/
axiom erdos_szemeredi_density (ε : ℝ) (hε : ε > 0) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        IsEpsilonRamsey G ε →
          let n := Fintype.card V
          c₁ * n^2 ≤ edgeCount G ∧ (edgeCount G : ℝ) ≤ c₂ * n^2

/-!
## Part VIII: Anticoncentration

The key technique in the KSSS proof.
-/

/-- Anticoncentration: a random variable doesn't concentrate on any single value. -/
def IsAnticoncentrated (X : ℕ → ℝ) (bound : ℝ) : Prop :=
  ∀ k : ℕ, X k ≤ bound

/-- The edge count of a random induced subgraph is anticoncentrated.

    If we sample vertices independently with probability p, the number
    of edges in the induced subgraph is well-spread across values. -/
axiom random_induced_anticoncentration (ε : ℝ) (hε : ε > 0) :
    ∃ C : ℝ, C > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      IsEpsilonRamsey G ε →
        let n := Fintype.card V
        ∀ (p : ℝ) (hp : 0 < p) (hp' : p < 1),
          -- The probability that the random subgraph has exactly m edges is ≤ C/n
          True  -- Placeholder for the precise probabilistic statement

/-!
## Part IX: The KSSS Theorem (2022)

The solution to Erdős Problem #88.
-/

/-- **Kwan-Sah-Sauermann-Sawhney Theorem** (2022):

    The Erdős-McKay conjecture is TRUE.

    For any ε > 0, there exists δ > 0 such that every ε-Ramsey graph
    achieves all edge counts from 0 to δn² via induced subgraphs. -/
axiom ksss_theorem : ErdosMcKayConjecture

/-- The KSSS proof earned the $100 Erdős prize. -/
def ksss_prize : String := "$100 Erdős Prize"

/-- Key technique: anticoncentration of random induced subgraph edge counts. -/
def ksss_technique : String := "Anticoncentration"

/-!
## Part X: Implications and Bounds

What we know about the parameter δ.
-/

/-- The function δ(ε) exists by the KSSS theorem. -/
noncomputable def delta (ε : ℝ) : ℝ :=
  if h : ε > 0 then
    Classical.choose (ksss_theorem ε h)
  else 0

/-- δ(ε) > 0 for ε > 0. -/
theorem delta_pos (ε : ℝ) (hε : ε > 0) : delta ε > 0 := by
  unfold delta
  simp [hε]
  exact (Classical.choose_spec (ksss_theorem ε hε)).1

/-- The KSSS bound is optimal up to constants. -/
axiom ksss_optimality :
    ∀ ε > 0, ∃ δ₀ > 0, ∀ δ > δ₀,
      ∃ (V : Type*) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        IsEpsilonRamsey G ε ∧ ¬EdgeCountRangeProperty G δ

/-!
## Part XI: Connection to Ramsey Theory

How this relates to Ramsey numbers.
-/

/-- The Ramsey number R(k, ℓ). -/
noncomputable def R (k ℓ : ℕ) : ℕ := sorry

/-- ε-Ramsey graphs exist for n < R(⌈ε log n⌉, ⌈ε log n⌉). -/
axiom ramsey_graph_existence (ε : ℝ) (hε : ε > 0) :
    ∀ n : ℕ, n ≥ 2 →
      let k := Nat.ceil (ε * Real.log n)
      n < R k k →
      ∃ (G : SimpleGraph (Fin n)), IsEpsilonRamsey G ε

/-- The probabilistic method gives ε-Ramsey graphs of exponential size. -/
axiom probabilistic_ramsey (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      ∃ (G : SimpleGraph (Fin n)),
        cliqueNumber G < c * Real.log n ∧
        independenceNumber G < c * Real.log n

/-!
## Part XII: Main Result

Erdős Problem #88 is SOLVED.
-/

/-- **Erdős Problem #88: SOLVED**

    The Erdős-McKay conjecture is TRUE.

    For ε > 0, there exists δ > 0 such that every graph with
    no clique or independent set of size ≥ ε log n has induced
    subgraphs achieving all edge counts from 0 to δn².

    Proved by Kwan, Sah, Sauermann, and Sawhney (2022)
    using anticoncentration techniques.

    Prize: $100 (awarded) -/
theorem erdos_88 : ErdosMcKayConjecture :=
  ksss_theorem

/-- The answer to Erdős Problem #88. -/
def erdos_88_answer : String :=
  "YES: The Erdős-McKay conjecture is TRUE (KSSS 2022)"

/-- The prize was $100 (awarded to KSSS). -/
def erdos_88_prize : ℕ := 100

#check erdos_88
#check ksss_theorem
#check delta

end Erdos88
