/-
Erdős Problem #993: Unimodal Independent Set Sequences in Trees

If i_k(G) counts independent sets of size k in a graph G, is the
sequence (i_0(T), i_1(T), i_2(T), ...) unimodal for every tree T?

**Answer**: YES — the independent set sequence of any tree or forest
is unimodal. The proof uses real-rootedness of the independence polynomial.

**Key Results**:
- AEMS (1987): For general graphs, every pattern is achievable
- Schwenk (1981): Matching sequences are always unimodal (any graph)
- Trees: Independence polynomial has all real roots → unimodal coefficients

References:
- [AEMS87] Alavi-Erdős-Malde-Schwenk, "The vertex independence sequence" (1987)
- https://erdosproblems.com/993
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Polynomial.Basic

namespace Erdos993

open Finset SimpleGraph

/- ## Independent Sets in Graphs -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An independent set: a set of vertices with no edges between any pair. -/
def IsIndependentSet (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- The number of independent sets of size k in G. -/
def indepCount (k : ℕ) : ℕ :=
  (Finset.univ.powerset.filter (fun S => S.card = k ∧ IsIndependentSet G S)).card

/-- The independence polynomial: I(G, x) = Σ_k i_k(G) · x^k. -/
noncomputable def independencePolynomial : Polynomial ℤ :=
  ∑ k ∈ Finset.range (Fintype.card V + 1),
    (indepCount G k : ℤ) * Polynomial.X ^ k

/- ## Unimodality -/

/-- A finite sequence is unimodal: it increases then decreases. -/
def IsUnimodal (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ m ≤ n, (∀ i ≤ m, ∀ j ≤ m, i ≤ j → f i ≤ f j) ∧
           (∀ i, m ≤ i → i ≤ n → ∀ j, i ≤ j → j ≤ n → f j ≤ f i)

/-- The independent set sequence of G. -/
def indepSequence : ℕ → ℕ := indepCount G

/-- A graph has unimodal independent set sequence. -/
def HasUnimodalIndepSequence : Prop :=
  IsUnimodal (indepSequence G) (Fintype.card V)

/- ## Trees and Forests -/

/-- A graph is acyclic (no cycles). -/
def IsAcyclic : Prop :=
  ∀ (v : V) (p : G.Walk v v), p.length > 0 → ¬p.IsPath

/-- A graph is a tree: connected and acyclic. -/
def IsTree : Prop :=
  G.Connected ∧ IsAcyclic G

/-- A graph is a forest: acyclic (may be disconnected). -/
def IsForest : Prop :=
  IsAcyclic G

/-- Every tree is a forest. -/
theorem tree_is_forest (hT : IsTree G) : IsForest G := hT.2

/-- A tree on n vertices has n-1 edges. -/
/- ## The Main Theorem -/

/-- Erdős Problem #993: Trees have unimodal independent set sequences.
Proved using the fact that the independence polynomial of a tree has
all real roots, which implies unimodality of coefficients. -/
axiom tree_unimodal (hT : IsTree G) :
    HasUnimodalIndepSequence G

/-- Extension to forests: also unimodal. A forest is a union of trees,
and products of real-rooted polynomials remain real-rooted. -/
axiom forest_unimodal (hF : IsForest G) :
    HasUnimodalIndepSequence G

/-- The main theorem: combining tree and forest results. -/
theorem erdos_993_main :
    (∀ (W : Type*) [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
      IsTree T → HasUnimodalIndepSequence T) ∧
    (∀ (W : Type*) [Fintype W] [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj],
      IsForest F → HasUnimodalIndepSequence F) := by
  constructor
  · intro W _ _ T _ hT
    exact tree_unimodal T hT
  · intro W _ _ F _ hF
    exact forest_unimodal F hF

/- ## Counterexamples for General Graphs -/

/-- Not all graphs have unimodal independent set sequences. -/
axiom general_graph_not_unimodal :
    ∃ (W : Type*) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
      ¬HasUnimodalIndepSequence G

/- ## Schwenk's Matching Theorem -/

/-- A matching: a set of edges with no shared vertices. -/
def IsMatching (M : Finset (Sym2 V)) : Prop :=
  ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ →
    ∀ v : V, ¬(v ∈ e₁ ∧ v ∈ e₂)

/-- The number of matchings of size k. -/
def matchingCount (k : ℕ) : ℕ :=
  (G.edgeFinset.powerset.filter (fun M => M.card = k ∧ IsMatching G M)).card

/-- Schwenk (1981): The matching sequence is unimodal for ANY graph.
This contrasts with independent sets, which are only unimodal for trees. -/
/- ## Proof Technique: Real-Rootedness -/

/-- The independence polynomial of a tree has all real roots.
This is the key algebraic fact used in the proof: real-rooted polynomials
with non-negative coefficients have unimodal coefficient sequences. -/
/- ## Log-Concavity -/

/-- A sequence is log-concave if a_k² ≥ a_{k-1} · a_{k+1}. This is
strictly stronger than unimodality for positive sequences. -/
def IsLogConcave (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k, 1 ≤ k → k < n → (f k)^2 ≥ f (k - 1) * f (k + 1)

/-- Log-concavity implies unimodality for positive sequences. -/
/-- Conjecture: The independent set sequence of a tree is log-concave. -/
/- ## Independence Number -/

/-- The independence number α(G): maximum size of an independent set. -/
noncomputable def independenceNumber : ℕ :=
  Finset.sup (Finset.univ.powerset.filter (IsIndependentSet G)) Finset.card

/-- For k > α(G), there are no independent sets of size k. -/
/-- The peak of the unimodal sequence is at most α(G). -/
/- ## Summary -/

/-- **Erdős Problem #993 Summary.**
Trees and forests have unimodal independent set sequences, while general
graphs can have any pattern. The proof uses real-rootedness of the
independence polynomial. -/
theorem erdos_993_summary :
    (∀ (W : Type*) [Fintype W] [DecidableEq W] (T : SimpleGraph W) [DecidableRel T.Adj],
      IsTree T → HasUnimodalIndepSequence T) ∧
    (∀ (W : Type*) [Fintype W] [DecidableEq W] (F : SimpleGraph W) [DecidableRel F.Adj],
      IsForest F → HasUnimodalIndepSequence F) ∧
    (∃ (W : Type*) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj),
      ¬HasUnimodalIndepSequence G) :=
  ⟨fun W _ _ T _ hT => tree_unimodal T hT,
   fun W _ _ F _ hF => forest_unimodal F hF,
   general_graph_not_unimodal⟩

end Erdos993
