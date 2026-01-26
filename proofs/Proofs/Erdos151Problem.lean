/-!
# Erdős Problem #151 — Clique Transversal Number and Triangle-Free Independence

For a graph G, let τ(G) be the clique transversal number: the minimum
number of vertices hitting every maximal clique of size ≥ 2.

Let H(n) be the maximum independent set size guaranteed in every
triangle-free graph on n vertices. (By Ramsey theory, H(n) ~ √n.)

## Conjecture (Erdős–Gallai)

τ(G) ≤ n − H(n) for every graph G on n vertices.

## Known results

- τ(G) ≤ n − √n (easy)
- The conjecture holds trivially for triangle-free graphs
- Even K₄-free case is open
- Erdős: "perhaps completely wrongheaded"

Reference: https://erdosproblems.com/151
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Graph properties (axiomatised) -/

/-- Number of vertices of a graph. -/
axiom vertexCount : Type → ℕ

/-- A set of vertices is a clique. -/
axiom IsClique : Type → Finset ℕ → Prop

/-- A clique is maximal (not contained in a larger clique). -/
axiom IsMaximalClique : Type → Finset ℕ → Prop

/-- A set of vertices is independent (no edges between them). -/
axiom IsIndependent : Type → Finset ℕ → Prop

/-- The graph is triangle-free. -/
axiom IsTriangleFree : Type → Prop

/-! ## Clique transversal number -/

/-- A vertex set T is a clique transversal if it intersects every maximal
    clique of size ≥ 2. -/
def IsCliqueTransversal (G : Type) (T : Finset ℕ) : Prop :=
    ∀ C : Finset ℕ, IsMaximalClique G C → 2 ≤ C.card → (T ∩ C).Nonempty

/-- τ(G): the minimum clique transversal size. -/
axiom cliqueTransversal : Type → ℕ

/-- τ(G) is achievable: there exists a transversal of this size. -/
axiom cliqueTransversal_spec (G : Type) :
    ∃ T : Finset ℕ, T.card = cliqueTransversal G ∧ IsCliqueTransversal G T

/-! ## Triangle-free independence number H(n) -/

/-- H(n): max k such that every triangle-free graph on n vertices has
    an independent set of size k. -/
axiom triangleFreeIndep : ℕ → ℕ

/-- H(n) is valid: every triangle-free graph on n vertices has an
    independent set of size ≥ H(n). -/
axiom triangleFreeIndep_spec (n : ℕ) (G : Type)
    (hv : vertexCount G = n) (htf : IsTriangleFree G) :
    ∃ I : Finset ℕ, IsIndependent G I ∧ triangleFreeIndep n ≤ I.card

/-- H(n) ≥ √n (Ramsey lower bound). -/
axiom triangleFreeIndep_sqrt (n : ℕ) :
    (Nat.sqrt n : ℕ) ≤ triangleFreeIndep n

/-! ## Easy bound -/

/-- τ(G) ≤ n − √n for every n-vertex graph G. -/
axiom clique_transversal_easy_bound (G : Type) (n : ℕ) (hv : vertexCount G = n) :
    cliqueTransversal G ≤ n - Nat.sqrt n

/-! ## Main conjecture -/

/-- Erdős Problem 151 (Erdős–Gallai): τ(G) ≤ n − H(n) for every
    n-vertex graph G. -/
def ErdosProblem151 : Prop :=
    ∀ (G : Type) (n : ℕ), vertexCount G = n →
      cliqueTransversal G ≤ n - triangleFreeIndep n

/-- The conjecture holds trivially for triangle-free graphs. -/
axiom erdos_151_triangle_free (G : Type) (n : ℕ)
    (hv : vertexCount G = n) (htf : IsTriangleFree G) :
    cliqueTransversal G ≤ n - triangleFreeIndep n
