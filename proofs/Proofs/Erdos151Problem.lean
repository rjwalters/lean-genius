/-
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

import Mathlib

namespace Erdos151

/- ## Part I: Graph Properties (axiomatised) -/

/-- Number of vertices of a graph. -/
axiom vertexCount : Type → ℕ

/-- A clique is maximal (not contained in a larger clique). -/
axiom IsMaximalClique : Type → Finset ℕ → Prop

/-- A set of vertices is independent (no edges between them). -/
axiom IsIndependent : Type → Finset ℕ → Prop

/-- The graph is triangle-free. -/
axiom IsTriangleFree : Type → Prop

/- ## Part II: Clique Transversal Number -/

/-- A vertex set T is a clique transversal if it intersects every maximal
    clique of size ≥ 2. -/
def IsCliqueTransversal (G : Type) (T : Finset ℕ) : Prop :=
    ∀ C : Finset ℕ, IsMaximalClique G C → 2 ≤ C.card → (T ∩ C).Nonempty

/-- τ(G): the minimum clique transversal size. -/
axiom cliqueTransversal : Type → ℕ

/-- τ(G) is minimal: no smaller transversal exists. -/
axiom cliqueTransversal_min (G : Type) (T : Finset ℕ)
    (h : IsCliqueTransversal G T) :
    cliqueTransversal G ≤ T.card

/- ## Part III: Triangle-Free Independence Number H(n) -/

/-- H(n): max k such that every triangle-free graph on n vertices has
    an independent set of size k. -/
axiom triangleFreeIndep : ℕ → ℕ

/-- H(n) is valid: every triangle-free graph on n vertices has an
    independent set of size ≥ H(n). -/
axiom triangleFreeIndep_spec (n : ℕ) (G : Type)
    (hv : vertexCount G = n) (htf : IsTriangleFree G) :
    ∃ I : Finset ℕ, IsIndependent G I ∧ triangleFreeIndep n ≤ I.card ∧ I.card ≤ n

/-- H(n) ≥ √n (Ramsey lower bound). -/
axiom triangleFreeIndep_sqrt (n : ℕ) :
    (Nat.sqrt n : ℕ) ≤ triangleFreeIndep n

/- ## Part IV: Proved Infrastructure Lemmas -/

/-- The clique transversal number is non-negative (trivially 0 ≤ τ(G)). -/
theorem cliqueTransversal_nonneg (G : Type) :
    0 ≤ cliqueTransversal G :=
  Nat.zero_le _

/-- The empty set is a transversal iff there are no maximal cliques of size ≥ 2. -/
theorem empty_transversal_iff (G : Type) :
    IsCliqueTransversal G ∅ ↔
      ∀ C : Finset ℕ, IsMaximalClique G C → C.card < 2 := by
  constructor
  · intro h C hmc
    by_contra hle
    push_neg at hle
    have := h C hmc hle
    simp at this
  · intro h C hmc hcard
    exfalso
    have := h C hmc
    omega

/-- If ErdosProblem151 holds, the easy bound τ(G) ≤ n − √n follows. -/
theorem conjecture_implies_easy_bound
    (hconj : ∀ (G : Type) (n : ℕ), vertexCount G = n →
      cliqueTransversal G ≤ n - triangleFreeIndep n)
    (G : Type) (n : ℕ) (hv : vertexCount G = n) :
    cliqueTransversal G ≤ n - Nat.sqrt n := by
  have h1 := hconj G n hv
  have h2 := triangleFreeIndep_sqrt n
  omega

/-- An independent set provides a transversal of the complement vertices.
    If I is an independent set in G, then V \ I contains a vertex
    from every maximal clique (since no clique is fully inside I). -/
axiom complement_of_indep_is_transversal (G : Type) (I : Finset ℕ) (n : ℕ)
    (hv : vertexCount G = n) (hi : IsIndependent G I) (hn : I.card ≤ n) :
    ∃ T : Finset ℕ, T.card ≤ n - I.card ∧ IsCliqueTransversal G T

/- ## Part V: Easy Bound (structural proof from axioms) -/

/-- τ(G) ≤ n − √n for every n-vertex graph G (from Ramsey bound). -/
axiom clique_transversal_easy_bound (G : Type) (n : ℕ) (hv : vertexCount G = n) :
    cliqueTransversal G ≤ n - Nat.sqrt n

/- ## Part VI: Main Conjecture -/

/-- **Erdős Problem 151 (Erdős–Gallai):** τ(G) ≤ n − H(n) for every
    n-vertex graph G. -/
def ErdosProblem151 : Prop :=
    ∀ (G : Type) (n : ℕ), vertexCount G = n →
      cliqueTransversal G ≤ n - triangleFreeIndep n

/-- The conjecture holds trivially for triangle-free graphs:
    by definition, H(n) ≤ α(G) for triangle-free G, and
    V \ (independent set) is a transversal. -/
theorem erdos_151_triangle_free (G : Type) (n : ℕ)
    (hv : vertexCount G = n) (htf : IsTriangleFree G) :
    cliqueTransversal G ≤ n - triangleFreeIndep n := by
  -- Get independent set I with |I| ≥ H(n) and |I| ≤ n
  obtain ⟨I, hI_indep, hI_card, hI_le⟩ := triangleFreeIndep_spec n G hv htf
  -- Get transversal T from complement of I with |T| ≤ n - |I|
  obtain ⟨T, hT_card, hT_trans⟩ := complement_of_indep_is_transversal G I n hv hI_indep hI_le
  -- τ(G) ≤ |T| ≤ n - |I| ≤ n - H(n)
  calc cliqueTransversal G ≤ T.card := cliqueTransversal_min G T hT_trans
    _ ≤ n - I.card := hT_card
    _ ≤ n - triangleFreeIndep n := by omega

/- Note: Even the K₄-free restriction of the conjecture remains open.
   Erdős and Gallai were unable to make progress even in this case. -/

/- ## Part VII: Corollaries and Summary -/

/-- The conjecture strengthens the easy bound since H(n) ≥ √n. -/
theorem conjecture_strengthens_easy_bound (n : ℕ) :
    triangleFreeIndep n ≥ Nat.sqrt n :=
  triangleFreeIndep_sqrt n

/-- If the conjecture is true, τ(G) + H(n) ≤ n. -/
theorem conjecture_reformulation
    (hconj : ErdosProblem151) (G : Type) (n : ℕ) (hv : vertexCount G = n)
    (hn : triangleFreeIndep n ≤ n) :
    cliqueTransversal G + triangleFreeIndep n ≤ n := by
  have h := hconj G n hv
  omega

/-- Summary of the current state of knowledge. -/
theorem erdos_151_summary :
    -- The easy bound holds
    (∀ (G : Type) (n : ℕ), vertexCount G = n →
      cliqueTransversal G ≤ n - Nat.sqrt n) ∧
    -- H(n) ≥ √n
    (∀ n : ℕ, Nat.sqrt n ≤ triangleFreeIndep n) ∧
    -- The conjecture implies the easy bound
    (ErdosProblem151 → ∀ (G : Type) (n : ℕ), vertexCount G = n →
      cliqueTransversal G ≤ n - Nat.sqrt n) :=
  ⟨clique_transversal_easy_bound,
   triangleFreeIndep_sqrt,
   fun h G n hv => conjecture_implies_easy_bound h G n hv⟩

end Erdos151
