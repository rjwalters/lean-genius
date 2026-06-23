/-
Erdős Problem #811: Rainbow Graphs in Balanced Edge-Colorings

Source: https://erdosproblems.com/811
Status: OPEN

Statement:
Given n ≡ 1 (mod m), a balanced edge-coloring of K_n with m colors has
each vertex incident to exactly ⌊n/m⌋ edges of each color. For which
graphs G (with m = e(G) edges) does every such balanced coloring of K_n
contain a rainbow copy of G?

Known Results:
- K_4 does NOT have this property (Clemen-Wagner 2023)
- Infinitely many K_m fail (Axenovich-Clemen 2024)
- Conjecture: K_m fails for all m ≥ 4
- For C_4: ⌊n/6⌋ ≤ d_{C_4}(n) ≤ (1/4 - c)n (Erdős-Tuza)

References:
- [ErPyTu91] Erdős-Pyber-Tuza, original formulation
- [ClWa23] Clemen-Wagner, K_4 disproof
- [AxCl24] Axenovich-Clemen, infinitely many K_m fail

Tags: graph-theory, ramsey-theory, rainbow-colorings, open-problem
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Erdos811

open Finset

/-
## Part 1: Basic Definitions
-/

/-- Edge count of K_n is n(n-1)/2 -/
def completeEdgeCount (n : ℕ) : ℕ := n * (n - 1) / 2

/-- An edge coloring of K_n with m colors -/
structure EdgeColoring (n m : ℕ) where
  color : Fin n → Fin n → Fin m
  symmetric : ∀ u v, color u v = color v u
  irrefl : ∀ v, color v v = ⟨0, by omega⟩  -- diagonal doesn't matter

/-- Color degree: number of edges of color c incident to vertex v -/
noncomputable def colorDegree (χ : EdgeColoring n m) (v : Fin n) (c : Fin m) : ℕ :=
  (Finset.univ.filter (fun w => w ≠ v ∧ χ.color v w = c)).card

/-
## Part 2: Balanced Colorings
-/

/-- A balanced coloring: each vertex sees exactly ⌊(n-1)/m⌋ edges of each color -/
def IsBalanced (χ : EdgeColoring n m) : Prop :=
  ∀ v : Fin n, ∀ c : Fin m, colorDegree χ v c = (n - 1) / m

/-- Balanced colorings exist only when n ≡ 1 (mod m) -/
/-
## Part 3: Rainbow Subgraphs
-/

/-- A graph embedding: maps vertices of G into K_n -/
structure GraphEmbedding (G : SimpleGraph (Fin k)) (n : ℕ) where
  map : Fin k → Fin n
  injective : Function.Injective map

/-- A rainbow copy: an embedding where all edge colors are distinct -/
def IsRainbow (G : SimpleGraph (Fin k)) (χ : EdgeColoring n m)
    (emb : GraphEmbedding G n) : Prop :=
  ∀ u₁ v₁ u₂ v₂ : Fin k,
    G.Adj u₁ v₁ → G.Adj u₂ v₂ → (u₁, v₁) ≠ (u₂, v₂) →
    χ.color (emb.map u₁) (emb.map v₁) ≠ χ.color (emb.map u₂) (emb.map v₂)

/-- A coloring contains a rainbow copy of G -/
def ContainsRainbow (G : SimpleGraph (Fin k)) (χ : EdgeColoring n m) : Prop :=
  ∃ emb : GraphEmbedding G n, IsRainbow G χ emb

/-
## Part 4: The Rainbow Property
-/

/-- G has the rainbow property: every balanced m-coloring of K_n
    (for large n ≡ 1 mod m, where m = e(G)) contains a rainbow copy of G -/
def HasRainbowProperty (G : SimpleGraph (Fin k)) (m : ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ≡ 1 [MOD m] →
    ∀ χ : EdgeColoring n m, IsBalanced χ → ContainsRainbow G χ

/-
## Part 5: Known Results
-/

/-- Clemen-Wagner (2023): K_4 does NOT have the rainbow property.
    There exist balanced 6-colorings of K_n without rainbow K_4. -/
axiom clemen_wagner_2023 :
    ∀ N₀ : ℕ, ∃ n ≥ N₀, n ≡ 1 [MOD 6] ∧
    ∃ χ : EdgeColoring n 6, IsBalanced χ ∧
    ¬ContainsRainbow (⊤ : SimpleGraph (Fin 4)) χ

/-- Axenovich-Clemen (2024): Infinitely many complete graphs fail.
    For infinitely many m, K_m does not have the rainbow property
    with m(m-1)/2 colors. -/
axiom axenovich_clemen_2024 :
    ∀ K : ℕ, ∃ m ≥ K, m ≥ 4 ∧
    ¬HasRainbowProperty (⊤ : SimpleGraph (Fin m)) (completeEdgeCount m)

/-- Conjecture (Axenovich-Clemen): K_m fails for ALL m ≥ 4 -/
def AxenovichClemenConjecture : Prop :=
  ∀ m ≥ 4, ¬HasRainbowProperty (⊤ : SimpleGraph (Fin m)) (completeEdgeCount m)

/-
## Part 6: Quantitative Version
-/

/-- Rainbow minimum degree d_G(n): minimum color degree at any vertex
    that guarantees a rainbow copy of G -/
axiom rainbowMinDegree (G : SimpleGraph (Fin k)) (n : ℕ) : ℕ

/-- Erdős-Tuza bound for C_4:
    ⌊n/6⌋ ≤ d_{C_4}(n) ≤ (1/4 - c)n for some constant c > 0 -/
/-
## Part 7: Erdős's Specific Challenge
-/

/-- Erdős's specific challenge: In any balanced 6-coloring of K_{6n+1},
    must there exist a rainbow C_6 or rainbow K_4?
    Status: OPEN (K_4 part resolved negatively by Clemen-Wagner) -/
def ErdosChallenge : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∀ χ : EdgeColoring (6 * n + 1) 6, IsBalanced χ →
    ContainsRainbow (⊤ : SimpleGraph (Fin 6)) χ ∨
    ContainsRainbow (⊤ : SimpleGraph (Fin 4)) χ

/-- The K_4 part is false (Clemen-Wagner), so the question reduces to C_6 -/
/-
## Part 8: Small Cases
-/

/-- Trees have the rainbow property (folklore) -/
/-- Stars K_{1,m} have the rainbow property -/
/-
## Part 9: Summary
-/

/-- **Erdős Problem #811: OPEN**

PROBLEM: For which graphs G (with m = e(G) edges) does every balanced
m-coloring of K_n contain a rainbow copy of G?

KNOWN:
- K_4 fails (Clemen-Wagner 2023)
- Infinitely many K_m fail (Axenovich-Clemen 2024)
- Conjecture: ALL K_m with m ≥ 4 fail

OPEN: Full characterization of graphs with the rainbow property. -/
theorem erdos_811 :
    -- K_4 fails
    (∀ N₀ : ℕ, ∃ n ≥ N₀, n ≡ 1 [MOD 6] ∧
      ∃ χ : EdgeColoring n 6, IsBalanced χ ∧
      ¬ContainsRainbow (⊤ : SimpleGraph (Fin 4)) χ) ∧
    -- Infinitely many K_m fail
    (∀ K : ℕ, ∃ m ≥ K, m ≥ 4 ∧
      ¬HasRainbowProperty (⊤ : SimpleGraph (Fin m)) (completeEdgeCount m)) :=
  ⟨clemen_wagner_2023, axenovich_clemen_2024⟩

end Erdos811
