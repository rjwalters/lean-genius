/-
  Erdős Problem #58: Chromatic Number vs Odd Cycle Lengths

  Source: https://erdosproblems.com/58
  Status: SOLVED (Gyárfás 1992)

  Statement:
  If G is a graph which contains odd cycles of ≤ k different lengths,
  then χ(G) ≤ 2k+2, with equality iff G contains K_{2k+2}.

  History:
  - Bollobás-Erdős: Conjectured this result
  - Bollobás-Shelah: Confirmed for k=1
  - Gyárfás (1992): SOLVED - proved the full conjecture
    Also proved: if G is 2-connected, then G is K_{2k+2} or has vertex of degree ≤ 2k
  - Gao-Huo-Ma (2021): Stronger - χ(G) ≥ 2k+3 implies k+1 consecutive odd cycle lengths

  This file formalizes the definitions and main results.
-/

import Mathlib

open Set SimpleGraph

namespace Erdos58

variable {V : Type*}

/-! ## Core Definitions -/

/-- The set of all cycle lengths in a graph. -/
def cycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = n }

/-- The set of all odd cycle lengths in a graph. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n ∈ cycleLengths G | Odd n }

/-- The number of distinct odd cycle lengths in a graph. -/
noncomputable def numOddCycleLengths (G : SimpleGraph V) : ℕ :=
  (oddCycleLengths G).ncard

/-! ## Chromatic Number -/

/-- A graph is k-colorable if it admits a proper k-coloring. -/
def IsColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ u v, G.Adj u v → f u ≠ f v

/-- The chromatic number χ(G) (axiomatized for simplicity). -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ := sorry

/-- The chromatic number is the minimum k for which G is k-colorable. -/
axiom chromaticNumber_spec (G : SimpleGraph V) :
    IsColorable G (chromaticNumber G) ∧
    ∀ k < chromaticNumber G, ¬IsColorable G k

/-! ## Complete Graph -/

/-- G contains K_n as a subgraph (has a clique of size n). -/
def ContainsClique (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ S : Finset V, S.card = n ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-! ## Main Results -/

/--
**Gyárfás' Theorem (1992) - Upper Bound**:
If G has at most k distinct odd cycle lengths, then χ(G) ≤ 2k + 2.
-/
axiom gyarfas_upper_bound (G : SimpleGraph V) (k : ℕ) :
    numOddCycleLengths G ≤ k → chromaticNumber G ≤ 2 * k + 2

/--
**Gyárfás' Theorem (1992) - Equality Characterization**:
χ(G) = 2k + 2 with at most k odd cycle lengths iff G contains K_{2k+2}.
-/
axiom gyarfas_equality (G : SimpleGraph V) (k : ℕ) :
    (numOddCycleLengths G ≤ k ∧ chromaticNumber G = 2 * k + 2) ↔
    ContainsClique G (2 * k + 2)

/--
**Gyárfás' Structural Result (1992)**:
If G is 2-connected with at most k odd cycle lengths, then either:
1. G contains K_{2k+2}, or
2. G has a vertex of degree ≤ 2k
-/
axiom gyarfas_structural (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (k : ℕ)
    (h2conn : G.Connected)
    (hk : numOddCycleLengths G ≤ k) :
    ContainsClique G (2 * k + 2) ∨ (∃ v : V, G.degree v ≤ 2 * k)

/-! ## Special Cases -/

/--
**Bollobás-Shelah (k=1)**:
If G has at most 1 odd cycle length, then χ(G) ≤ 4.
-/
theorem bollobas_shelah (G : SimpleGraph V) :
    numOddCycleLengths G ≤ 1 → chromaticNumber G ≤ 4 := by
  intro h
  have := gyarfas_upper_bound G 1 h
  omega

/--
**Bipartite Case (k=0)**:
If G has no odd cycles, then χ(G) ≤ 2 (G is bipartite).
-/
theorem no_odd_cycles_bipartite (G : SimpleGraph V) :
    numOddCycleLengths G = 0 → chromaticNumber G ≤ 2 := by
  intro h
  have := gyarfas_upper_bound G 0 (by omega : numOddCycleLengths G ≤ 0)
  omega

/-! ## Strengthening: Gao-Huo-Ma (2021) -/

/-- A set of consecutive odd integers: {2m+1, 2m+3, ..., 2m+2count-1}. -/
def consecutiveOddLengths (start : ℕ) (count : ℕ) : Set ℕ :=
  { n | ∃ i < count, n = 2 * start + 2 * i + 1 }

/--
**Gao-Huo-Ma Theorem (2021)**:
If χ(G) ≥ 2k + 3, then G contains cycles of k+1 consecutive odd lengths.

This strengthens Gyárfás by showing high chromatic number forces
consecutive odd cycle lengths, not just many distinct ones.
-/
axiom gao_huo_ma (G : SimpleGraph V) (k : ℕ) :
    chromaticNumber G ≥ 2 * k + 3 →
    ∃ start : ℕ, consecutiveOddLengths start (k + 1) ⊆ oddCycleLengths G

/-! ## Corollaries -/

/-- If χ(G) ≥ 5, then G has at least 2 distinct odd cycle lengths. -/
theorem chi_5_two_odd_lengths (G : SimpleGraph V) :
    chromaticNumber G ≥ 5 → 2 ≤ numOddCycleLengths G := by
  intro h
  by_contra hlt
  push_neg at hlt
  have hbound := gyarfas_upper_bound G 1 (by omega : numOddCycleLengths G ≤ 1)
  omega

/-- If χ(G) = 2k+2 with ≤k odd cycle lengths, G has a (2k+2)-clique. -/
theorem equality_implies_clique (G : SimpleGraph V) (k : ℕ)
    (hk : numOddCycleLengths G ≤ k)
    (hchi : chromaticNumber G = 2 * k + 2) :
    ContainsClique G (2 * k + 2) := by
  rw [← gyarfas_equality]
  exact ⟨hk, hchi⟩

/-! ## Historical Notes

This problem relates chromatic number to the diversity of odd cycles.
- k=0: No odd cycles means bipartite (χ ≤ 2)
- k=1: At most one odd cycle length means χ ≤ 4 (Bollobás-Shelah)
- General k: At most k odd cycle lengths means χ ≤ 2k+2 (Gyárfás)

The Gao-Huo-Ma strengthening shows that high chromatic number forces
not just many odd cycle lengths, but specifically consecutive ones.

References:
- Gyárfás (1992): "Graphs with k odd cycle lengths"
- Gao-Huo-Ma (2021): "A strengthening on odd cycles in graphs of given chromatic number"
-/

end Erdos58
