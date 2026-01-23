/-
Erdős Problem #762: Chromatic vs Cochromatic Number

Source: https://erdosproblems.com/762
Status: DISPROVED (Steiner 2024)

Statement:
The cochromatic number ζ(G) is the minimum number of colors needed to color
vertices such that each color class induces either a complete graph or an
empty (independent) graph.

Conjecture (Erdős-Gimbel-Straight 1990):
If G has no K₅ (clique number ω(G) ≤ 4) and ζ(G) ≥ 4, then χ(G) ≤ ζ(G) + 2.

Answer: NO (Steiner 2024)

Counterexample: Steiner constructed a graph G with:
- ω(G) = 4 (no K₅)
- ζ(G) = 4
- χ(G) = 7

This shows χ(G) = 7 > 4 + 2 = 6 = ζ(G) + 2, disproving the conjecture.

Related Results:
- Erdős-Gimbel-Straight (1990): For every n > 2, there exists f(n) such that
  if ω(G) < n then χ(G) ≤ ζ(G) + f(n). The question was about specific bounds.

References:
- Erdős, Gimbel, Straight (1990): "Chromatic number versus cochromatic number"
- Steiner (2024): "On the difference between the chromatic and cochromatic number"
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic

open SimpleGraph

namespace Erdos762

/-!
## Part I: Basic Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Proper Coloring:**
A coloring where adjacent vertices have different colors.
-/
def IsProperColoring (G : SimpleGraph V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ v w, G.Adj v w → c v ≠ c w

/--
**Chromatic Number χ(G):**
The minimum number of colors for a proper coloring.
-/
axiom chromaticNumber (G : SimpleGraph V) : ℕ

/--
**Clique Number ω(G):**
The maximum size of a complete subgraph.
-/
axiom cliqueNumber (G : SimpleGraph V) : ℕ

/-!
## Part II: Cochromatic Coloring

The cochromatic number generalizes chromatic number by allowing color classes
to be either independent sets (no edges) OR cliques (all edges).
-/

/--
**Cochromatic Partition:**
A partition of vertices where each part induces either a complete graph or
an independent set.

More formally: for each color class C, either:
1. C is an independent set: no two vertices in C are adjacent, OR
2. C is a clique: every two distinct vertices in C are adjacent
-/
def IsCochromaticColorClass (G : SimpleGraph V) (C : Set V) : Prop :=
  -- Either C is an independent set (no edges)
  (∀ v w, v ∈ C → w ∈ C → v ≠ w → ¬G.Adj v w) ∨
  -- Or C is a clique (all edges)
  (∀ v w, v ∈ C → w ∈ C → v ≠ w → G.Adj v w)

/--
**Cochromatic Coloring:**
A coloring where each color class is either a clique or an independent set.
-/
def IsCochromaticColoring (G : SimpleGraph V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ i : Fin k, IsCochromaticColorClass G {v | c v = i}

/--
**Cochromatic Number ζ(G):**
The minimum number of colors for a cochromatic coloring.
-/
axiom cochromaticNumber (G : SimpleGraph V) : ℕ

/-!
## Part III: Relationship Between χ and ζ

Since proper coloring is a special case of cochromatic coloring
(all color classes are independent sets), we have χ(G) ≥ ζ(G).
-/

/-- Proper colorings are cochromatic colorings. -/
theorem proper_implies_cochromatic (G : SimpleGraph V) (k : ℕ) (c : V → Fin k) :
    IsProperColoring G k c → IsCochromaticColoring G k c := by
  intro hproper i
  -- Each color class is an independent set under proper coloring
  left
  intro v w hv hw hvw
  simp only [Set.mem_setOf_eq] at hv hw
  intro hadj
  have := hproper v w hadj
  rw [hv, hw] at this
  exact this rfl

/-- χ(G) ≥ ζ(G) always holds. -/
axiom chi_ge_zeta (G : SimpleGraph V) : chromaticNumber G ≥ cochromaticNumber G

/-!
## Part IV: The Erdős-Gimbel-Straight Conjecture
-/

/--
**Erdős-Gimbel-Straight Conjecture (1990):**
If G has no K₅ (ω(G) ≤ 4) and ζ(G) ≥ 4, then χ(G) ≤ ζ(G) + 2.

This was conjectured to be TRUE but has been DISPROVED.
-/
def egs_conjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    cliqueNumber G ≤ 4 →  -- no K₅
    cochromaticNumber G ≥ 4 →
    chromaticNumber G ≤ cochromaticNumber G + 2

/-!
## Part V: Steiner's Counterexample (2024)
-/

/--
**Steiner's Counterexample:**
There exists a graph G with:
- ω(G) = 4 (clique number 4, no K₅)
- ζ(G) = 4 (cochromatic number 4)
- χ(G) = 7 (chromatic number 7)

This gives χ(G) = 7 > 6 = 4 + 2 = ζ(G) + 2, disproving the conjecture.
-/
axiom steiner_counterexample :
  ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    cliqueNumber G = 4 ∧
    cochromaticNumber G = 4 ∧
    chromaticNumber G = 7

/--
**Resolution: The EGS Conjecture is FALSE.**
-/
theorem egs_conjecture_false : ¬egs_conjecture := by
  intro h
  obtain ⟨V, hfin, hdec, G, hω, hζ, hχ⟩ := steiner_counterexample
  -- Apply the conjecture to Steiner's graph
  have hbound := @h V hfin hdec G (by rw [hω]) (by rw [hζ])
  -- But χ(G) = 7 > 6 = ζ(G) + 2
  rw [hχ, hζ] at hbound
  omega

/-!
## Part VI: The General Theorem of Erdős-Gimbel-Straight
-/

/--
**EGS Theorem (1990):**
For every n > 2, there exists f(n) such that if ω(G) < n then χ(G) ≤ ζ(G) + f(n).

This general statement IS TRUE - only the specific bound "+2 for n=5" was disproved.
-/
axiom egs_general_theorem :
  ∀ n : ℕ, n > 2 → ∃ f : ℕ,
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      cliqueNumber G < n → chromaticNumber G ≤ cochromaticNumber G + f

/--
The gap χ(G) - ζ(G) can be bounded in terms of clique number.
-/
theorem chi_zeta_gap_bounded :
    ∀ n : ℕ, n > 2 → ∃ f : ℕ,
      ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        cliqueNumber G < n → chromaticNumber G - cochromaticNumber G ≤ f := by
  intro n hn
  obtain ⟨f, hf⟩ := egs_general_theorem n hn
  exact ⟨f, fun V _ _ G hω => by
    have := hf V G hω
    omega⟩

/-!
## Part VII: Known Bounds
-/

/--
**Trivial Upper Bound:**
ζ(G) ≤ χ(G) since proper colorings are cochromatic.
-/
axiom zeta_le_chi (G : SimpleGraph V) : cochromaticNumber G ≤ chromaticNumber G

/--
**Steiner's Result:**
The gap can be at least 3 for K₅-free graphs with ζ(G) = 4.
-/
axiom steiner_gap_lower_bound :
  ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    cliqueNumber G = 4 ∧
    chromaticNumber G - cochromaticNumber G ≥ 3

/-!
## Part VIII: Summary

**Problem Status: DISPROVED**

The Erdős-Gimbel-Straight conjecture that χ(G) ≤ ζ(G) + 2 for K₅-free graphs
with ζ(G) ≥ 4 has been DISPROVED by Steiner (2024).

**Counterexample:**
Steiner constructed a graph with ω = 4, ζ = 4, and χ = 7.

**What Remains True:**
The general theorem that χ(G) - ζ(G) is bounded by some function of ω(G)
still holds; only the specific bound "+2" was shown to be insufficient.

**Open Question:**
What is the optimal function f(n) such that χ(G) ≤ ζ(G) + f(n) whenever ω(G) < n?
-/

/-- Summary of known results about χ vs ζ. -/
theorem erdos_762_summary :
    -- The specific conjecture is false
    ¬egs_conjecture ∧
    -- But a general bound exists
    (∀ n > 2, ∃ f : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      cliqueNumber G < n → chromaticNumber G ≤ cochromaticNumber G + f) := by
  constructor
  · exact egs_conjecture_false
  · intro n hn
    exact egs_general_theorem n hn

end Erdos762
