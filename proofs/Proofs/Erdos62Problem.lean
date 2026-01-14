/-
  Erdős Problem #62: Common Subgraphs of Graphs with Chromatic Number ℵ₁

  Source: https://erdosproblems.com/62
  Status: OPEN

  Statement:
  If G₁, G₂ are two graphs with chromatic number ℵ₁, must there exist a graph G
  whose chromatic number is 4 (or even ℵ₀) which is a subgraph of both G₁ and G₂?

  History:
  - Erdős posed this question about infinite chromatic numbers
  - Generalization: Any finite collection of graphs with χ = ℵ₁ should share
    a common subgraph H with χ = 4 or χ = ℵ₀
  - Erdős-Hajnal-Shelah: Graphs with χ = ℵ₁ contain all large odd cycles

  Background:
  This problem sits at the intersection of infinite combinatorics and graph theory.
  Graphs with uncountable chromatic number have rich subgraph structure.

  This file formalizes the definitions and known partial results.
-/

import Mathlib

open Set

namespace Erdos62

/-! ## Infinite Graph Theory Setup -/

/-- An infinite simple graph on vertex set V. -/
structure InfGraph (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ u v, Adj u v → Adj v u
  loopless : ∀ v, ¬Adj v v

variable {V W : Type*}

/-- A graph coloring using colors from a type C. -/
def IsColoring (G : InfGraph V) (C : Type*) (f : V → C) : Prop :=
  ∀ u v, G.Adj u v → f u ≠ f v

/-- A graph is k-colorable if it admits a proper k-coloring. -/
def IsColorable (G : InfGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, IsColoring G (Fin k) f

/-- A graph is countably colorable. -/
def IsCountablyColorable (G : InfGraph V) : Prop :=
  ∃ f : V → ℕ, IsColoring G ℕ f

/-! ## Chromatic Number Classes -/

/-- A graph has chromatic number exactly k. -/
def HasChromaticNumber (G : InfGraph V) (k : ℕ) : Prop :=
  IsColorable G k ∧ ∀ j < k, ¬IsColorable G j

/-- A graph has chromatic number ℵ₀ (countably infinite). -/
def HasChromaticAleph0 (G : InfGraph V) : Prop :=
  IsCountablyColorable G ∧ ∀ k : ℕ, ¬IsColorable G k

/-- A graph has chromatic number ℵ₁ (uncountable). -/
def HasChromaticAleph1 (G : InfGraph V) : Prop :=
  ¬IsCountablyColorable G

/-! ## Subgraph Relation -/

/-- H embeds into G as a subgraph via an injective homomorphism. -/
def EmbedsInto (H : InfGraph V) (G : InfGraph W) : Prop :=
  ∃ f : V → W, Function.Injective f ∧ ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/-! ## Main Conjecture (OPEN) -/

/--
**Erdős Problem 62** (OPEN):

If G₁ and G₂ both have chromatic number ℵ₁, must there exist a graph H
with chromatic number 4 (or ℵ₀) that embeds into both G₁ and G₂?

Strong version: common subgraph with χ = 4.
-/
def erdos_62_conjecture_strong : Prop :=
  ∀ (V₁ V₂ : Type) (G₁ : InfGraph V₁) (G₂ : InfGraph V₂),
    HasChromaticAleph1 G₁ → HasChromaticAleph1 G₂ →
    ∃ (W : Type) (H : InfGraph W),
      HasChromaticNumber H 4 ∧ EmbedsInto H G₁ ∧ EmbedsInto H G₂

/-- Weaker version: The common subgraph has χ = ℵ₀ instead of χ = 4. -/
def erdos_62_conjecture_weak : Prop :=
  ∀ (V₁ V₂ : Type) (G₁ : InfGraph V₁) (G₂ : InfGraph V₂),
    HasChromaticAleph1 G₁ → HasChromaticAleph1 G₂ →
    ∃ (W : Type) (H : InfGraph W),
      HasChromaticAleph0 H ∧ EmbedsInto H G₁ ∧ EmbedsInto H G₂

/-! ## Generalization to Finite Collections -/

/--
**Generalized Conjecture** (Erdős 1987):
Any finite collection of graphs with chromatic number ℵ₁ should share
a common subgraph H with χ = 4 or χ = ℵ₀.
-/
def erdos_62_generalized (n : ℕ) : Prop :=
  ∀ (Vs : Fin n → Type) (Gs : ∀ i, InfGraph (Vs i)),
    (∀ i, HasChromaticAleph1 (Gs i)) →
    ∃ (W : Type) (H : InfGraph W),
      (HasChromaticNumber H 4 ∨ HasChromaticAleph0 H) ∧
      ∀ i, EmbedsInto H (Gs i)

/-! ## Related Results -/

/-- The odd cycle of length 2k+1 (axiomatized). -/
axiom oddCycle (k : ℕ) (hk : 1 ≤ k) : InfGraph (Fin (2*k + 1))

/-- Odd cycles have chromatic number 3. -/
axiom oddCycle_chromatic (k : ℕ) (hk : 1 ≤ k) :
    HasChromaticNumber (oddCycle k hk) 3

/--
**Erdős-Hajnal-Shelah Theorem**:
Every graph with chromatic number ℵ₁ contains all sufficiently large odd cycles.

More precisely, there exists N such that all odd cycles of length ≥ N embed.
-/
axiom erdos_hajnal_shelah (G : InfGraph V) (hχ : HasChromaticAleph1 G) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ (hk : 1 ≤ k), EmbedsInto (oddCycle k hk) G

/-- Graphs with χ = ℵ₁ share odd cycles as common subgraphs (χ = 3). -/
theorem odd_cycles_are_common (G₁ : InfGraph V) (G₂ : InfGraph W)
    (h₁ : HasChromaticAleph1 G₁) (h₂ : HasChromaticAleph1 G₂) :
    ∃ k : ℕ, ∃ (hk : 1 ≤ k),
      HasChromaticNumber (oddCycle k hk) 3 ∧
      EmbedsInto (oddCycle k hk) G₁ ∧
      EmbedsInto (oddCycle k hk) G₂ := by
  obtain ⟨N₁, hN₁⟩ := erdos_hajnal_shelah G₁ h₁
  obtain ⟨N₂, hN₂⟩ := erdos_hajnal_shelah G₂ h₂
  let k := max N₁ N₂ + 1
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by omega)
  use k, hk
  refine ⟨oddCycle_chromatic k hk, ?_, ?_⟩
  · exact hN₁ k (by omega) hk
  · exact hN₂ k (by omega) hk

/-! ## Gap Between χ = 3 and χ = 4 -/

/--
The key open question: Can we improve from χ = 3 to χ = 4?

We know odd cycles (χ = 3) are common subgraphs.
The conjecture asks for χ = 4 or even χ = ℵ₀.
-/
def chi_gap_problem : Prop :=
  ∀ (V₁ V₂ : Type) (G₁ : InfGraph V₁) (G₂ : InfGraph V₂),
    HasChromaticAleph1 G₁ → HasChromaticAleph1 G₂ →
    ∃ (W : Type) (H : InfGraph W),
      (∀ k ≤ 3, ¬HasChromaticNumber H k) ∧
      EmbedsInto H G₁ ∧ EmbedsInto H G₂

/-! ## Finite Chromatic Number Properties -/

/-- A graph has finite chromatic number. -/
def HasFiniteChromaticNumber (G : InfGraph V) : Prop :=
  ∃ k : ℕ, IsColorable G k

/-- Finite chromatic number implies countably colorable. -/
theorem finite_implies_countable (G : InfGraph V) :
    HasFiniteChromaticNumber G → IsCountablyColorable G := by
  intro ⟨k, f, hf⟩
  use fun v => (f v).val
  intro u v hadj
  have := hf u v hadj
  simp only [ne_eq, Fin.val_injective.eq_iff]
  exact this

/-! ## Monotonicity -/

/-- If H embeds into G and G is k-colorable, then H is k-colorable. -/
theorem embed_colorable (H : InfGraph V) (G : InfGraph W) (k : ℕ)
    (hemb : EmbedsInto H G) (hcol : IsColorable G k) : IsColorable H k := by
  obtain ⟨f, hf_inj, hf_edge⟩ := hemb
  obtain ⟨c, hc⟩ := hcol
  use c ∘ f
  intro u v hadj
  exact hc (f u) (f v) (hf_edge u v hadj)

/-! ## Summary

**Problem Status: OPEN**

The conjecture asks whether any two graphs with χ = ℵ₁ must share a common
subgraph with χ = 4 (or at least χ = ℵ₀).

**Known Results**:
1. Erdős-Hajnal-Shelah: All large odd cycles (χ = 3) are common subgraphs
2. The gap between χ = 3 and χ = 4 remains open
3. Generalizes to finite collections of graphs with χ = ℵ₁

**Open Questions**:
- Does there exist a common subgraph with χ = 4?
- Does there exist a common subgraph with χ = ℵ₀?
- What is the structure of graphs with χ = ℵ₁?

References:
- Erdős (1987, 1990, 1995): Original problem statements
- Erdős-Hajnal-Shelah (1974): Large odd cycles result
-/

end Erdos62
