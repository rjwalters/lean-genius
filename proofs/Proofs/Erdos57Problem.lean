/-
  Erdős Problem #57: Odd Cycles in Graphs with Infinite Chromatic Number

  Source: https://erdosproblems.com/57
  Status: SOLVED (Liu-Montgomery 2020)

  Statement:
  If G is a graph with infinite chromatic number and a₁ < a₂ < ⋯ are the
  lengths of the odd cycles of G, then ∑ 1/aᵢ = ∞.

  History:
  - Erdős-Hajnal (1966): Conjectured this result
  - Erdős (1981): Asked if odd cycle lengths have positive upper density
  - Erdős (1995-96): Speculated upper density might be ≥ 1/2
  - Liu-Montgomery (2020): SOLVED - proved the conjecture

  Key insight: Graphs with infinite chromatic number must have "many" odd
  cycles in the sense that their reciprocal lengths diverge.

  This file formalizes the definitions and main result.
-/

import Mathlib

open Set BigOperators

namespace Erdos57

variable {V : Type*}

/-! ## Core Definitions -/

/-- The set of all cycle lengths in a graph using Mathlib's Walk.IsCycle. -/
def cycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = n }

/-- The set of all odd cycle lengths in a graph. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n ∈ cycleLengths G | Odd n }

/-! ## Chromatic Number -/

/-- A graph is k-colorable if it admits a proper k-coloring. -/
def IsColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ u v, G.Adj u v → f u ≠ f v

/-- A graph has infinite chromatic number if it's not k-colorable for any finite k. -/
def HasInfiniteChromaticNumber (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ¬IsColorable G k

/-! ## The Harmonic Sum -/

/-- The sum ∑ 1/aᵢ where aᵢ are the odd cycle lengths. -/
noncomputable def oddCycleHarmonicSum (G : SimpleGraph V) : ENNReal :=
  ∑' n : (oddCycleLengths G), (1 : ENNReal) / n.val

/-! ## Main Results -/

/--
**Erdős-Hajnal Conjecture (1966) - SOLVED by Liu-Montgomery (2020)**:
If G has infinite chromatic number, then ∑ 1/aᵢ = ∞ where aᵢ are odd cycle lengths.
-/
axiom erdos_57 (G : SimpleGraph V) :
    HasInfiniteChromaticNumber G → oddCycleHarmonicSum G = ⊤

/--
A finite sum of reciprocals is finite (not ⊤).
-/
lemma finite_reciprocal_sum_ne_top (S : Set ℕ) (hS : S.Finite) (hpos : ∀ n ∈ S, 0 < n) :
    ∑' n : S, (1 : ENNReal) / n.val ≠ ⊤ := by
  -- Convert tsum over finite subtype to Finset.sum
  have h_sum : ∑' n : S, (1 : ENNReal) / n.val =
      ∑ n ∈ hS.toFinset, (1 : ENNReal) / n := by
    rw [tsum_subtype S (fun n => (1 : ENNReal) / n)]
    rw [tsum_eq_sum (s := hS.toFinset)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp only [Set.Finite.mem_toFinset] at hn ⊢
      simp [hn]
    · intro n hn
      simp only [Set.Finite.mem_toFinset] at hn
      simp [hn]
  rw [h_sum]
  -- Each term is finite, and finite sum of finite terms is finite
  have h_lt : ∑ n ∈ hS.toFinset, (1 : ENNReal) / n < ⊤ := by
    rw [ENNReal.sum_lt_top]
    intro n hn
    simp only [Set.Finite.mem_toFinset] at hn
    have hn_pos : 0 < n := hpos n hn
    apply ENNReal.div_lt_top (by norm_num)
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  exact h_lt.ne

/--
All odd cycle lengths are positive (≥ 3 actually, since minimum odd cycle is a triangle).
-/
lemma oddCycleLengths_pos (G : SimpleGraph V) : ∀ n ∈ oddCycleLengths G, 0 < n := by
  intro n hn
  simp only [oddCycleLengths, cycleLengths, Set.mem_setOf_eq] at hn
  obtain ⟨⟨u, p, hp, hlen⟩, hodd⟩ := hn
  rw [← hlen]
  -- A cycle has length ≥ 3, and odd cycles are at least 3
  have hge3 : 3 ≤ p.length := hp.three_le_length
  omega

/--
**Corollary**: A graph with infinite chromatic number has infinitely many
distinct odd cycle lengths.
-/
theorem infinite_odd_cycle_lengths (G : SimpleGraph V)
    (hG : HasInfiniteChromaticNumber G) : (oddCycleLengths G).Infinite := by
  by_contra h
  push_neg at h
  have h_sum := erdos_57 G hG
  -- If oddCycleLengths G is finite, the harmonic sum is finite (≠ ⊤)
  have h_ne_top := finite_reciprocal_sum_ne_top (oddCycleLengths G) h (oddCycleLengths_pos G)
  -- But h_sum says the harmonic sum = ⊤, contradiction
  exact h_ne_top h_sum

/-! ## Related Questions (OPEN) -/

/-- Upper density of a set of natural numbers. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (Set.ncard (S ∩ Set.Icc 1 N) : ℝ) / N) Filter.atTop

/--
**Open Question (Erdős 1981)**:
Must odd cycle lengths have positive upper density?
-/
def UpperDensityConjecture : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    HasInfiniteChromaticNumber G → 0 < upperDensity (oddCycleLengths G)

/--
**Stronger Conjecture (Erdős 1995-96)**:
Upper density of odd cycle lengths is at least 1/2.
-/
def HalfDensityConjecture : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    HasInfiniteChromaticNumber G → 1/2 ≤ upperDensity (oddCycleLengths G)

/-! ## Bipartite Characterization -/

/-- A graph is bipartite iff it has no odd cycles. -/
theorem bipartite_iff_no_odd_cycles (G : SimpleGraph V) :
    G.IsBipartite ↔ oddCycleLengths G = ∅ := by
  sorry

/-- 2-colorable graphs have no odd cycles. -/
theorem colorable_two_no_odd_cycles (G : SimpleGraph V)
    (h : IsColorable G 2) : oddCycleLengths G = ∅ := by
  sorry

/-! ## Historical Notes

The Liu-Montgomery proof uses sophisticated techniques from extremal
combinatorics. The connection between chromatic number and odd cycles
is fundamental: bipartite iff no odd cycles iff χ(G) ≤ 2.

References:
- Erdős-Hajnal (1966): Original conjecture
- Liu-Montgomery (2020): "A solution to Erdős and Hajnal's odd cycle problem"
-/

end Erdos57
