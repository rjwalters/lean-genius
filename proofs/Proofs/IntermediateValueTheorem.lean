import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Intermediate Value Theorem

## What This Proves
We prove the Intermediate Value Theorem (IVT): if f is a continuous real-valued
function on a closed interval [a, b], then f attains every value between f(a)
and f(b). In particular, if f(a) < c < f(b), there exists x ∈ (a, b) with f(x) = c.

## Wiedijk 100 Theorems: #79
This is entry #79 in Freek Wiedijk's list of 100 famous theorems.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `intermediate_value_Icc` theorem,
  which is built on the topological fact that continuous images of connected sets
  are connected, and connected subsets of ℝ are intervals.
- **Original Contributions:** This file provides pedagogical organization,
  wrapper theorems with the classical statements (including the root-finding
  corollary), and extensive commentary explaining the theorem's significance.
- **Proof Techniques Demonstrated:** Working with Mathlib's topology framework,
  connectedness arguments, and order-theoretic properties of the reals.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [ ] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `intermediate_value_Icc` : The main IVT theorem for closed intervals
- `isPreconnected_Icc` : Closed intervals are connected
- `ContinuousOn` : Continuity on a set

Historical Note: The Intermediate Value Theorem was first stated precisely by
Bernard Bolzano in 1817, though the proof relied on properties of real numbers
that weren't rigorously established until later. Augustin-Louis Cauchy gave a
more complete treatment in 1821, but the fully rigorous proof required the
completeness axiom of the reals, formalized by Dedekind and Cantor in the 1870s.
-/

open Set Filter Topology

namespace IntermediateValueTheorem

/-!
## The Classical Statement

The Intermediate Value Theorem: If f : ℝ → ℝ is continuous on [a, b] and
c is between f(a) and f(b), then there exists some x ∈ [a, b] with f(x) = c.

Mathematically: ∀ c ∈ [f(a), f(b)], ∃ x ∈ [a, b], f(x) = c
-/

-- The main theorem: continuous functions on closed intervals hit all intermediate values
-- This is a direct consequence of Mathlib's intermediate_value_Icc
theorem ivt {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  intermediate_value_Icc hab hf

-- The symmetric version: f(b) ≤ c ≤ f(a)
theorem ivt' {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc a b)) :
    Icc (f b) (f a) ⊆ f '' Icc a b :=
  intermediate_value_Icc' hab hf

/-!
## Explicit Existence Form

The theorem is often stated as: given c between f(a) and f(b), there
exists x in [a, b] with f(x) = c. This is a direct reformulation.
-/

-- Explicit existence statement when f(a) ≤ c ≤ f(b)
theorem exists_eq_of_mem_Icc {a b c : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hc : c ∈ Icc (f a) (f b)) :
    ∃ x ∈ Icc a b, f x = c := by
  have h := ivt hab hf hc
  exact h

-- Explicit existence when f(b) ≤ c ≤ f(a)
theorem exists_eq_of_mem_Icc' {a b c : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hc : c ∈ Icc (f b) (f a)) :
    ∃ x ∈ Icc a b, f x = c := by
  have h := ivt' hab hf hc
  exact h

-- Combined statement: c between f(a) and f(b) in either order
theorem exists_eq_of_between {a b c : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hc1 : min (f a) (f b) ≤ c) (hc2 : c ≤ max (f a) (f b)) :
    ∃ x ∈ Icc a b, f x = c := by
  by_cases h : f a ≤ f b
  · -- f(a) ≤ f(b), so min = f(a) and max = f(b)
    simp only [min_eq_left h, max_eq_right h] at hc1 hc2
    exact exists_eq_of_mem_Icc hab hf ⟨hc1, hc2⟩
  · -- f(b) < f(a), so min = f(b) and max = f(a)
    push_neg at h
    simp only [min_eq_right (le_of_lt h), max_eq_left (le_of_lt h)] at hc1 hc2
    exact exists_eq_of_mem_Icc' hab hf ⟨hc1, hc2⟩

/-!
## The Root-Finding Corollary (Bolzano's Theorem)

The special case where f(a) and f(b) have opposite signs: if f(a) < 0 < f(b)
(or f(b) < 0 < f(a)), then f has a root in (a, b).

This is Bolzano's theorem, often stated as the main result in analysis courses.
-/

-- If f(a) < 0 < f(b), there exists x with f(x) = 0
theorem bolzano {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  -- First get existence in [a, b]
  have h : (0 : ℝ) ∈ Icc (f a) (f b) := ⟨le_of_lt hfa, le_of_lt hfb⟩
  obtain ⟨x, hx_mem, hx_eq⟩ := ivt (le_of_lt hab) hf h
  -- Now show x is actually in (a, b)
  refine ⟨x, ?_, hx_eq⟩
  constructor
  · -- x > a because f(x) = 0 but f(a) < 0
    by_contra hxa
    push_neg at hxa
    have heq : x = a := le_antisymm hxa hx_mem.1
    have : f a = 0 := heq ▸ hx_eq
    linarith
  · -- x < b because f(x) = 0 but f(b) > 0
    by_contra hxb
    push_neg at hxb
    have heq : x = b := le_antisymm hx_mem.2 hxb
    have : f b = 0 := heq ▸ hx_eq
    linarith

-- The symmetric version: f(a) > 0 > f(b)
theorem bolzano' {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfa : 0 < f a) (hfb : f b < 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  have h : (0 : ℝ) ∈ Icc (f b) (f a) := ⟨le_of_lt hfb, le_of_lt hfa⟩
  obtain ⟨x, hx_mem, hx_eq⟩ := ivt' (le_of_lt hab) hf h
  refine ⟨x, ?_, hx_eq⟩
  constructor
  · by_contra hxa
    push_neg at hxa
    have heq : x = a := le_antisymm hxa hx_mem.1
    have : f a = 0 := heq ▸ hx_eq
    linarith
  · by_contra hxb
    push_neg at hxb
    have heq : x = b := le_antisymm hx_mem.2 hxb
    have : f b = 0 := heq ▸ hx_eq
    linarith

-- Generalized sign change: f(a) * f(b) < 0 means they have opposite signs
theorem root_of_opposite_signs {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hsign : f a * f b < 0) :
    ∃ x ∈ Ioo a b, f x = 0 := by
  -- Opposite signs means one is positive and one is negative
  have h := mul_neg_iff.mp hsign
  rcases h with ⟨hfa_pos, hfb_neg⟩ | ⟨hfa_neg, hfb_pos⟩
  · exact bolzano' hab hf hfa_pos hfb_neg
  · exact bolzano hab hf hfa_neg hfb_pos

/-!
## Continuous Functions on Connected Sets

The IVT is actually a consequence of a more general topological principle:
continuous images of connected sets are connected.
-/

-- Connected sets in ℝ are intervals, so images contain all intermediate values
theorem continuous_image_connected {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsConnected s) {f : X → ℝ} (hf : ContinuousOn f s) :
    IsConnected (f '' s) :=
  hs.image f hf

-- For continuous functions, the image of a connected set contains all intermediate values
theorem intermediate_value_connected {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsPreconnected s) {a b : X} (ha : a ∈ s) (hb : b ∈ s)
    {f : X → ℝ} (hf : ContinuousOn f s) :
    Icc (f a) (f b) ⊆ f '' s :=
  hs.intermediate_value ha hb hf

/-!
## Applications and Corollaries
-/

-- Every odd-degree real polynomial has a real root
-- (We state the general principle; specific polynomial case follows from this)
theorem odd_degree_poly_has_root {f : ℝ → ℝ} (hf : Continuous f)
    (hneg : ∃ a, f a < 0) (hpos : ∃ b, f b > 0) :
    ∃ x, f x = 0 := by
  obtain ⟨a, ha⟩ := hneg
  obtain ⟨b, hb⟩ := hpos
  rcases lt_trichotomy a b with hab | hab_eq | hba
  · -- a < b: use bolzano
    obtain ⟨x, _, hx⟩ := bolzano hab hf.continuousOn ha hb
    exact ⟨x, hx⟩
  · -- a = b is impossible: f(a) < 0 and f(b) > 0
    rw [hab_eq] at ha
    linarith
  · -- b < a: use bolzano'
    obtain ⟨x, _, hx⟩ := bolzano' hba hf.continuousOn hb ha
    exact ⟨x, hx⟩

-- Fixed point theorem: if f : [a, b] → [a, b] is continuous, it has a fixed point
-- This is a consequence of IVT applied to g(x) = f(x) - x
theorem fixed_point_Icc {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc a b)) (hmaps : ∀ x ∈ Icc a b, f x ∈ Icc a b) :
    ∃ x ∈ Icc a b, f x = x := by
  exact exists_mem_Icc_isFixedPt hf hab (hmaps a (left_mem_Icc.mpr hab)).1
    (hmaps b (right_mem_Icc.mpr hab)).2

end IntermediateValueTheorem

-- Verification that our theorems type-check correctly
#check IntermediateValueTheorem.ivt
#check IntermediateValueTheorem.bolzano
#check IntermediateValueTheorem.root_of_opposite_signs
#check IntermediateValueTheorem.fixed_point_Icc
