/-
  Erdős Problem #77: Ramsey Number Growth Rate

  Source: https://erdosproblems.com/77
  Status: OPEN
  Prize: $100 (limit exists), $10000 (limit doesn't exist)

  Statement:
  If R(k) is the Ramsey number for K_k (the minimal n such that every
  2-coloring of the edges of K_n contains a monochromatic K_k), find
  the value of lim_{k→∞} R(k)^{1/k}.

  **Known Bounds** (Erdős):
  √2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 4

  **Recent Improvements**:
  - Upper bound 4 - 1/128 (Campos, Griffiths, Morris, Sahasrabudhe 2023)
  - Upper bound 3.7992... (Gupta, Ndiaye, Norin, Wei 2024)

  **Open Questions**:
  1. Does the limit exist?
  2. If so, what is its value? (Erdős suspected it might be 2)

  **Prize History**:
  - $100 for proving limit exists (without value)
  - $1000 (later $10000) for proving limit doesn't exist
    (Erdős called this "a joke" - he believed it exists)

  References:
  - [ErGr80], [Er81], [Er97]
  - Campos, Griffiths, Morris, Sahasrabudhe (2023)
  - Gupta, Ndiaye, Norin, Wei (2024)
-/

import Mathlib

open Filter

namespace Erdos77

/-!
## Ramsey Numbers

R(k) is the minimum n such that every 2-coloring of K_n contains a
monochromatic K_k. We axiomatize its existence and basic properties.
-/

/-- The Ramsey number R(k).

    **Definition**: R(k) is the minimum n such that every 2-coloring
    of the edges of K_n contains a monochromatic copy of K_k.

    We axiomatize this function rather than constructing it from scratch,
    as the full definition requires significant graph theory infrastructure. -/
axiom RamseyNumber : ℕ → ℕ

/-- Ramsey numbers are well-defined and positive for k ≥ 2. -/
axiom ramseyNumber_pos : ∀ k ≥ 2, RamseyNumber k ≥ 1

/-!
## Small Ramsey Numbers (Known Values)
-/

/-- R(1) = 1 (trivial: any single vertex is a monochromatic K_1). -/
axiom ramsey_1 : RamseyNumber 1 = 1

/-- R(2) = 2 (trivial: any edge is monochromatic). -/
axiom ramsey_2 : RamseyNumber 2 = 2

/-- R(3) = 6 (classic result, often the first non-trivial Ramsey number computed).

    This can be proven: K_5 can be 2-colored without monochromatic K_3,
    but K_6 cannot. -/
axiom ramsey_3 : RamseyNumber 3 = 6

/-- R(4) = 18 (Greenwood-Gleason 1955).

    This required significant computation to establish. -/
axiom ramsey_4 : RamseyNumber 4 = 18

/-- R(5) is between 43 and 48 (bounds, exact value unknown as of 2024).

    Even with modern computers, determining R(5) exactly remains open. -/
axiom ramsey_5_bounds : 43 ≤ RamseyNumber 5 ∧ RamseyNumber 5 ≤ 48

/-!
## Classical Bounds

Erdős proved the following bounds using probabilistic and explicit methods.
-/

/-- **Erdős Lower Bound (1947)**: R(k) ≥ 2^{k/2} for k ≥ 3.

    This was one of the first applications of the **probabilistic method**.

    **Proof sketch**: A random 2-coloring of K_n has probability (1/2)^{C(k,2)}
    of having any specific k-clique be monochromatic. By union bound over
    all C(n,k) possible k-cliques, if n < 2^{k/2}, then with positive
    probability no monochromatic k-clique exists. -/
axiom erdos_lower_bound :
    ∀ k ≥ 3, (RamseyNumber k : ℝ) ≥ 2^((k : ℝ)/2)

/-- **Erdős-Szekeres Upper Bound**: R(k) ≤ 4^{k-1} for k ≥ 2.

    By the recurrence R(s,t) ≤ R(s-1,t) + R(s,t-1) with R(s,2) = R(2,t) = 2,
    we get R(k,k) ≤ C(2k-2, k-1) < 4^{k-1}. -/
axiom erdos_upper_bound :
    ∀ k ≥ 2, (RamseyNumber k : ℝ) ≤ 4^((k : ℝ) - 1)

/-- Corollary: R(k) ≤ 4^k (slightly weaker but cleaner). -/
theorem erdos_upper_bound' :
    ∀ k ≥ 2, (RamseyNumber k : ℝ) ≤ 4^(k : ℝ) := by
  intro k hk
  calc (RamseyNumber k : ℝ) ≤ 4^((k : ℝ) - 1) := erdos_upper_bound k hk
    _ ≤ 4^(k : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      linarith

/-!
## The Growth Rate Question

The main question is whether lim_{k→∞} R(k)^{1/k} exists, and if so, what is its value.
-/

/-- The sequence R(k)^{1/k}. -/
noncomputable def ramseyGrowthRate (k : ℕ) : ℝ :=
  (RamseyNumber k : ℝ)^(1/(k : ℝ))

/-- **Erdős's Bound on liminf**: liminf R(k)^{1/k} ≥ √2.

    From R(k) ≥ 2^{k/2}, we get R(k)^{1/k} ≥ (2^{k/2})^{1/k} = 2^{1/2} = √2. -/
axiom liminf_lower_bound :
    liminf (fun k => ramseyGrowthRate k) atTop ≥ Real.sqrt 2

/-- **Erdős's Bound on limsup**: limsup R(k)^{1/k} ≤ 4.

    From R(k) ≤ 4^k, we get R(k)^{1/k} ≤ (4^k)^{1/k} = 4. -/
axiom limsup_upper_bound :
    limsup (fun k => ramseyGrowthRate k) atTop ≤ 4

/-- Combined: √2 ≤ liminf ≤ limsup ≤ 4. -/
theorem erdos_bounds :
    Real.sqrt 2 ≤ liminf (fun k => ramseyGrowthRate k) atTop ∧
    limsup (fun k => ramseyGrowthRate k) atTop ≤ 4 :=
  ⟨liminf_lower_bound, limsup_upper_bound⟩

/-!
## Recent Breakthrough: Upper Bound Improvements (2023-2024)

After ~90 years with no improvement to the upper bound, major progress was made.
-/

/-- **Campos-Griffiths-Morris-Sahasrabudhe (2023)**:
    R(k) ≤ (4 - ε)^k for ε = 1/128.

    This was the first improvement to Erdős's upper bound since the 1930s!
    The paper "An exponential improvement for diagonal Ramsey" appeared in
    Annals of Mathematics. -/
axiom cgms_2023_bound :
    ∀ᶠ k in atTop, (RamseyNumber k : ℝ) ≤ (4 - 1/128)^(k : ℝ)

/-- Corollary: limsup R(k)^{1/k} ≤ 4 - 1/128 ≈ 3.992. -/
axiom cgms_2023_limsup :
    limsup (fun k => ramseyGrowthRate k) atTop ≤ 4 - 1/128

/-- **Gupta-Ndiaye-Norin-Wei (2024)**:
    R(k) ≤ (3.7993)^k.

    Further improvement using refined techniques. -/
axiom gnnw_2024_bound :
    ∀ᶠ k in atTop, (RamseyNumber k : ℝ) ≤ (3.7993 : ℝ)^(k : ℝ)

/-- Corollary: limsup R(k)^{1/k} ≤ 3.7993. -/
axiom gnnw_2024_limsup :
    limsup (fun k => ramseyGrowthRate k) atTop ≤ 3.7993

/-- Best known bounds as of 2024:
    √2 ≤ liminf R(k)^{1/k} ≤ limsup R(k)^{1/k} ≤ 3.7993.

    Note: √2 ≈ 1.414, so the gap is [1.414, 3.7993]. -/
theorem current_best_bounds :
    Real.sqrt 2 ≤ liminf (fun k => ramseyGrowthRate k) atTop ∧
    limsup (fun k => ramseyGrowthRate k) atTop ≤ 3.7993 :=
  ⟨liminf_lower_bound, gnnw_2024_limsup⟩

/-!
## The Open Questions
-/

/-- **Main Open Question**: Does the limit exist?

    Erdős offered $100 for proving the limit exists (even without finding its value).
    He offered $10000 for proving it doesn't exist, but called this "a joke"
    as he believed the limit certainly exists.

    Note: liminf ≤ limsup always. The limit exists iff liminf = limsup. -/
def LimitExists : Prop :=
  ∃ L : ℝ, Tendsto ramseyGrowthRate atTop (nhds L)

/-- **Erdős's Conjecture** (informal): The limit exists and equals 2.

    Erdős said "I suspect the limit is 2, but we have no real evidence for this."
    If true, this would mean R(k) ~ 2^k asymptotically. -/
def ErdosConjecture : Prop :=
  ∃ L : ℝ, Tendsto ramseyGrowthRate atTop (nhds L) ∧ L = 2

/-- Observation: If Erdős's conjecture is true (L = 2), the current bounds are off.
    We have √2 ≈ 1.414 as lower bound, but L = 2 is above this.
    However, 2 < 3.7993, so it's consistent with the upper bound. -/
theorem erdos_conjecture_consistent :
    Real.sqrt 2 < 2 ∧ (2 : ℝ) < 3.7993 := by
  constructor
  · have h1 : Real.sqrt 2 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h2 : Real.sqrt 4 = 2 := by norm_num
    linarith
  · norm_num

/-!
## Probabilistic Method Bounds

The probabilistic method gives the best known lower bounds.
-/

/-- **Refined Probabilistic Lower Bound**:
    R(k) ≥ (1 + o(1)) · k · 2^{k/2} / (e√2).

    This improves on Erdős's original 2^{k/2} by a factor of k/(e√2). -/
axiom probabilistic_lower_bound_refined :
    ∃ f : ℕ → ℝ, (∀ᶠ k in atTop, |f k| ≤ 1/k) ∧
    ∀ᶠ k in atTop, (RamseyNumber k : ℝ) ≥
      (1 + f k) * k * 2^((k : ℝ)/2) / (Real.exp 1 * Real.sqrt 2)

/-!
## Erdős's "Evil Spirit" Parable

Erdős illustrated the difficulty of computing Ramsey numbers with this story:

"Suppose aliens invade the Earth and threaten to obliterate it in a year's time
unless human beings can find R(5). We could marshal the world's best minds and
computers, and within a year we could probably calculate the value.

If they ask instead for R(6), we would have no choice but to launch a
preemptive attack against the aliens."

This captures how rapidly the computational difficulty grows.
-/

/-!
## Historical Significance

This problem showcases several important themes:

1. **The Probabilistic Method**: Erdős's lower bound was one of the first uses
   of this revolutionary technique.

2. **Long-standing Bounds**: The upper bound of 4 stood for ~90 years before
   Campos et al. improved it in 2023.

3. **Computational Intractability**: Even small Ramsey numbers (R(5), R(6))
   are beyond our computational reach.

4. **The Prize System**: Erdős's prizes ($100, $10000) show his conviction
   that the limit exists, while acknowledging the difficulty of proving it.
-/

/-!
## Summary

**Erdős Problem #77** asks for lim_{k→∞} R(k)^{1/k}.

**Status**: OPEN

**Known Bounds** (as of 2024):
- Lower: √2 ≈ 1.414 (Erdős 1947, probabilistic method)
- Upper: 3.7993 (Gupta-Ndiaye-Norin-Wei 2024)

**Open Questions**:
1. Does the limit exist? ($100 prize)
2. What is its value? (Erdős suspected 2, but "no real evidence")

**Small Known Values**:
- R(1) = 1, R(2) = 2, R(3) = 6, R(4) = 18
- 43 ≤ R(5) ≤ 48 (exact value unknown!)

**Historical Significance**:
- Probabilistic method birthplace
- 2023 breakthrough: first upper bound improvement in ~90 years
-/

end Erdos77
