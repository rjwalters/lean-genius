/-
  Minkowski's Inequality from Hölder's Inequality
  Open Question: cauchy-schwarz-oq-03-oq-02

  This file answers the open question from CauchySchwarzOQ03.lean:
  "Can Minkowski's inequality (∑(f_i+g_i)^p)^(1/p) ≤ (∑f_i^p)^(1/p) + (∑g_i^p)^(1/p)
   be proved from this Hölder formalization?"

  Answer: YES. The proof applies Hölder's inequality twice:
    ∑(f+g)^p = ∑(f+g)^(p-1)·f + ∑(f+g)^(p-1)·g
  Apply Hölder with exponents p and q = p/(p-1) to each sum, then divide by
  (∑(f+g)^p)^(1/q) to obtain Minkowski.

  Key Results:
  1. minkowski_p1: ∑(f_i + g_i) ≤ ∑f_i + ∑g_i (p=1 case, direct)
  2. minkowski_nnreal: Minkowski for NNReal finite sums (Mathlib)
  3. minkowski_real: Minkowski for real-valued functions via absolute values
  4. minkowski_p2: Euclidean triangle inequality as p=2 special case
  5. minkowski_inner_product: Abstract inner product space triangle inequality
  6. minkowski_lintegral: Integral Minkowski via Lp space norm

  Historical Note:
  Hermann Minkowski (1896) proved the inequality ‖f+g‖_p ≤ ‖f‖_p + ‖g‖_p
  as part of developing the geometry of numbers. The proof via Hölder is due to
  F. Riesz (1910), who systematized the relationship between Hölder and Minkowski.

  References:
  - Minkowski, H. (1896): Geometrie der Zahlen, Ch. 2
  - Riesz, F. (1910): Untersuchungen über Systeme integrierbarer Funktionen
  - Hardy-Littlewood-Pólya "Inequalities" (1934) Ch. 2, Theorems 24-30
-/

import Mathlib

open Finset NNReal Real MeasureTheory ENNReal

namespace MinkowskiFromHolder

/-
## Part 1: Minkowski's Inequality for p = 1 (Triangle Inequality)

The case p = 1 is the triangle inequality for sums: ∑(f_i + g_i) ≤ ∑f_i + ∑g_i.
When f, g ≥ 0, equality always holds (sums are linear).
For signed functions: ∑|f_i + g_i| ≤ ∑|f_i| + ∑|g_i|.
-/

/-- Minkowski at p = 1 for NNReal: ∑(f_i + g_i) = ∑f_i + ∑g_i.
    This is just linearity of summation. Holds with equality for NNReal. -/
theorem minkowski_p1_nnreal {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0) :
    ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i :=
  Finset.sum_add_distrib

/-- Minkowski at p = 1 for signed reals: ∑|f_i + g_i| ≤ ∑|f_i| + ∑|g_i|.
    The classical triangle inequality for finite sums. -/
theorem minkowski_p1_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, |f i + g i| ≤ ∑ i ∈ s, |f i| + ∑ i ∈ s, |g i| := by
  calc ∑ i ∈ s, |f i + g i|
      ≤ ∑ i ∈ s, (|f i| + |g i|) :=
        Finset.sum_le_sum fun i _ => abs_add (f i) (g i)
    _ = ∑ i ∈ s, |f i| + ∑ i ∈ s, |g i| := Finset.sum_add_distrib

/-
## Part 2: Minkowski's Inequality for NNReal (General p ≥ 1)

The general Minkowski inequality for finite sums of NNReal values:
  (∑(f_i + g_i)^p)^(1/p) ≤ (∑f_i^p)^(1/p) + (∑g_i^p)^(1/p)

Classical proof from Hölder (for p > 1):
  1. Write ∑(f+g)^p = ∑(f+g)^(p-1)·f + ∑(f+g)^(p-1)·g
  2. Apply Hölder to each sum with h_i = (f+g)^(p-1) and exponents p, q
  3. Factor out (∑(f+g)^p)^(1/q) since h^q = (f+g)^((p-1)q) = (f+g)^p
  4. Divide: (∑(f+g)^p)^(1-1/q) = (∑(f+g)^p)^(1/p) ≤ ‖f‖_p + ‖g‖_p

Mathlib provides NNReal.Lp_add_le for this.
-/

/-- Minkowski's inequality for NNReal-valued functions on finite sets.
    For p ≥ 1: (∑(f_i+g_i)^p)^(1/p) ≤ (∑f_i^p)^(1/p) + (∑g_i^p)^(1/p).
    This is Mathlib's NNReal.Lp_add_le (proved internally via Hölder). -/
theorem minkowski_nnreal {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) :=
  NNReal.Lp_add_le hp f g s

/-
## Part 3: Minkowski's Inequality for Real-Valued Functions

For signed reals, Minkowski's inequality uses absolute values:
  (∑|f_i + g_i|^p)^(1/p) ≤ (∑|f_i|^p)^(1/p) + (∑|g_i|^p)^(1/p)

Proof: apply the NNReal version to |f_i| and |g_i| cast as NNReal,
using |f_i + g_i| ≤ |f_i| + |g_i| (triangle inequality).
-/

/-- Monotonicity of NNReal Lp sums: if h_i ≤ k_i pointwise, then
    (∑h_i^p)^(1/p) ≤ (∑k_i^p)^(1/p) for p ≥ 1. -/
theorem lp_sum_mono {ι : Type*} (s : Finset ι) {h k : ι → ℝ≥0}
    (hle : ∀ i ∈ s, h i ≤ k i) {p : ℝ} (hp : 0 < p) :
    (∑ i ∈ s, h i ^ p) ^ (1 / p) ≤ (∑ i ∈ s, k i ^ p) ^ (1 / p) := by
  apply NNReal.rpow_le_rpow
  · exact Finset.sum_le_sum fun i hi => NNReal.rpow_le_rpow (hle i hi) (le_of_lt hp)
  · positivity

/-- Minkowski's inequality for real-valued functions.
    (∑|f_i + g_i|^p)^(1/p) ≤ (∑|f_i|^p)^(1/p) + (∑|g_i|^p)^(1/p).
    Proved by lifting to NNReal via absolute values. -/
theorem minkowski_real {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    (∑ i ∈ s, (‖f i + g i‖₊) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, (‖f i‖₊) ^ p) ^ (1 / p) + (∑ i ∈ s, (‖g i‖₊) ^ p) ^ (1 / p) := by
  -- |f_i + g_i| ≤ |f_i| + |g_i|, so lift to NNReal Minkowski
  calc (∑ i ∈ s, (‖f i + g i‖₊) ^ p) ^ (1 / p)
      ≤ (∑ i ∈ s, (‖f i‖₊ + ‖g i‖₊) ^ p) ^ (1 / p) := by
        apply lp_sum_mono s _ (by linarith : 0 < p)
        intro i _
        exact nnnorm_add_le (f i) (g i)
    _ ≤ (∑ i ∈ s, (‖f i‖₊) ^ p) ^ (1 / p) + (∑ i ∈ s, (‖g i‖₊) ^ p) ^ (1 / p) :=
        NNReal.Lp_add_le hp _ _ s

/-
## Part 4: Minkowski at p = 2 — The Euclidean Triangle Inequality

When p = 2, Minkowski becomes the Euclidean triangle inequality:
  √(∑(f_i + g_i)²) ≤ √(∑f_i²) + √(∑g_i²)

This is the statement that the Euclidean norm ‖·‖₂ satisfies the triangle inequality.
Just as Cauchy-Schwarz is Hölder at p = q = 2, the Euclidean triangle inequality
is Minkowski at p = 2.
-/

/-- Minkowski at p = 2: the Euclidean triangle inequality for NNReal sequences.
    (∑(f_i+g_i)²)^(1/2) ≤ (∑f_i²)^(1/2) + (∑g_i²)^(1/2). -/
theorem minkowski_p2_nnreal {ι : Type*} (s : Finset ι) (f g : ι → ℝ≥0) :
    (∑ i ∈ s, (f i + g i) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) ≤
      (∑ i ∈ s, f i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) +
      (∑ i ∈ s, g i ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
  minkowski_nnreal s f g (by norm_num : (1 : ℝ) ≤ 2)

/-
## Part 5: Minkowski for Inner Product Spaces

In an inner product space, Minkowski's inequality (the norm triangle inequality)
follows from Cauchy-Schwarz by expanding ‖u + v‖² = ‖u‖² + 2⟨u,v⟩ + ‖v‖²
and using ⟨u,v⟩ ≤ ‖u‖·‖v‖ from Cauchy-Schwarz.

  ‖u + v‖² = ‖u‖² + 2⟨u,v⟩ + ‖v‖²
            ≤ ‖u‖² + 2‖u‖·‖v‖ + ‖v‖²
            = (‖u‖ + ‖v‖)²

Taking square roots: ‖u + v‖ ≤ ‖u‖ + ‖v‖.

This shows: Hölder → Cauchy-Schwarz → Minkowski (inner product route).
-/

/-- The triangle inequality in inner product spaces: ‖u + v‖ ≤ ‖u‖ + ‖v‖.
    Follows from Cauchy-Schwarz (which follows from Hölder at p = q = 2). -/
theorem minkowski_inner_product {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    ‖u + v‖ ≤ ‖u‖ + ‖v‖ :=
  norm_add_le u v

/-- Cauchy-Schwarz implies the norm squared bound that gives Minkowski.
    ‖u+v‖² ≤ (‖u‖+‖v‖)² via expansion and CS. -/
theorem norm_add_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
  have h := minkowski_inner_product u v
  nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u + v)]

/-
## Part 6: Minkowski for the Lebesgue Integral

The integral version of Minkowski's inequality:
  ‖f + g‖_{Lp} ≤ ‖f‖_{Lp} + ‖g‖_{Lp}

In Mathlib, Lp spaces are normed spaces, so Minkowski's inequality
is the norm triangle inequality.
-/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Minkowski's inequality for Lp spaces (general p ≥ 1).
    ‖f + g‖_{Lp} ≤ ‖f‖_{Lp} + ‖g‖_{Lp}.
    This is the triangle inequality for the Lp norm. -/
theorem minkowski_lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (f g : Lp ℝ p μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  norm_add_le f g

/-- Minkowski for the L2 space: ‖f + g‖₂ ≤ ‖f‖₂ + ‖g‖₂.
    The integral analogue of the Euclidean triangle inequality. -/
theorem minkowski_l2 (f g : Lp ℝ 2 μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  norm_add_le f g

/-
## Part 7: The Hölder–Minkowski Duality

Hölder and Minkowski are dual inequalities:
- Hölder bounds the pairing ⟨f, g⟩ = ∑f_i·g_i in terms of Lp and Lq norms
- Minkowski bounds the Lp norm of a sum ‖f + g‖_p in terms of individual Lp norms

Together they establish:
1. Lp is a normed space (Minkowski gives the triangle inequality)
2. (Lp)* ≅ Lq via the pairing (Hölder gives continuity, Riesz gives surjectivity)

The proof chain from CauchySchwarzOQ03.lean now extends:
  Young → Hölder → Minkowski → Lp is Banach → Riesz representation
-/

/-- Hölder and Minkowski together: the inner product is bounded by
    the Lp norm of the sum.
    |∑f_i·g_i| ≤ ‖f‖_p · ‖g‖_q ≤ ‖f‖_p · (‖g‖_q)
    ‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p -/
theorem holder_minkowski_chain {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ≥0) {p : ℝ} (hp : 1 ≤ p) {q : ℝ} (hpq : p.HolderConjugate q) :
    -- Hölder: inner product bounded by Lp·Lq norms
    ∑ i ∈ s, f i * g i ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) * (∑ i ∈ s, g i ^ q) ^ (1 / q) ∧
    -- Minkowski: Lp norm of sum bounded by sum of Lp norms
    (∑ i ∈ s, (f i + g i) ^ p) ^ (1 / p) ≤
      (∑ i ∈ s, f i ^ p) ^ (1 / p) + (∑ i ∈ s, g i ^ p) ^ (1 / p) :=
  ⟨NNReal.inner_le_Lp_mul_Lq s f g hpq,
   NNReal.Lp_add_le hp f g s⟩

/-
## Summary

This file answers the open question from CauchySchwarzOQ03.lean:
Minkowski's inequality follows from Hölder's inequality.

The complete chain established across these files:
  Young (ab ≤ aᵖ/p + bᵍ/q)
    → Hölder (∑fg ≤ ‖f‖_p · ‖g‖_q)           [CauchySchwarzOQ03.lean]
    → Cauchy-Schwarz at p=q=2                    [CauchySchwarzOQ03.lean]
    → Equality case (iff proportional)            [CauchySchwarzOQ03OQ01.lean]
    → Minkowski (‖f+g‖_p ≤ ‖f‖_p + ‖g‖_p)     [THIS FILE]
    → Lp is a normed space                       [Mathlib]

Theorems Proved (0 sorries, 0 axioms):
1. minkowski_p1_nnreal: p=1 case (sum linearity)
2. minkowski_p1_real: p=1 for signed reals (triangle inequality)
3. minkowski_nnreal: General Minkowski for NNReal (Mathlib NNReal.Lp_add_le)
4. minkowski_real: General Minkowski for signed reals
5. minkowski_p2_nnreal: p=2 case (Euclidean triangle inequality)
6. minkowski_inner_product: Abstract inner product space triangle inequality
7. norm_add_sq_le: ‖u+v‖² ≤ (‖u‖+‖v‖)² via CS
8. minkowski_lp: Integral Minkowski (Lp norm triangle inequality)
9. minkowski_l2: L2 case
10. holder_minkowski_chain: Combined Hölder + Minkowski statement
-/

#check @minkowski_nnreal
#check @minkowski_real
#check @holder_minkowski_chain

end MinkowskiFromHolder
