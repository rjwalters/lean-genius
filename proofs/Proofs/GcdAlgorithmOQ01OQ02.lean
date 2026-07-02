import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-
# Distribution of Euclidean Algorithm Step Counts — Concentration Infrastructure

## Open Question (parent `gcd-algorithm-oq-01-oq-02`)
"What is the *full distribution* of step counts of the Euclidean algorithm?
Hensley (1994) computed the variance; can the limiting distribution be formalized?"

## Background
For coprime inputs the number of division steps `euclideanSteps a b` behaves like a
random variable. Dixon (1970) proved the mean is `(12 ln 2 / π²) ln N ≈ 0.8427 ln N`;
Hensley (1994) proved a **central limit theorem**: suitably normalized, the step count
converges to a Gaussian. Proving that limit theorem in Lean is far out of reach — it
requires the spectral theory of the Gauss–Kuzmin–Wirsing transfer operator, which is
not in Mathlib.

## What This File Actually Proves (honest scope)
This file does **not** formalize Hensley's Gaussian limit. It builds the elementary,
fully verified probabilistic scaffolding that *any* distributional statement rests on:
the **finite Chebyshev inequality** for the empirical distribution of step counts over
a finite sample of input pairs. Concretely, over any finite sample `s` of pairs `(a,b)`,
the fraction of pairs whose step count deviates from the empirical mean by at least `t`
is at most `Var / t²`. This is the rigorous "concentration around the mean" content
underlying a limiting distribution — a genuine but elementary first layer.

## Status
- [x] Empirical mean / variance of a rational-valued statistic over a finite sample
- [x] Finite Chebyshev inequality (counting form and normalized fraction form)
- [x] Specialization to `euclideanSteps` over a canonical sample of input pairs
- [x] Non-negativity of the empirical variance
- [ ] Hensley's central limit theorem (requires transfer-operator spectral theory)

All results are `sorry`-free and use no `axiom`/`native_decide` (0 assumptions).
-/

namespace GcdAlgorithmOQ01OQ02

open Finset

/-!
## Step Counting

Same definition as the parent entry `GCDAlgorithmOQ01`, restated so this file is
self-contained.
-/

/-- Count division steps in the Euclidean algorithm. -/
def euclideanSteps (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else euclideanSteps b (a % b) + 1
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero ‹b ≠ 0›)

theorem euclideanSteps_zero (a : ℕ) : euclideanSteps a 0 = 0 := by
  rw [euclideanSteps]; simp

/-- The step count as a rational-valued statistic on input pairs. -/
def stepsQ (p : ℕ × ℕ) : ℚ := (euclideanSteps p.1 p.2 : ℚ)

theorem stepsQ_nonneg (p : ℕ × ℕ) : 0 ≤ stepsQ p := by
  unfold stepsQ; positivity

/-!
## Empirical Mean and Variance

We model the uniform distribution over a finite sample `s : Finset ι` and a
rational-valued statistic `f : ι → ℚ`. All quantities are exact rationals.
-/

/-- Empirical (sample) mean of `f` over the uniform distribution on `s`. -/
noncomputable def empMean {ι : Type*} (s : Finset ι) (f : ι → ℚ) : ℚ :=
  (∑ i ∈ s, f i) / s.card

/-- Empirical (sample) variance of `f` over the uniform distribution on `s`. -/
noncomputable def empVar {ι : Type*} (s : Finset ι) (f : ι → ℚ) : ℚ :=
  (∑ i ∈ s, (f i - empMean s f) ^ 2) / s.card

/-- The empirical variance is non-negative. -/
theorem empVar_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℚ) : 0 ≤ empVar s f := by
  unfold empVar
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · exact_mod_cast Nat.zero_le _

/-!
## Finite Chebyshev Inequality

The core estimate: on the set of points at deviation `≥ t` from a reference value `μ`,
each squared deviation is at least `t²`, so the count times `t²` is bounded by the total
sum of squared deviations. This is the finite / uniform-measure Chebyshev inequality.
-/

/-- **Chebyshev, counting form.** For any reference value `μ` and threshold `t > 0`,
the number of sample points deviating from `μ` by at least `t`, times `t²`, is bounded
by the total sum of squared deviations from `μ`. -/
theorem chebyshev_count {ι : Type*} (s : Finset ι) (f : ι → ℚ) (μ : ℚ)
    {t : ℚ} (ht : 0 < t) :
    ((s.filter (fun i => t ≤ |f i - μ|)).card : ℚ) * t ^ 2
      ≤ ∑ i ∈ s, (f i - μ) ^ 2 := by
  set T := s.filter (fun i => t ≤ |f i - μ|) with hT
  have hsub : T ⊆ s := Finset.filter_subset _ _
  -- `T.card * t² = ∑_{i ∈ T} t²`
  have h1 : (T.card : ℚ) * t ^ 2 = ∑ _i ∈ T, t ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  -- On `T` every squared deviation dominates `t²`.
  have h2 : ∑ _i ∈ T, t ^ 2 ≤ ∑ i ∈ T, (f i - μ) ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : t ≤ |f i - μ| := (Finset.mem_filter.mp hi).2
    have hprod : (0 : ℚ) ≤ (|f i - μ| - t) * (|f i - μ| + t) :=
      mul_nonneg (by linarith) (by linarith [abs_nonneg (f i - μ)])
    nlinarith [sq_abs (f i - μ), hprod]
  -- Extend the sum from `T` to all of `s` (extra terms are non-negative).
  have h3 : ∑ i ∈ T, (f i - μ) ^ 2 ≤ ∑ i ∈ s, (f i - μ) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg _)
  calc (T.card : ℚ) * t ^ 2 = ∑ _i ∈ T, t ^ 2 := h1
    _ ≤ ∑ i ∈ T, (f i - μ) ^ 2 := h2
    _ ≤ ∑ i ∈ s, (f i - μ) ^ 2 := h3

/-- **Chebyshev, normalized form.** For a non-empty sample, the *fraction* of points whose
statistic deviates from the empirical mean by at least `t` is bounded by `Var / t²`. This
is the classical `P(|X − μ| ≥ t) ≤ σ²/t²`. -/
theorem chebyshev_fraction {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℚ)
    {t : ℚ} (ht : 0 < t) :
    ((s.filter (fun i => t ≤ |f i - empMean s f|)).card : ℚ) / s.card
      ≤ empVar s f / t ^ 2 := by
  have hcard : (0 : ℚ) < (s.card : ℚ) := by exact_mod_cast Finset.card_pos.mpr hs
  have hcard' : (s.card : ℚ) ≠ 0 := ne_of_gt hcard
  have ht2 : (0 : ℚ) < t ^ 2 := by positivity
  have key := chebyshev_count s f (empMean s f) ht
  unfold empVar
  rw [div_le_div_iff₀ hcard ht2, div_mul_eq_mul_div, mul_div_assoc, div_self hcard', mul_one]
  exact key

/-!
## Specialization to Euclidean Step Counts

We take as canonical sample the pairs `(a, b)` with `1 ≤ b ≤ a ≤ N`. This is a
concrete finite universe on which `stepsQ` is an honest random variable; the concentration
bound holds for it (and, by `chebyshev_fraction`, for *any* other finite sample).
-/

/-- Canonical sample of input pairs `(a, b)` with `1 ≤ b ≤ a ≤ N`. -/
def sampleN (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter (fun p => 1 ≤ p.2 ∧ p.2 ≤ p.1)

/-- The canonical sample is non-empty for `N ≥ 1` (it contains `(1, 1)`). -/
theorem sampleN_nonempty {N : ℕ} (hN : 1 ≤ N) : (sampleN N).Nonempty := by
  refine ⟨(1, 1), ?_⟩
  simp only [sampleN, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- **Concentration of Euclidean step counts.** Over the canonical sample of input pairs
with `1 ≤ b ≤ a ≤ N`, the fraction of pairs whose step count deviates from the empirical
mean by at least `t` is at most `Var / t²`. This is the rigorous concentration statement
underlying (but far weaker than) Hensley's Gaussian limit law. -/
theorem euclideanSteps_concentration {N : ℕ} (hN : 1 ≤ N) {t : ℚ} (ht : 0 < t) :
    ((sampleN N).filter (fun p => t ≤ |stepsQ p - empMean (sampleN N) stepsQ|)).card
        / ((sampleN N).card : ℚ)
      ≤ empVar (sampleN N) stepsQ / t ^ 2 :=
  chebyshev_fraction (sampleN N) (sampleN_nonempty hN) stepsQ ht

end GcdAlgorithmOQ01OQ02
