/-
  PAC Learning OQ-04: The ε-net theorem for finite range spaces and
  tighter PAC sample complexity bounds.

  Advancing pac-learning-bounds-oq-04:
  "Epsilon-net theorem formalization for tighter PAC sample complexity bounds."

  The full ε-net theorem (Haussler–Welzl 1987) states that for a range space of
  VC dimension d, a random sample of size m = O((d/ε)·log(1/ε)) is an ε-net
  with high probability. Its measure-theoretic form is out of reach here, but
  the *analytic and combinatorial heart* of the theorem — the union-bound
  sample-complexity estimate for a **finite** range space — is fully
  formalizable and constitutes the sharpest elementary PAC bound.

  This file develops, with zero axioms:

    * Part I   — the ε-net concept over an abstract range space, with the
                 monotonicity `ε ≤ ε' → (ε-net → ε'-net)`.
    * Part II  — the analytic core:
                   `1 - x ≤ exp(-x)`,  `(1-x)^m ≤ exp(-x·m)`,
                 and the master sample-complexity inequality
                   `m ≥ (1/ε)·log(N/δ)  ⟹  N·(1-ε)^m ≤ δ`.
    * Part III — the finite union bound `∑_{r} miss(r) ≤ |R|·(1-ε)^m`,
                 giving the ε-net theorem for finite range spaces:
                 a sample of size `m ≥ (1/ε)·log(N/δ)` fails to be an ε-net
                 with union-bound value at most `δ`.
    * Part IV  — the ε-net ⟹ PAC-learning bridge: any hypothesis consistent
                 on an ε-net has true error `< ε`.

  Vapnik–Chervonenkis (1971); Haussler–Welzl (1987); Blumer–Ehrenfeucht–
  Haussler–Warmuth (1989).
-/
import Mathlib

namespace LearningTheory.EpsilonNet

open Finset

/-! ## Part I — Range spaces and ε-nets

A range space is a ground type `α` together with an indexed family of ranges
`ranges : ι → Set α` and a weight (measure) `μ : ι → ℝ` on the ranges. A finite
subset `S ⊆ α` (given as a `Set α`) is an **ε-net** if it meets every *heavy*
range, i.e. every range of weight at least `ε`. -/

variable {α : Type*} {ι : Type*}

/-- `S` is an ε-net for the range space `(ranges, μ)`: it intersects every range
    of weight `≥ ε`. -/
def IsEpsilonNet (ranges : ι → Set α) (μ : ι → ℝ) (ε : ℝ) (S : Set α) : Prop :=
  ∀ i, ε ≤ μ i → ∃ x ∈ S, x ∈ ranges i

/-- Monotonicity of ε-nets in the parameter: a finer net is also a coarser one.
    If `S` meets every range of weight `≥ ε` and `ε ≤ ε'`, then `S` meets every
    range of weight `≥ ε'` (there are fewer such ranges). -/
theorem isEpsilonNet_mono {ranges : ι → Set α} {μ : ι → ℝ} {ε ε' : ℝ}
    {S : Set α} (hεε' : ε ≤ ε') (h : IsEpsilonNet ranges μ ε S) :
    IsEpsilonNet ranges μ ε' S := by
  intro i hi
  exact h i (le_trans hεε' hi)

/-- If `S` is an ε-net and it *misses* a range `i` (no point of `S` lies in it),
    then that range is light: `μ i < ε`. This contrapositive is the exact form
    used in the PAC bridge of Part IV. -/
theorem light_of_missed {ranges : ι → Set α} {μ : ι → ℝ} {ε : ℝ}
    {S : Set α} (h : IsEpsilonNet ranges μ ε S)
    (i : ι) (hmiss : ∀ x ∈ S, x ∉ ranges i) : μ i < ε := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨x, hxS, hxr⟩ := h i hcon
  exact hmiss x hxS hxr

/-! ## Part II — The analytic core

The exponential estimates underlying every PAC/ε-net sample-complexity bound. -/

/-- The workhorse bound `1 - x ≤ exp(-x)`, valid for all real `x`. -/
theorem one_sub_le_exp_neg (x : ℝ) : 1 - x ≤ Real.exp (-x) := by
  have h := Real.add_one_le_exp (-x)
  linarith

/-- Raising to the `m`-th power: `(1 - x)^m ≤ exp(-x·m)` for `0 ≤ x ≤ 1`.
    This is the per-sample failure probability compounded over `m` independent
    draws. -/
theorem one_sub_pow_le_exp {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (m : ℕ) :
    (1 - x) ^ m ≤ Real.exp (-x * m) := by
  have hbase : (1 - x) ^ m ≤ (Real.exp (-x)) ^ m := by
    apply pow_le_pow_left₀ (by linarith) (one_sub_le_exp_neg x)
  calc (1 - x) ^ m ≤ (Real.exp (-x)) ^ m := hbase
    _ = Real.exp (-x * m) := by
        rw [← Real.exp_nat_mul]
        ring_nf

/-- **Master sample-complexity inequality.**  For a finite range/hypothesis
    class of size `N ≥ 1`, target accuracy `ε ∈ (0,1)`, and confidence `δ > 0`,
    a sample of size

        m ≥ (1/ε)·log(N/δ)

    drives the union-bound failure `N·(1-ε)^m` down to at most `δ`.

    This is the tightest *elementary* PAC bound: it is exactly the estimate that
    yields sample complexity `m = ⌈(1/ε)(ln N + ln(1/δ))⌉` for finite classes,
    and the same computation is the analytic heart of the ε-net theorem. -/
theorem sample_complexity_bound
    (ε δ : ℝ) (N m : ℕ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ)
    (hN : 1 ≤ N)
    (hm : (1 / ε) * Real.log ((N : ℝ) / δ) ≤ (m : ℝ)) :
    (N : ℝ) * (1 - ε) ^ m ≤ δ := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNδpos : (0 : ℝ) < (N : ℝ) / δ := div_pos hNpos hδ0
  -- Step 1: compound bound `(1-ε)^m ≤ exp(-ε·m)`.
  have hpow : (1 - ε) ^ m ≤ Real.exp (-ε * m) :=
    one_sub_pow_le_exp (le_of_lt hε0) (le_of_lt hε1) m
  -- Step 2: the sample-size hypothesis forces `log(N/δ) ≤ ε·m`.
  have hlog : Real.log ((N : ℝ) / δ) ≤ ε * m := by
    have := mul_le_mul_of_nonneg_left hm (le_of_lt hε0)
    rw [← mul_assoc] at this
    rwa [mul_one_div, div_self (ne_of_gt hε0), one_mul] at this
  -- Step 3: hence `exp(-ε·m) ≤ exp(-log(N/δ)) = δ/N`.
  have hexp : Real.exp (-ε * m) ≤ δ / N := by
    have hmono : Real.exp (-ε * m) ≤ Real.exp (-Real.log ((N : ℝ) / δ)) := by
      apply Real.exp_le_exp.mpr
      have : (-ε) * m = -(ε * m) := by ring
      rw [this]
      exact neg_le_neg hlog
    calc Real.exp (-ε * m)
        ≤ Real.exp (-Real.log ((N : ℝ) / δ)) := hmono
      _ = ((N : ℝ) / δ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hNδpos]
      _ = δ / N := by rw [inv_div]
  -- Step 4: assemble.
  calc (N : ℝ) * (1 - ε) ^ m
      ≤ (N : ℝ) * Real.exp (-ε * m) := by
        apply mul_le_mul_of_nonneg_left hpow (le_of_lt hNpos)
    _ ≤ (N : ℝ) * (δ / N) := by
        apply mul_le_mul_of_nonneg_left hexp (le_of_lt hNpos)
    _ = δ := by field_simp

/-! ## Part III — Finite union bound and the ε-net theorem

For a finite collection of heavy ranges, the probability that a random sample
misses *some* heavy range is bounded, via the union bound, by the sum of the
individual miss probabilities. When each range is missed with probability at
most `(1-ε)^m`, the total is at most `|R|·(1-ε)^m`. -/

/-- The union bound as a pure `Finset` inequality: if each term is at most `q`,
    the sum over a finite index set is at most `|R|·q`. -/
theorem union_bound (R : Finset ι) (q : ℝ) (miss : ι → ℝ)
    (hmiss : ∀ i ∈ R, miss i ≤ q) :
    ∑ i ∈ R, miss i ≤ R.card * q := by
  calc ∑ i ∈ R, miss i ≤ ∑ _i ∈ R, q := Finset.sum_le_sum hmiss
    _ = R.card * q := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **ε-net theorem for finite range spaces (union-bound form).**

    Let `R` be the finite set of heavy ranges (`|R| ≤ N`). Suppose each heavy
    range is missed by an `m`-sample with probability at most `(1-ε)^m` and the
    sample size satisfies `m ≥ (1/ε)·log(N/δ)`. Then the union-bound estimate
    on the probability that the sample fails to be an ε-net is at most `δ`.

    In words: `m ≥ (1/ε)·log(N/δ)` samples suffice for an ε-net with
    failure probability `≤ δ`. -/
theorem epsilon_net_failure_bound
    (ε δ : ℝ) (N m : ℕ) (R : Finset ι) (miss : ι → ℝ)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hN : 1 ≤ N)
    (hcard : R.card ≤ N)
    (hmiss : ∀ i ∈ R, miss i ≤ (1 - ε) ^ m)
    (hm : (1 / ε) * Real.log ((N : ℝ) / δ) ≤ (m : ℝ)) :
    ∑ i ∈ R, miss i ≤ δ := by
  have hpow_nonneg : (0 : ℝ) ≤ (1 - ε) ^ m := pow_nonneg (by linarith) m
  -- Union bound over the heavy ranges.
  have hub : ∑ i ∈ R, miss i ≤ (R.card : ℝ) * (1 - ε) ^ m :=
    union_bound R _ miss hmiss
  -- Enlarge `|R|` to `N`, then apply the master inequality.
  have hcardN : (R.card : ℝ) * (1 - ε) ^ m ≤ (N : ℝ) * (1 - ε) ^ m := by
    apply mul_le_mul_of_nonneg_right _ hpow_nonneg
    exact_mod_cast hcard
  have hmaster : (N : ℝ) * (1 - ε) ^ m ≤ δ :=
    sample_complexity_bound ε δ N m hε0 hε1 hδ0 hN hm
  linarith

/-! ## Part IV — The ε-net ⟹ PAC-learning bridge

The reason ε-nets matter for learning: fix a target concept `c` and a hypothesis
`h`. The *error region* of `h` is the set of points on which `h` disagrees with
`c`. If the sample `S` is an ε-net for the range space whose ranges are the error
regions, then any hypothesis that is **consistent** on `S` (agrees with `c`
everywhere on `S`) has true error below `ε`. -/

/-- Consistency of `h` on the sample: `h` agrees with the target `c` on every
    sample point, i.e. `S` avoids the error region of `h`. -/
def Consistent (errRegion : Set α) (S : Set α) : Prop :=
  ∀ x ∈ S, x ∉ errRegion

/-- **ε-net ⟹ generalization.**  If `S` is an ε-net for the family of error
    regions (weighted by generalization error `err`) and hypothesis `j` is
    consistent on `S`, then its true error is `< ε`.

    This is the qualitative guarantee behind PAC learning: consistency on a large
    enough sample forces small true error. Combined with Part III, `O((1/ε)·
    log(N/δ))` samples give an ε-net, hence PAC-learn the class. -/
theorem generalization_of_consistent
    {errRegion : ι → Set α} {err : ι → ℝ} {ε : ℝ} {S : Set α}
    (hnet : IsEpsilonNet errRegion err ε S)
    (j : ι) (hcons : Consistent (errRegion j) S) :
    err j < ε :=
  light_of_missed hnet j hcons

end LearningTheory.EpsilonNet
