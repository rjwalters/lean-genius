/-
# AM–GM from Bernoulli: the first-order-truncation route

**Open Question (binomial-theorem-oq-05-oq-02).** The parent entry
`binomial-theorem-oq-05` proved Bernoulli's inequality `1 + n·a ≤ (1 + a)ⁿ` as
the *first-order truncation* of the binomial expansion. The follow-up asks:
does that same viewpoint give a clean Lean proof of the AM–GM inequality, the
way Bernoulli "applied termwise" classically yields it?

**Answer: yes.** The unweighted AM–GM inequality

  `∏ xᵢ ≤ (mean xᵢ)ⁿ`            (`amgm_list`)

falls out of a single list induction whose *only* analytic input is the
gallery's Bernoulli inequality in tangent-line form `1 + n·(r − 1) ≤ rⁿ`
(`bernoulli_pow`, i.e. Mathlib's `one_add_mul_sub_le_pow`). There are **no
logarithms, no convexity of `exp`, no Jensen inequality** — in pointed contrast
to Mathlib's `Real.geom_mean_le_arith_mean_weighted`, whose proof routes through
`convexOn_exp.map_sum_le`. The whole argument is the elementary
"`A_{n+1}^{n+1} ≥ A_n^n · x_{n+1}` via Bernoulli" induction step.

**What this file proves.**
- `bernoulli_pow` — tangent-line Bernoulli (the kernel), from the parent's theme.
- `amgm_step` — the inductive heart: `x · Aₜⁿ ≤ A^{n+1}` whenever
  `(n+1)·A = x + n·Aₜ`. This is *pure* Bernoulli.
- `amgm_list` — unweighted AM–GM for a list of nonnegative reals.
- `amgm_prod_le` — the same as a clean `∏ ≤ (∑/n)ⁿ` over `Finset` indices.
- Numeric witnesses (two- and three-variable AM–GM as instant corollaries).

All results are fully verified: 0 sorries, 0 axioms.
-/
import Mathlib

namespace BinomialTheoremOQ05OQ02

open scoped BigOperators

/-! ## The kernel: tangent-line Bernoulli -/

/-- **Bernoulli, tangent-line form** (the gallery's `bernoulli_pow`). For
`r ≥ -1` and any `n : ℕ`, `1 + n·(r − 1) ≤ rⁿ`: the tangent line to `t ↦ tⁿ` at
`t = 1` lies below the curve. This single inequality is the *only* analytic
ingredient of the AM–GM proof below. -/
theorem bernoulli_pow {r : ℝ} (hr : -1 ≤ r) (n : ℕ) : 1 + n * (r - 1) ≤ r ^ n :=
  one_add_mul_sub_le_pow hr n

/-! ## The inductive heart -/

/-- **The Bernoulli step.** Splicing a new nonnegative term `x` into a sample
whose previous mean was `Aₜ ≥ 0`, giving the new mean `A`, satisfies
`x · Aₜⁿ ≤ A^{n+1}`, provided the means obey the bookkeeping identity
`(n+1)·A = x + n·Aₜ`.

This is exactly Bernoulli: dividing through by `Aₜ^{n+1}` (when `Aₜ > 0`) turns
the claim into `(n+1)·r − n ≤ r^{n+1}` with `r = A/Aₜ`, which is
`bernoulli_pow` rearranged. -/
theorem amgm_step {n : ℕ} {x At A : ℝ} (_hx : 0 ≤ x) (hAt : 0 ≤ At) (hA : 0 ≤ A)
    (hrel : ((n : ℝ) + 1) * A = x + n * At) : x * At ^ n ≤ A ^ (n + 1) := by
  rcases eq_or_lt_of_le hAt with hAt0 | hAtpos
  · -- Degenerate case `Aₜ = 0`: the previous sample was all zeros.
    rcases n with _ | m
    · -- `n = 0`: then `A = x`, and both sides equal `x`.
      simp only [Nat.cast_zero, zero_add, one_mul, zero_mul, add_zero, pow_zero,
        mul_one, pow_one] at hrel ⊢
      linarith
    · -- `n = m+1 ≥ 1`: `Aₜⁿ = 0`, so the left side is `0 ≤ A^{n+1}`.
      have h0 : At ^ (m + 1) = 0 := by rw [← hAt0]; simp
      rw [h0, mul_zero]
      exact pow_nonneg hA _
  · -- Main case `Aₜ > 0`: rescale by `r = A / Aₜ` and apply Bernoulli.
    have hAtne : At ≠ 0 := ne_of_gt hAtpos
    set r : ℝ := A / At with hr_def
    have hr0 : 0 ≤ r := div_nonneg hA hAt
    have hArAt : A = r * At := by rw [hr_def]; exact (div_mul_cancel₀ A hAtne).symm
    -- The bookkeeping identity in terms of `r`: `x = ((n+1)·r − n)·Aₜ`.
    have hx_eq : x = (((n : ℝ) + 1) * r - n) * At := by
      have h : ((n : ℝ) + 1) * (r * At) = x + n * At := by rw [← hArAt]; exact hrel
      nlinarith [h]
    -- Bernoulli: `(n+1)·r − n ≤ r^{n+1}`.
    have hb : ((n : ℝ) + 1) * r - n ≤ r ^ (n + 1) := by
      have h := bernoulli_pow (by linarith : (-1 : ℝ) ≤ r) (n + 1)
      push_cast at h
      linarith [h]
    -- Assemble: both sides carry the common factor `Aₜ^{n+1} ≥ 0`.
    have hpow : (0 : ℝ) ≤ At ^ (n + 1) := by positivity
    calc x * At ^ n
        = (((n : ℝ) + 1) * r - n) * At ^ (n + 1) := by rw [hx_eq]; ring
      _ ≤ r ^ (n + 1) * At ^ (n + 1) := mul_le_mul_of_nonneg_right hb hpow
      _ = A ^ (n + 1) := by rw [hArAt, mul_pow]

/-! ## Unweighted AM–GM -/

/-- **Unweighted AM–GM, list form.** For a list `l` of nonnegative reals,
`∏ l ≤ (mean l)^(length l)`, where `mean l = (∑ l) / (length l)`. Proved by a
single induction on `l`, the cons-step being `amgm_step` — i.e. pure Bernoulli.
The empty list gives `1 ≤ (0/0)^0 = 1`. -/
theorem amgm_list (l : List ℝ) (hl : ∀ x ∈ l, 0 ≤ x) :
    l.prod ≤ (l.sum / l.length) ^ l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    have hx : 0 ≤ x := hl x (by simp)
    have ht : ∀ y ∈ t, 0 ≤ y := fun y hy => hl y (by simp [hy])
    have hts : 0 ≤ t.sum := List.sum_nonneg ht
    have ih' : t.prod ≤ (t.sum / t.length) ^ t.length := ih ht
    have hAt : (0 : ℝ) ≤ t.sum / t.length := div_nonneg hts (by positivity)
    have hA : (0 : ℝ) ≤ (x + t.sum) / ((t.length : ℝ) + 1) :=
      div_nonneg (by linarith) (by positivity)
    -- `n·Aₜ = ∑ t`, handling the empty tail separately.
    have hnAt : (t.length : ℝ) * (t.sum / t.length) = t.sum := by
      rcases Nat.eq_zero_or_pos t.length with h0 | hpos
      · have ht0 : t = [] := List.length_eq_zero_iff.mp h0
        simp [ht0]
      · have hne : (t.length : ℝ) ≠ 0 := by positivity
        field_simp
    -- Bookkeeping identity feeding `amgm_step`.
    have hrel : ((t.length : ℝ) + 1) * ((x + t.sum) / ((t.length : ℝ) + 1))
        = x + t.length * (t.sum / t.length) := by
      rw [hnAt]
      have hne : ((t.length : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    have step : x * (t.sum / t.length) ^ t.length
        ≤ ((x + t.sum) / ((t.length : ℝ) + 1)) ^ (t.length + 1) :=
      amgm_step (n := t.length) hx hAt hA hrel
    calc (x :: t).prod
        = x * t.prod := List.prod_cons
      _ ≤ x * (t.sum / t.length) ^ t.length := mul_le_mul_of_nonneg_left ih' hx
      _ ≤ ((x + t.sum) / ((t.length : ℝ) + 1)) ^ (t.length + 1) := step
      _ = ((x :: t).sum / (x :: t).length) ^ (x :: t).length := by
          rw [List.sum_cons, List.length_cons]; push_cast; ring_nf

/-! ## Multiplicative `Finset` form -/

/-- **Unweighted AM–GM, `Finset` form.** For nonnegative reals `z i` indexed by
a `Finset s` of size `n`, `∏ z ≤ (∑ z / n)ⁿ`. This is `amgm_list` transported
along `s.toList`. -/
theorem amgm_prod_le {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    ∏ i ∈ s, z i ≤ ((∑ i ∈ s, z i) / s.card) ^ s.card := by
  have hmap : ∀ x ∈ s.toList.map z, 0 ≤ x := by
    intro x hx
    simp only [List.mem_map, Finset.mem_toList] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hz i hi
  have key := amgm_list (s.toList.map z) hmap
  rwa [Finset.prod_map_toList, Finset.sum_map_toList,
    List.length_map, Finset.length_toList] at key

/-! ## Numeric witnesses -/

/-- Two-variable AM–GM `√(ab) ≤ (a+b)/2`, here as `ab ≤ ((a+b)/2)²`, is just
`amgm_list [a, b]` — i.e. straight from Bernoulli with `n = 2`. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b ≤ ((a + b) / 2) ^ 2 := by
  have h := amgm_list [a, b] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  simpa using h

/-- Three-variable AM–GM `abc ≤ ((a+b+c)/3)³`. -/
example (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  have h := amgm_list [a, b, c] (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption)
  simp only [List.prod_cons, List.prod_nil, mul_one, List.sum_cons, List.sum_nil,
    add_zero, List.length_cons, List.length_nil] at h
  norm_num at h ⊢
  linarith [h]

/-- A concrete instance: `2·4·8 = 64 ≤ ((2+4+8)/3)³ = (14/3)³ ≈ 101.6`. -/
example : (2 : ℝ) * 4 * 8 ≤ ((2 + 4 + 8) / 3) ^ 3 := by norm_num

end BinomialTheoremOQ05OQ02
