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
"`A_{n+1}^{n+1} ≥ A_n^n · x_{n+1}` via Bernoulli" step.

We then promote it to the **rational-weighted** AM–GM

  `∏ xᵢ ^ kᵢ ≤ (mean) ^ (∑ kᵢ)`   (`amgm_weighted_nat`)

by the classical *repeat-with-multiplicity* reduction (replace each `xᵢ` by `kᵢ`
copies), so the weighted inequality the open question names is obtained from the
Bernoulli proof with no further analytic input.

**What this file proves.**
- `bernoulli_pow` — tangent-line Bernoulli (the kernel), re-exported from the
  parent's theme.
- `amgm_step` — the inductive heart: `x · Aₜⁿ ≤ A^{n+1}` whenever
  `(n+1)·A = x + n·Aₜ`. This is *pure* Bernoulli.
- `amgm_list` — unweighted AM–GM for a list of nonnegative reals.
- `amgm_prod_le` — the same with the product/sum written multiplicatively as a
  clean `∏ ≤ (∑/n)ⁿ` over `Finset` indices.
- `repList` and `repList_{prod,sum,length,nonneg}` — the repeat-with-multiplicity
  bookkeeping: building, for a list of `(value, weight)` pairs, the flat list
  containing each value with its multiplicity.
- `amgm_weighted_list` / `amgm_weighted_nat` — rational/natural-weighted AM–GM via
  the repetition reduction (list form and `Finset` form).
- Numeric witnesses.

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
theorem amgm_step {n : ℕ} {x At A : ℝ} (hx : 0 ≤ x) (hAt : 0 ≤ At) (hA : 0 ≤ A)
    (hrel : ((n : ℝ) + 1) * A = x + n * At) : x * At ^ n ≤ A ^ (n + 1) := by
  rcases eq_or_lt_of_le hAt with hAt0 | hAtpos
  · -- Degenerate case `Aₜ = 0`: the previous sample was all zeros.
    rcases n with _ | m
    · -- `n = 0`: then `A = x`, and both sides equal `x`.
      simp only [Nat.cast_zero, zero_add, one_mul, Nat.zero_eq, pow_zero, mul_one,
        pow_one] at *
      linarith [hrel]
    · -- `n = m+1 ≥ 1`: `Aₜⁿ = 0`, so the left side is `0 ≤ A^{n+1}`.
      have : At ^ (m + 1) = 0 := by rw [← hAt0]; simp
      rw [this, mul_zero]
      positivity
  · -- Main case `Aₜ > 0`: rescale by `r = A / Aₜ` and apply Bernoulli.
    set r : ℝ := A / At with hr_def
    have hAtne : At ≠ 0 := ne_of_gt hAtpos
    have hr0 : 0 ≤ r := div_nonneg hA hAt
    have hArAt : A = r * At := by field_simp [hr_def]
    -- The bookkeeping identity in terms of `r`: `x = ((n+1)·r − n)·Aₜ`.
    have hx_eq : x = (((n : ℝ) + 1) * r - n) * At := by
      have : ((n : ℝ) + 1) * (r * At) = x + n * At := by rw [← hArAt]; exact hrel
      nlinarith [this]
    -- Bernoulli: `(n+1)·r − n ≤ r^{n+1}`.
    have hb : ((n : ℝ) + 1) * r - n ≤ r ^ (n + 1) := by
      have h := bernoulli_pow (by linarith : (-1 : ℝ) ≤ r) (n + 1)
      have hcast : (1 : ℝ) + ((n : ℝ) + 1) * (r - 1) = ((n : ℝ) + 1) * r - n := by ring
      have : (1 : ℝ) + ((n + 1 : ℕ) : ℝ) * (r - 1) ≤ r ^ (n + 1) := h
      push_cast at this
      linarith [this]
    -- Assemble: both sides carry a common factor `Aₜ^{n+1} ≥ 0`.
    have hpow : (0 : ℝ) ≤ At ^ (n + 1) := by positivity
    calc x * At ^ n
        = (((n : ℝ) + 1) * r - n) * At ^ (n + 1) := by
          rw [hx_eq]; ring
      _ ≤ r ^ (n + 1) * At ^ (n + 1) := by exact mul_le_mul_of_nonneg_right hb hpow
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
    have hx : 0 ≤ x := hl x (List.mem_cons_self x t)
    have ht : ∀ y ∈ t, 0 ≤ y := fun y hy => hl y (List.mem_cons_of_mem x hy)
    have hts : 0 ≤ t.sum := List.sum_nonneg ht
    set n : ℕ := t.length with hn
    set At : ℝ := t.sum / n with hAt_def
    set A : ℝ := (x + t.sum) / ((n : ℝ) + 1) with hA_def
    have hAt : 0 ≤ At := div_nonneg hts (by positivity)
    have hA : 0 ≤ A := by
      apply div_nonneg (by linarith) (by positivity)
    -- Bookkeeping `(n+1)·A = x + n·Aₜ`.
    have hnAt : (n : ℝ) * At = t.sum := by
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · -- `n = 0` forces `t = []`, so `t.sum = 0`.
        have : t = [] := List.length_eq_zero_iff.mp hn0
        simp [this, hn0]
      · have : (n : ℝ) ≠ 0 := by positivity
        rw [hAt_def]; field_simp
    have hrel : ((n : ℝ) + 1) * A = x + n * At := by
      rw [hA_def]; field_simp; linarith [hnAt]
    -- Apply the inductive hypothesis, then the Bernoulli step.
    have ih' : t.prod ≤ At ^ n := ih ht
    have step : x * At ^ n ≤ A ^ (n + 1) := amgm_step hx hAt hA hrel
    calc (x :: t).prod
        = x * t.prod := by rw [List.prod_cons]
      _ ≤ x * At ^ n := by exact mul_le_mul_of_nonneg_left ih' hx
      _ ≤ A ^ (n + 1) := step
      _ = ((x :: t).sum / (x :: t).length) ^ (x :: t).length := by
          rw [List.sum_cons, List.length_cons, hA_def]; push_cast; ring_nf

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

/-! ## Rational/natural-weighted AM–GM via repetition

The classical promotion of unweighted AM–GM to natural-weighted AM–GM: replace
each value `xᵢ` by `kᵢ` copies and apply the unweighted inequality to the
resulting flat sample. No new analytic input — the only inequality used is still
`amgm_list`, hence still pure Bernoulli. -/

/-- The *repetition list* of a list of `(value, weight)` pairs: each pair
`(v, k)` contributes `k` copies of `v`. -/
def repList (p : List (ℝ × ℕ)) : List ℝ :=
  p.flatMap (fun q => List.replicate q.2 q.1)

@[simp] theorem repList_nil : repList [] = [] := rfl

@[simp] theorem repList_cons (q : ℝ × ℕ) (p : List (ℝ × ℕ)) :
    repList (q :: p) = List.replicate q.2 q.1 ++ repList p := by
  simp [repList, List.flatMap_cons]

/-- The product over the repetition list is `∏ vᵢ ^ kᵢ`. -/
theorem repList_prod (p : List (ℝ × ℕ)) :
    (repList p).prod = (p.map (fun q => q.1 ^ q.2)).prod := by
  induction p with
  | nil => simp
  | cons q p ih => simp [repList_cons, List.prod_append, List.prod_replicate, ih]

/-- The sum over the repetition list is `∑ kᵢ · vᵢ` (the weighted total). -/
theorem repList_sum (p : List (ℝ × ℕ)) :
    (repList p).sum = (p.map (fun q => (q.2 : ℝ) * q.1)).sum := by
  induction p with
  | nil => simp
  | cons q p ih =>
      simp [repList_cons, List.sum_append, List.sum_replicate, nsmul_eq_mul, ih]

/-- The length of the repetition list is the total weight `∑ kᵢ`. -/
theorem repList_length (p : List (ℝ × ℕ)) :
    (repList p).length = (p.map (fun q => q.2)).sum := by
  induction p with
  | nil => simp
  | cons q p ih => simp [repList_cons, List.length_append, List.length_replicate, ih]

/-- Nonnegativity transfers from the values to every entry of the repetition
list. -/
theorem repList_nonneg (p : List (ℝ × ℕ)) (hp : ∀ q ∈ p, 0 ≤ q.1) :
    ∀ x ∈ repList p, 0 ≤ x := by
  intro x hx
  rw [repList, List.mem_flatMap] at hx
  obtain ⟨q, hq, hxq⟩ := hx
  rw [List.eq_of_mem_replicate hxq]
  exact hp q hq

/-- **Natural-weighted AM–GM, list-of-pairs form.** For pairs `(vᵢ, kᵢ)` with
`vᵢ ≥ 0`, the weighted geometric mean is bounded by the weighted arithmetic mean:
`∏ vᵢ^{kᵢ} ≤ ((∑ kᵢ·vᵢ) / (∑ kᵢ))^{∑ kᵢ}`. Obtained from `amgm_list` applied to
the repetition list — pure Bernoulli, no logarithms. -/
theorem amgm_weighted_list (p : List (ℝ × ℕ)) (hp : ∀ q ∈ p, 0 ≤ q.1) :
    (p.map (fun q => q.1 ^ q.2)).prod ≤
      ((p.map (fun q => (q.2 : ℝ) * q.1)).sum / (p.map (fun q => q.2)).sum) ^
        (p.map (fun q => q.2)).sum := by
  have key := amgm_list (repList p) (repList_nonneg p hp)
  rwa [repList_prod, repList_sum, repList_length] at key

/-- **Natural-weighted AM–GM, `Finset` form.** For nonnegative reals `x i` with
natural-number weights `k i` over a `Finset s`,
`∏ x i ^ k i ≤ ((∑ k i · x i) / (∑ k i))^(∑ k i)`. This is the inequality the open
question names, derived from the Bernoulli route by the repetition reduction. -/
theorem amgm_weighted_nat {ι : Type*} (s : Finset ι) (x : ι → ℝ) (k : ι → ℕ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∏ i ∈ s, x i ^ k i ≤
      ((∑ i ∈ s, (k i : ℝ) * x i) / (∑ i ∈ s, k i)) ^ (∑ i ∈ s, k i) := by
  set p : List (ℝ × ℕ) := s.toList.map (fun i => (x i, k i)) with hp_def
  have hp : ∀ q ∈ p, 0 ≤ q.1 := by
    intro q hq
    rw [hp_def, List.mem_map] at hq
    obtain ⟨i, hi, rfl⟩ := hq
    exact hx i (Finset.mem_toList.mp hi)
  have key := amgm_weighted_list p hp
  have e1 : (p.map (fun q => q.1 ^ q.2)).prod = ∏ i ∈ s, x i ^ k i := by
    rw [hp_def, List.map_map]
    simp only [Function.comp_def]
    exact Finset.prod_map_toList s (fun i => x i ^ k i)
  have e2 : (p.map (fun q => (q.2 : ℝ) * q.1)).sum = ∑ i ∈ s, (k i : ℝ) * x i := by
    rw [hp_def, List.map_map]
    simp only [Function.comp_def]
    exact Finset.sum_map_toList s (fun i => (k i : ℝ) * x i)
  have e3 : (p.map (fun q => q.2)).sum = ∑ i ∈ s, k i := by
    rw [hp_def, List.map_map]
    simp only [Function.comp_def]
    exact Finset.sum_map_toList s (fun i => k i)
  rw [e1, e2, e3] at key
  exact key

/-! ## Numeric witnesses -/

/-- Two-variable AM–GM `√(ab) ≤ (a+b)/2`, here as `ab ≤ ((a+b)/2)²`, falls out of
`amgm_list [a, b]` — i.e. straight from Bernoulli with `n = 2`. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b ≤ ((a + b) / 2) ^ 2 := by
  have h := amgm_list [a, b] (by
    intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hx; rcases hx with rfl | rfl <;> assumption)
  simpa using h

/-- Three-variable AM–GM `abc ≤ ((a+b+c)/3)³`. -/
example (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ ((a + b + c) / 3) ^ 3 := by
  have h := amgm_list [a, b, c] (by
    intro x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> assumption)
  simp only [List.prod_cons, List.prod_nil, mul_one, List.sum_cons, List.sum_nil,
    add_zero, List.length_cons, List.length_nil] at h
  norm_num at h ⊢
  linarith [h]

/-- A concrete instance: `2·4·8 = 64 ≤ ((2+4+8)/3)³ = (14/3)³ ≈ 101.6`. -/
example : (2 : ℝ) * 4 * 8 ≤ ((2 + 4 + 8) / 3) ^ 3 := by norm_num

/-- **Weighted** witness: with weights `(2, 1)` on `(a, b)`, the weighted AM–GM
gives `a² · b ≤ ((2a + b)/3)³`. This is `amgm_weighted_list [(a,2), (b,1)]`. -/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 2 * b ^ 1 ≤ ((2 * a + b) / 3) ^ 3 := by
  have h := amgm_weighted_list [(a, 2), (b, 1)] (by
    intro q hq
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ha
    · exact hb)
  simpa using h

end BinomialTheoremOQ05OQ02
