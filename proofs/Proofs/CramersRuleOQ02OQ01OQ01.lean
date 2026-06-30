import Mathlib

/-
# Splitting the Gaussian-Elimination Multiply Count: divisions vs multiplications (OQ-02-OQ-01-OQ-01)

## Research Question

The parent entry `CramersRuleOQ02OQ01` proves the exact forward-elimination
multiplication+division count

  `gaussExactOps n = ∑_{j<n} (j² + j) = (n³ − n)/3`

as a *single lumped* quantity, and separately counts the subtractions
`∑_{j<n} j² ≈ n³/3`. But the lumped `j² + j` per step mixes two different
arithmetic operations: at the step that clears a column with `j` rows beneath
the pivot we perform

- `j` **divisions** (one multiplier per row below the pivot), and
- `j²` **multiplications** (scaling the `j` trailing entries of each of the
  `j` rows).

Which of the two carries the `n³/3` headline, and how subdominant is the other?

## Answer

Splitting `gaussExactOps n = gaussMults n + gaussDivs n` where

  `gaussMults n = ∑_{j<n} j²`  (multiplications)   and
  `gaussDivs  n = ∑_{j<n} j`   (divisions),

we prove:

- `gaussMults n` carries the entire cubic term: `6·gaussMults n + 3n² = 2n³ + n`,
  so `gaussMults n = (2n³ − 3n² + n)/6 ≈ n³/3`, and `6·gaussMults n ≤ 2n³`.
- `gaussDivs n` is purely **quadratic**: `2·gaussDivs n + n = n²`, i.e.
  `gaussDivs n = (n² − n)/2 = C(n,2)` — the triangular numbers, `Θ(n²)`.
- Hence the divisions are asymptotically negligible:
  `gaussDivs n ≤ gaussMults n` for all `n` (strict for `n ≥ 3`), and the whole
  `n³/3` of `gaussExactOps` comes from the multiplications.

This refines the "`n³/3` flops" headline: of the `(n³−n)/3` multiply/divide
operations, the `Θ(n²)` divisions vanish into the lower-order terms and the
cubic constant `1/3` is entirely a *multiplication* count.

## What is proved here (no axioms, no sorry, no native_decide)

- `gaussMults`, `gaussDivs` and the lumped `gaussOps = gaussMults + gaussDivs`.
- `gaussOps_split` : `∑_{j<n} (j²+j) = gaussMults n + gaussDivs n`.
- `gaussDivs_closed` : `2·gaussDivs n + n = n²` (triangular numbers).
- `gaussDivs_eq_choose` : `gaussDivs n = n.choose 2`.
- `gaussMults_closed` : `6·gaussMults n + 3n² = 2n³ + n`.
- `gaussMults_le_third` : `6·gaussMults n ≤ 2n³` (the multiplications alone are `≤ n³/3`).
- `gaussDivs_le_mults` : `gaussDivs n ≤ gaussMults n` (divisions subdominant);
  `gaussDivs_lt_mults` strict for `n ≥ 3`.
- `gaussOps_closed` : `3·gaussOps n + n = n³` (recovers the parent's `(n³−n)/3`).

## Proof techniques

- `Finset.sum_range_succ` for the inductive unfolding of each `∑`.
- Subtraction-free `calc`/`ring` over the `ℕ` semiring for the closed forms.
- `omega` to read off bounds from the linear closed-form identities (treating
  `n²`, `n³` and the sums as opaque non-negative atoms).
- `Finset.sum_le_sum` with the pointwise `j ≤ j²` for the dominance comparison.
- `Nat.choose_two_right` to identify the divisions with the binomial `C(n,2)`.
-/

namespace CramersComplexityOpSplit

open Finset

/-- Exact **multiplication** count of forward elimination: at the step clearing a
    column with `j` rows beneath the pivot, each of those `j` rows has `j` trailing
    entries scaled by the multiplier — `j²` multiplications per step, summed over
    `j < n`. -/
def gaussMults (n : ℕ) : ℕ := ∑ j ∈ range n, j ^ 2

/-- Exact **division** count of forward elimination: at the step clearing a column
    with `j` rows beneath the pivot we form one multiplier per row — `j` divisions
    per step, summed over `j < n`. -/
def gaussDivs (n : ℕ) : ℕ := ∑ j ∈ range n, j

/-- The lumped multiply/divide count of the parent entry, here exhibited as the
    sum of its two constituent operations. -/
def gaussOps (n : ℕ) : ℕ := ∑ j ∈ range n, (j ^ 2 + j)

/-- Unfolding one elimination step for the multiplication count. -/
lemma gaussMults_succ (n : ℕ) : gaussMults (n + 1) = gaussMults n + n ^ 2 := by
  unfold gaussMults; rw [Finset.sum_range_succ]

/-- Unfolding one elimination step for the division count. -/
lemma gaussDivs_succ (n : ℕ) : gaussDivs (n + 1) = gaussDivs n + n := by
  unfold gaussDivs; rw [Finset.sum_range_succ]

/-- **The split.** The lumped multiply/divide count is exactly multiplications plus
    divisions: `∑_{j<n} (j²+j) = gaussMults n + gaussDivs n`. -/
theorem gaussOps_split (n : ℕ) : gaussOps n = gaussMults n + gaussDivs n := by
  unfold gaussOps gaussMults gaussDivs
  rw [← Finset.sum_add_distrib]

/-- **Closed form for the divisions (subtraction-free).** `2·gaussDivs n + n = n²`,
    i.e. `gaussDivs n = (n² − n)/2` — the triangular numbers, a purely `Θ(n²)` count. -/
theorem gaussDivs_closed (n : ℕ) : 2 * gaussDivs n + n = n ^ 2 := by
  induction n with
  | zero => simp [gaussDivs]
  | succ m ih =>
    calc 2 * gaussDivs (m + 1) + (m + 1)
        = (2 * gaussDivs m + m) + (2 * m + 1) := by rw [gaussDivs_succ]; ring
      _ = m ^ 2 + (2 * m + 1) := by rw [ih]
      _ = (m + 1) ^ 2 := by ring

/-- The divisions are the binomial `C(n,2)`: `gaussDivs n = n.choose 2`. -/
theorem gaussDivs_eq_choose (n : ℕ) : gaussDivs n = n.choose 2 := by
  rw [Nat.choose_two_right]
  have h : 2 * gaussDivs n = n * (n - 1) := by
    have hc := gaussDivs_closed n
    cases n with
    | zero => simp [gaussDivs]
    | succ k =>
      have : (k + 1) ^ 2 = (k + 1) * ((k + 1) - 1) + (k + 1) := by
        simp [pow_two]; ring
      omega
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- **Closed form for the multiplications (subtraction-free).**
    `6·gaussMults n + 3n² = 2n³ + n`, i.e. `gaussMults n = (2n³ − 3n² + n)/6 ≈ n³/3`. -/
theorem gaussMults_closed (n : ℕ) : 6 * gaussMults n + 3 * n ^ 2 = 2 * n ^ 3 + n := by
  induction n with
  | zero => simp [gaussMults]
  | succ m ih =>
    calc 6 * gaussMults (m + 1) + 3 * (m + 1) ^ 2
        = (6 * gaussMults m + 3 * m ^ 2) + (6 * m ^ 2 + 6 * m + 3) := by
          rw [gaussMults_succ]; ring
      _ = (2 * m ^ 3 + m) + (6 * m ^ 2 + 6 * m + 3) := by rw [ih]
      _ = 2 * (m + 1) ^ 3 + (m + 1) := by ring

/-- **The multiplications alone are `≤ n³/3`.** `6·gaussMults n ≤ 2n³`, the cubic-term
    bound; together with `gaussMults_closed` it pins the leading constant of the
    multiplication count at exactly `1/3`. -/
theorem gaussMults_le_third (n : ℕ) : 6 * gaussMults n ≤ 2 * n ^ 3 := by
  induction n with
  | zero => simp [gaussMults]
  | succ m ih =>
    rw [gaussMults_succ]
    nlinarith [ih]

/-- **Divisions are subdominant.** `gaussDivs n ≤ gaussMults n` for every `n`,
    since `j ≤ j²` term by term. -/
theorem gaussDivs_le_mults (n : ℕ) : gaussDivs n ≤ gaussMults n := by
  unfold gaussDivs gaussMults
  apply Finset.sum_le_sum
  intro j _
  nlinarith [Nat.zero_le j]

/-- The dominance is **strict** for `n ≥ 3`: by then the `j = 2` term already gives
    `2 < 4`, so the multiplications strictly exceed the divisions. -/
theorem gaussDivs_lt_mults {n : ℕ} (hn : 3 ≤ n) : gaussDivs n < gaussMults n := by
  have hd := gaussDivs_closed n
  have hm := gaussMults_closed n
  nlinarith [hd, hm, hn]

/-- **Recovers the parent's lumped closed form.** `3·gaussOps n + n = n³`, hence
    `gaussOps n = (n³ − n)/3`, now seen as the sum of a cubic multiplication count
    and a quadratic division count. -/
theorem gaussOps_closed (n : ℕ) : 3 * gaussOps n + n = n ^ 3 := by
  rw [gaussOps_split]
  have hd := gaussDivs_closed n
  have hm := gaussMults_closed n
  nlinarith [hd, hm]

/-- Concrete split counts (sanity check against the hand computation):
    multiplications `n=2↦1, n=3↦5, n=4↦14, n=5↦30`;
    divisions       `n=2↦1, n=3↦3, n=4↦6,  n=5↦10` (triangular). -/
lemma split_small :
    gaussMults 2 = 1 ∧ gaussMults 3 = 5 ∧ gaussMults 4 = 14 ∧ gaussMults 5 = 30 ∧
    gaussDivs 2 = 1 ∧ gaussDivs 3 = 3 ∧ gaussDivs 4 = 6 ∧ gaussDivs 5 = 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [gaussMults, gaussDivs, Finset.sum_range_succ]

/-- Summary: the multiply/divide count splits into a cubic multiplication count and a
    quadratic (triangular) division count; the multiplications carry the entire
    `n³/3`, the divisions are `C(n,2) = Θ(n²)` and subdominant, and their sum recovers
    the parent's `(n³ − n)/3`. -/
theorem op_split_summary :
    (∀ n : ℕ, gaussOps n = gaussMults n + gaussDivs n) ∧
    (∀ n : ℕ, 2 * gaussDivs n + n = n ^ 2) ∧
    (∀ n : ℕ, gaussDivs n = n.choose 2) ∧
    (∀ n : ℕ, 6 * gaussMults n + 3 * n ^ 2 = 2 * n ^ 3 + n) ∧
    (∀ n : ℕ, 6 * gaussMults n ≤ 2 * n ^ 3) ∧
    (∀ n : ℕ, gaussDivs n ≤ gaussMults n) ∧
    (∀ n : ℕ, 3 * gaussOps n + n = n ^ 3) :=
  ⟨gaussOps_split, gaussDivs_closed, gaussDivs_eq_choose, gaussMults_closed,
   gaussMults_le_third, gaussDivs_le_mults, gaussOps_closed⟩

end CramersComplexityOpSplit
