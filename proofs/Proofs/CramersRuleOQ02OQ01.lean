import Mathlib
import Proofs.CramersRuleOQ02

/-
# Tightening the Gaussian-Elimination Complexity Model (OQ-02-OQ-01)

## Research Question

The parent entry `CramersRuleOQ02` compares Cramer's rule against Gaussian
elimination using the deliberately *loose* upper model `gaussMuls n = n³`.
Can the Gaussian-elimination cost be tightened to the **exact** leading
multiplication/division count, the classic `n³/3` figure?

## Answer: YES — the exact count is `(n³ − n)/3`.

Forward elimination of an `n × n` system proceeds in steps `k = 1, …, n−1`.
At step `k` the pivot sits in position `(k,k)` and there are `n − k` rows
below it. For each such row we:

- compute one multiplier (a **division**): `n − k` divisions at step `k`;
- update the `n − k` trailing entries of that row (one **multiplication**
  each): `(n − k)²` multiplications at step `k`.

So the per-step multiplication+division count is `(n−k) + (n−k)²`. Writing
`j = n − k` (which ranges over `1, …, n−1`), the total is

  `∑_{j=1}^{n−1} (j² + j) = (n−1)·n·(n+1)/3 = (n³ − n)/3`.

This is the exact arithmetic behind the textbook "`n³/3` flops" headline for
LU/Gaussian elimination, and it tightens the parent's `n³` model by a factor
of ~3 while preserving every comparison conclusion (a smaller cost only makes
Gaussian elimination look better against Cramer's rule).

## What is proved here (no axioms, no sorry)

- `gaussExactOps n` — the exact per-step model `∑_{j<n} (j² + j)`.
- `gaussExactOps_closed`     : `3 · gaussExactOps n + n = n³` (subtraction-free).
- `gaussExactOps_eq_div`     : `gaussExactOps n = (n³ − n)/3`.
- `gaussExactOps_le_cube`    : `gaussExactOps n ≤ n³` (it really is tighter).
- `gaussExactOps_lt_cube`    : strict for `n ≥ 2` (the factor-3 gap is real).
- `gaussExact_beats_cramer`  : the tighter model still beats Cramer's rule for
  `n ≥ 4`, a fortiori.

## Proof techniques

- `Finset.sum_range_succ` for the inductive step on `∑_{j<n} (j² + j)`.
- A subtraction-free `calc` so the closed form lives entirely in `ℕ`
  (`ring` over the commutative semiring `ℕ`, no `linear_combination`).
- `Nat.eq_div_of_eq_mul_left` to recover the `(n³ − n)/3` division form.
- Reuse of the parent's `factorial_gt_sq` growth lemma via the import.
-/

namespace CramersComplexityExact

open Finset

/-- Exact multiplication+division count for forward elimination of an `n × n`
    system: at the step that clears a column with `j` rows beneath the pivot we
    spend `j` divisions and `j²` multiplications, summed as `j` ranges over
    `0, …, n−1` (the `j = 0` term contributes nothing). -/
def gaussExactOps (n : ℕ) : ℕ := ∑ j ∈ range n, (j ^ 2 + j)

/-- Unfolding one elimination step. -/
lemma gaussExactOps_succ (n : ℕ) :
    gaussExactOps (n + 1) = gaussExactOps n + (n ^ 2 + n) := by
  unfold gaussExactOps
  rw [Finset.sum_range_succ]

/-- **Closed form (subtraction-free).** `3 · gaussExactOps n + n = n³`.

    Equivalently `gaussExactOps n = (n³ − n)/3`, but stated over `ℕ` without
    truncated subtraction so that `ring` closes the inductive step. -/
theorem gaussExactOps_closed (n : ℕ) : 3 * gaussExactOps n + n = n ^ 3 := by
  induction n with
  | zero => simp [gaussExactOps]
  | succ m ih =>
    calc 3 * gaussExactOps (m + 1) + (m + 1)
        = (3 * gaussExactOps m + m) + (3 * (m ^ 2 + m) + 1) := by
          rw [gaussExactOps_succ]; ring
      _ = m ^ 3 + (3 * (m ^ 2 + m) + 1) := by rw [ih]
      _ = (m + 1) ^ 3 := by ring

/-- The exact count in explicit division form: `gaussExactOps n = (n³ − n)/3`. -/
theorem gaussExactOps_eq_div (n : ℕ) : gaussExactOps n = (n ^ 3 - n) / 3 := by
  have h : 3 * gaussExactOps n = n ^ 3 - n := by
    have := gaussExactOps_closed n
    omega
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]

/-- The exact model never exceeds the parent's `n³` upper model:
    `gaussExactOps n ≤ n³`. -/
theorem gaussExactOps_le_cube (n : ℕ) : gaussExactOps n ≤ n ^ 3 := by
  have := gaussExactOps_closed n; omega

/-- The tightening is genuine: for `n ≥ 2` the exact count is *strictly* below
    the `n³` model (the missing `~2n³/3` is what the loose bound overcounts). -/
theorem gaussExactOps_lt_cube {n : ℕ} (hn : 2 ≤ n) : gaussExactOps n < n ^ 3 := by
  have hclosed := gaussExactOps_closed n
  -- 3 * ops + n = n^3, and n ≥ 2 forces ops < n^3 (since 2*ops = n^3 - n - ops ...).
  -- Concretely ops < n^3 ⇔ 0 < n^3 - ops = 2*ops + n, which holds as n ≥ 2 > 0.
  omega

/-- Concrete exact counts (sanity check against the hand computation):
    `n=2 ↦ 2`, `n=3 ↦ 8`, `n=4 ↦ 20`, `n=5 ↦ 40`. -/
lemma gaussExactOps_small :
    gaussExactOps 2 = 2 ∧ gaussExactOps 3 = 8 ∧
    gaussExactOps 4 = 20 ∧ gaussExactOps 5 = 40 := by
  have h2 := gaussExactOps_closed 2
  have h3 := gaussExactOps_closed 3
  have h4 := gaussExactOps_closed 4
  have h5 := gaussExactOps_closed 5
  norm_num at h2 h3 h4 h5
  omega

/-- With the *tighter* model, Gaussian elimination still beats Cramer's rule for
    `n ≥ 4` — a fortiori, since `gaussExactOps n ≤ n³ = gaussMuls n` and the
    parent already proved `gaussMuls n < cramersRuleMuls n`. -/
theorem gaussExact_beats_cramer {n : ℕ} (hn : 4 ≤ n) :
    gaussExactOps n < CramersComplexity.cramersRuleMuls n :=
  lt_of_le_of_lt (gaussExactOps_le_cube n) (CramersComplexity.gauss_beats_cramer hn)

/-- Summary: the exact `(n³ − n)/3` count, its consistency with and strict
    improvement over the `n³` model, and the preserved comparison verdict. -/
theorem gauss_exact_summary :
    (∀ n : ℕ, 3 * gaussExactOps n + n = n ^ 3) ∧
    (∀ n : ℕ, gaussExactOps n = (n ^ 3 - n) / 3) ∧
    (∀ n : ℕ, gaussExactOps n ≤ n ^ 3) ∧
    (∀ n : ℕ, 2 ≤ n → gaussExactOps n < n ^ 3) ∧
    (∀ n : ℕ, 4 ≤ n → gaussExactOps n < CramersComplexity.cramersRuleMuls n) :=
  ⟨gaussExactOps_closed, gaussExactOps_eq_div, gaussExactOps_le_cube,
   fun _ h => gaussExactOps_lt_cube h, fun _ h => gaussExact_beats_cramer h⟩

end CramersComplexityExact
