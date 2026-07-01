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

Two further sections extend this to the FULL flop count and the COMPLETE solve:

- `gaussExactSubs`/`gaussExactFlops` — the `≈ n³/3` subtractions and the resulting
  `≈ 2n³/3` total leading flop count of the factorization.
- `solveMulsDivs` — the multiplication+division count of a complete linear solve
  `A x = b` (factorization + right-hand-side elimination + back-substitution), with
  `solve_overhead_quadratic : solveMulsDivs n = gaussExactOps n + n²` showing the RHS
  handling is a pure lower-order `n²` correction, so the cubic `n³/3` headline lives
  entirely in the factorization.

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

-- ============================================================
-- Additions/subtractions and the full ~2n³/3 flop total (OQ-01)
-- ============================================================

/-- Exact **subtraction** count of forward elimination: clearing a column with `j` rows
    beneath the pivot updates, in each of those `j` rows, `j` trailing entries via
    `a := a − mult·pivotEntry` — one subtraction each, `j²` per step, summed over `j < n`.
    (Equivalently the number of multiply–subtract pairs in the trailing-submatrix update.) -/
def gaussExactSubs (n : ℕ) : ℕ := ∑ j ∈ range n, j ^ 2

/-- Unfolding one elimination step for the subtraction count. -/
lemma gaussExactSubs_succ (n : ℕ) :
    gaussExactSubs (n + 1) = gaussExactSubs n + n ^ 2 := by
  unfold gaussExactSubs; rw [Finset.sum_range_succ]

/-- **Closed form for the subtraction count (subtraction-free over ℕ).**
    `6·gaussExactSubs n + 3·n² = 2·n³ + n`, i.e. `gaussExactSubs n = (2n³ − 3n² + n)/6` —
    the classic `∑_{j<n} j²`, asymptotically `n³/3` (matching the `≈ n³/3` additions of the
    `2n³/3`-flop headline). -/
theorem gaussExactSubs_closed (n : ℕ) :
    6 * gaussExactSubs n + 3 * n ^ 2 = 2 * n ^ 3 + n := by
  induction n with
  | zero => simp [gaussExactSubs]
  | succ m ih =>
    calc 6 * gaussExactSubs (m + 1) + 3 * (m + 1) ^ 2
        = (6 * gaussExactSubs m + 3 * m ^ 2) + (6 * m ^ 2 + 6 * m + 3) := by
          rw [gaussExactSubs_succ]; ring
      _ = (2 * m ^ 3 + m) + (6 * m ^ 2 + 6 * m + 3) := by rw [ih]
      _ = 2 * (m + 1) ^ 3 + (m + 1) := by ring

/-- The full leading **flop** count of forward elimination: multiplications + divisions
    (`gaussExactOps`) together with the equal number of subtractions (`gaussExactSubs`). -/
def gaussExactFlops (n : ℕ) : ℕ := gaussExactOps n + gaussExactSubs n

/-- **Closed form for the total flop count (subtraction-free).**
    `6·gaussExactFlops n + 3·n² + n = 4·n³`, i.e. `gaussExactFlops n = (4n³ − 3n² − n)/6`,
    asymptotically `2n³/3` — the textbook leading flop count for dense Gaussian elimination
    / LU factorization (`≈ n³/3` multiplications + `≈ n³/3` additions). -/
theorem gaussExactFlops_closed (n : ℕ) :
    6 * gaussExactFlops n + 3 * n ^ 2 + n = 4 * n ^ 3 := by
  have h1 := gaussExactOps_closed n
  have h2 := gaussExactSubs_closed n
  unfold gaussExactFlops
  omega

/-- The total flop count dominates the multiplication+division count: the subtractions are
    genuine extra work. `gaussExactOps n ≤ gaussExactFlops n`. -/
theorem gaussExactOps_le_flops (n : ℕ) : gaussExactOps n ≤ gaussExactFlops n := by
  unfold gaussExactFlops; exact Nat.le_add_right _ _

/-- Concrete total flop counts (multiplications+divisions plus subtractions):
    `n=2 ↦ 3`, `n=3 ↦ 13`, `n=4 ↦ 34`, `n=5 ↦ 70`. -/
lemma gaussExactFlops_small :
    gaussExactFlops 2 = 3 ∧ gaussExactFlops 3 = 13 ∧
    gaussExactFlops 4 = 34 ∧ gaussExactFlops 5 = 70 := by
  have h2 := gaussExactFlops_closed 2
  have h3 := gaussExactFlops_closed 3
  have h4 := gaussExactFlops_closed 4
  have h5 := gaussExactFlops_closed 5
  norm_num at h2 h3 h4 h5
  omega

-- ============================================================
-- Right-hand-side handling and the COMPLETE linear solve (OQ-01)
-- ============================================================
--
-- The counts above (`gaussExactOps`, `gaussExactSubs`, `gaussExactFlops`) account
-- only for **factoring the matrix** (forward elimination of `A`). To actually
-- *solve* `A x = b` one must also (i) forward-eliminate the right-hand side `b`
-- and (ii) back-substitute through the resulting upper-triangular system. Both of
-- these are merely **quadratic** in `n`, so they leave the cubic leading term
-- untouched — the headline `n³/3` multiplications live entirely in the
-- factorization. We pin that down exactly: the full multiplication+division count
-- of a complete solve exceeds the factorization count by *precisely* `n²`.

/-- The triangular (Gauss) sum `∑_{i<n} i = n(n−1)/2`, the shape of both the
    right-hand-side and back-substitution multiplication counts. -/
def gaussSum (n : ℕ) : ℕ := ∑ i ∈ range n, i

/-- Unfolding one term of the triangular sum. -/
lemma gaussSum_succ (n : ℕ) : gaussSum (n + 1) = gaussSum n + n := by
  unfold gaussSum; rw [Finset.sum_range_succ]

/-- **Closed form (subtraction-free).** `2 · gaussSum n + n = n²`, i.e.
    `gaussSum n = (n² − n)/2`. -/
theorem gaussSum_closed (n : ℕ) : 2 * gaussSum n + n = n ^ 2 := by
  induction n with
  | zero => simp [gaussSum]
  | succ m ih =>
    calc 2 * gaussSum (m + 1) + (m + 1)
        = (2 * gaussSum m + m) + (2 * m + 1) := by rw [gaussSum_succ]; ring
      _ = m ^ 2 + (2 * m + 1) := by rw [ih]
      _ = (m + 1) ^ 2 := by ring

/-- **Right-hand-side forward-elimination multiplications.** At the step clearing a
    column with `j` rows beneath the pivot, each of those rows updates its single RHS
    entry `b := b − mult · b_pivot` — one multiplication per row, `j` per step, so
    `∑_{j<n} j = n(n−1)/2` in total. -/
def rhsElimMuls (n : ℕ) : ℕ := gaussSum n

/-- **Back-substitution multiplications.** Solving the upper-triangular `U x = y`,
    the unknown with `i` already-solved entries to its right costs `i` multiplications
    (one per term `U_{i,k} · x_k`), so `∑_{i<n} i = n(n−1)/2` in total. Back-substitution
    additionally performs exactly `n` divisions (one per pivot, `x_i := (…)/U_{i,i}`). -/
def backSubMuls (n : ℕ) : ℕ := gaussSum n

/-- **Total multiplications + divisions for a COMPLETE linear solve `A x = b`:**
    forward elimination of the matrix (`gaussExactOps`), forward elimination of the
    right-hand side (`rhsElimMuls`), and back-substitution (`backSubMuls` multiplications
    plus `n` divisions). -/
def solveMulsDivs (n : ℕ) : ℕ :=
  gaussExactOps n + rhsElimMuls n + backSubMuls n + n

/-- **Closed form for the complete-solve count (subtraction-free).**
    `3 · solveMulsDivs n + n = n³ + 3n²`, i.e. `solveMulsDivs n = (n³ + 3n² − n)/3`,
    asymptotically `n³/3` — the same cubic leading term as the bare factorization. -/
theorem solveMulsDivs_closed (n : ℕ) :
    3 * solveMulsDivs n + n = n ^ 3 + 3 * n ^ 2 := by
  have h1 := gaussExactOps_closed n
  have h2 := gaussSum_closed n
  unfold solveMulsDivs rhsElimMuls backSubMuls
  omega

/-- The complete-solve count in explicit division form: `(n³ + 3n² − n)/3`. -/
theorem solveMulsDivs_eq_div (n : ℕ) :
    solveMulsDivs n = (n ^ 3 + 3 * n ^ 2 - n) / 3 := by
  have h : 3 * solveMulsDivs n = n ^ 3 + 3 * n ^ 2 - n := by
    have := solveMulsDivs_closed n; omega
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)]

/-- **The cubic leading term lives entirely in the factorization.** The right-hand-side
    handling and back-substitution add *exactly* `n²` multiplications+divisions on top of
    the matrix-factorization count: `solveMulsDivs n = gaussExactOps n + n²`. So the
    `n³/3` headline is precisely the cost of factoring `A`; everything RHS-related is
    a lower-order `n²` correction. -/
theorem solve_overhead_quadratic (n : ℕ) :
    solveMulsDivs n = gaussExactOps n + n ^ 2 := by
  have h := gaussSum_closed n
  unfold solveMulsDivs rhsElimMuls backSubMuls
  omega

/-- The complete solve still costs no more than the parent's loose `n³` model
    (for `n ≥ 4`): `solveMulsDivs n ≤ n³`. The quadratic RHS overhead is absorbed
    by the gap between the exact `(n³−n)/3` factorization count and `n³`. -/
theorem solveMulsDivs_le_cube {n : ℕ} (hn : 4 ≤ n) : solveMulsDivs n ≤ n ^ 3 := by
  have hc := solveMulsDivs_closed n
  have hpow : 2 * n ^ 2 ≤ n ^ 3 := by
    calc 2 * n ^ 2 ≤ n * n ^ 2 := by gcongr; omega
      _ = n ^ 3 := by ring
  omega

/-- With the full complete-solve accounting (factorization + RHS + back-substitution),
    Gaussian elimination *still* beats Cramer's rule for `n ≥ 4` — the quadratic RHS
    overhead is dwarfed by the factorial blow-up of Cramer's rule. -/
theorem solve_beats_cramer {n : ℕ} (hn : 4 ≤ n) :
    solveMulsDivs n < CramersComplexity.cramersRuleMuls n :=
  lt_of_le_of_lt (solveMulsDivs_le_cube hn) (CramersComplexity.gauss_beats_cramer hn)

/-- Concrete complete-solve counts: `n=2 ↦ 6`, `n=3 ↦ 17`, `n=4 ↦ 36`, `n=5 ↦ 65`
    (factorization `2,8,20,40` plus the `n²` overhead `4,9,16,25`). -/
lemma solveMulsDivs_small :
    solveMulsDivs 2 = 6 ∧ solveMulsDivs 3 = 17 ∧
    solveMulsDivs 4 = 36 ∧ solveMulsDivs 5 = 65 := by
  have h2 := solveMulsDivs_closed 2
  have h3 := solveMulsDivs_closed 3
  have h4 := solveMulsDivs_closed 4
  have h5 := solveMulsDivs_closed 5
  norm_num at h2 h3 h4 h5
  omega

/-- Summary of the complete-solve accounting: closed form, division form, the exact
    `n²` overhead over the factorization, and the preserved comparison verdict. -/
theorem solve_complete_summary :
    (∀ n : ℕ, 3 * solveMulsDivs n + n = n ^ 3 + 3 * n ^ 2) ∧
    (∀ n : ℕ, solveMulsDivs n = (n ^ 3 + 3 * n ^ 2 - n) / 3) ∧
    (∀ n : ℕ, solveMulsDivs n = gaussExactOps n + n ^ 2) ∧
    (∀ n : ℕ, 4 ≤ n → solveMulsDivs n < CramersComplexity.cramersRuleMuls n) :=
  ⟨solveMulsDivs_closed, solveMulsDivs_eq_div, solve_overhead_quadratic,
   fun _ h => solve_beats_cramer h⟩

-- ============================================================
-- The COMPLETE-SOLVE full flop count: the ~2n³/3 headline (OQ-01)
-- ============================================================
--
-- `solveMulsDivs` counts only multiplications+divisions of a complete solve.
-- The textbook "≈ 2n³/3 flops to solve a linear system" also counts the
-- additions/subtractions. We complete the accounting: every multiplication in
-- the right-hand-side elimination and in back-substitution is paired with one
-- subtraction (`b := b − mult·b_pivot`, `x_i := (y_i − Σ U_{i,k}x_k)/U_{i,i}`),
-- and the matrix factorization contributes its `gaussExactSubs` subtractions.
-- Summing everything yields the full leading `2n³/3` flop count of a solve.

/-- **Right-hand-side elimination subtractions.** Each RHS multiplication
    `b := b − mult · b_pivot` is paired with one subtraction, so the count matches
    `rhsElimMuls`: `∑_{j<n} j = n(n−1)/2`. -/
def rhsElimSubs (n : ℕ) : ℕ := gaussSum n

/-- **Back-substitution subtractions.** Each of the `i` multiply terms
    `U_{i,k} · x_k` accumulated for the `i`-th unknown is subtracted off, so the
    count matches `backSubMuls`: `∑_{i<n} i = n(n−1)/2`. -/
def backSubSubs (n : ℕ) : ℕ := gaussSum n

/-- **Total leading flop count of a COMPLETE linear solve `A x = b`:** the matrix
    factorization flops (`gaussExactFlops` = multiplications + divisions +
    subtractions), the right-hand-side elimination (multiplications and
    subtractions), and back-substitution (multiplications, subtractions, and the
    `n` pivot divisions). -/
def solveFlops (n : ℕ) : ℕ :=
  gaussExactFlops n + rhsElimMuls n + rhsElimSubs n + backSubMuls n + backSubSubs n + n

/-- **Closed form for the complete-solve flop count (subtraction-free).**
    `6 · solveFlops n + 7·n = 4·n³ + 9·n²`, i.e. `solveFlops n = (4n³ + 9n² − 7n)/6`,
    asymptotically `2n³/3` — the classic textbook flop count for solving a dense
    linear system by Gaussian elimination. -/
theorem solveFlops_closed (n : ℕ) :
    6 * solveFlops n + 7 * n = 4 * n ^ 3 + 9 * n ^ 2 := by
  have h1 := gaussExactFlops_closed n
  have h2 := gaussSum_closed n
  unfold solveFlops rhsElimMuls rhsElimSubs backSubMuls backSubSubs
  omega

/-- The complete-solve flop count in explicit division form: `(4n³ + 9n² − 7n)/6`. -/
theorem solveFlops_eq_div (n : ℕ) :
    solveFlops n = (4 * n ^ 3 + 9 * n ^ 2 - 7 * n) / 6 := by
  have h : 6 * solveFlops n = 4 * n ^ 3 + 9 * n ^ 2 - 7 * n := by
    have := solveFlops_closed n; omega
  rw [← h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 6)]

/-- The full flop count dominates the multiplication+division count: the
    subtractions are genuine extra work. `solveMulsDivs n ≤ solveFlops n`. -/
theorem solveMulsDivs_le_flops (n : ℕ) : solveMulsDivs n ≤ solveFlops n := by
  -- `solveFlops = solveMulsDivs + gaussExactSubs + (rhs + back-sub) subtractions`;
  -- the extra subtraction terms are manifestly nonnegative.
  unfold solveFlops solveMulsDivs gaussExactFlops rhsElimMuls rhsElimSubs backSubMuls backSubSubs
  omega

/-- **The `2n³/3` leading term is asymptotically below the loose `n³` model.**
    For `n ≥ 4` the complete-solve flop count stays under the parent's `n³`
    multiplication model: `solveFlops n ≤ n³`. (The crossover is exactly at
    `n = 4`: `solveFlops 3 = 28 > 27 = 3³`, `solveFlops 4 = 62 ≤ 64 = 4³`.) -/
theorem solveFlops_le_cube {n : ℕ} (hn : 4 ≤ n) : solveFlops n ≤ n ^ 3 := by
  have hc := solveFlops_closed n
  have hpow : 9 * n ^ 2 ≤ 2 * n ^ 3 + 7 * n := by nlinarith
  omega

/-- With the full complete-solve flop accounting (factorization + RHS +
    back-substitution, multiplications *and* additions/subtractions), Gaussian
    elimination *still* beats Cramer's rule for `n ≥ 4`. -/
theorem solveFlops_beats_cramer {n : ℕ} (hn : 4 ≤ n) :
    solveFlops n < CramersComplexity.cramersRuleMuls n :=
  lt_of_le_of_lt (solveFlops_le_cube hn) (CramersComplexity.gauss_beats_cramer hn)

/-- Concrete complete-solve flop counts: `n=2 ↦ 9`, `n=3 ↦ 28`, `n=4 ↦ 62`,
    `n=5 ↦ 115`. -/
lemma solveFlops_small :
    solveFlops 2 = 9 ∧ solveFlops 3 = 28 ∧
    solveFlops 4 = 62 ∧ solveFlops 5 = 115 := by
  have h2 := solveFlops_closed 2
  have h3 := solveFlops_closed 3
  have h4 := solveFlops_closed 4
  have h5 := solveFlops_closed 5
  norm_num at h2 h3 h4 h5
  omega

/-- Summary of the complete-solve flop accounting: closed form, division form,
    dominance over the mul/div count, and the preserved comparison verdict. -/
theorem solve_flops_summary :
    (∀ n : ℕ, 6 * solveFlops n + 7 * n = 4 * n ^ 3 + 9 * n ^ 2) ∧
    (∀ n : ℕ, solveFlops n = (4 * n ^ 3 + 9 * n ^ 2 - 7 * n) / 6) ∧
    (∀ n : ℕ, solveMulsDivs n ≤ solveFlops n) ∧
    (∀ n : ℕ, 4 ≤ n → solveFlops n < CramersComplexity.cramersRuleMuls n) :=
  ⟨solveFlops_closed, solveFlops_eq_div, solveMulsDivs_le_flops,
   fun _ h => solveFlops_beats_cramer h⟩

end CramersComplexityExact

#print axioms CramersComplexityExact.solveFlops_closed
#print axioms CramersComplexityExact.solveFlops_beats_cramer
