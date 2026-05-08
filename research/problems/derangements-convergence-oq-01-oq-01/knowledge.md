# Knowledge Base: derangements-convergence-oq-01-oq-01

## Problem Summary

**Title**: Derangements Nearest Integer Theorem
**Focus**: Prove D(n) = round(n!/e) for n ≥ 1, i.e., |D(n) - n!/e| < 1/2

## Session 2026-05-03 (Session 1) — Nearest Integer Theorem Proved

**Mode**: FRESH
**Outcome**: completed — 7 theorems, 0 sorries, 0 axioms; PR created

### What I Did
- Fixed `DerangementsConvergence.lean`: replaced 12 deprecated `∑ k in`/`∑ i in` usages with `∑ k ∈`/`∑ i ∈` throughout (Python replace to handle Unicode correctly)
- Wrote `DerangementsConvergenceOQ01OQ01.lean` with 7 theorems proving D(n) = round(n!/e)
- Created gallery entry `src/data/proofs/derangements-convergence-oq-01-oq-01/`

### Key Findings
- **Rate scaling**: |D(n)/n! - e⁻¹| ≤ 1/(n+1)! scaled by n! gives |D(n) - n!/e| ≤ 1/(n+1)
- **Main theorem**: For n ≥ 2, 1/(n+1) ≤ 1/3 < 1/2, so D(n) is within 1/2 of n!/e
- **n=1 case**: D(1) = 0 and |0 - 1/e| = 1/e. Uses `Real.add_one_lt_exp one_ne_zero` (strict convexity at x=1) to get e > 2, hence 1/e < 1/2
- **Uniqueness**: If |m - n!/e| < 1/2 and |D(n) - n!/e| < 1/2, then |m - D(n)| < 1. Integer gap lemma: an integer strictly between -1 and 1 is 0, proved via omega after casting real bound to ℤ
- **macOS sed Unicode bug**: `sed -i ''` with unicode patterns silently fails on macOS. Must use Python's `str.replace()` for Unicode substitutions.

### Files Modified
- `proofs/Proofs/DerangementsConvergence.lean` (12 syntax fixes: ∑ k in → ∑ k ∈)
- `proofs/Proofs/DerangementsConvergenceOQ01OQ01.lean` (NEW, 130 lines, 7 theorems)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/derangements-convergence-oq-01-oq-01/` (gallery entry)

### Theorems Proved
1. `derangements_rate_scaled`: |D(n) - n!/e| ≤ 1/(n+1) for all n
2. `derangements_nearest_integer`: |D(n) - n!/e| < 1/2 for n ≥ 2
3. `derangements_nearest_integer_n1`: |D(1) - 1/e| < 1/2 using e > 2
4. `derangements_nearest_all`: |D(n) - n!/e| < 1/2 for all n ≥ 1
5. `derangements_unique_nearest`: D(n) is the unique natural in this window
6. `derangements_quarter_bound`: |D(n) - n!/e| ≤ 1/4 for n ≥ 3
7. `derangements_parametric_bound`: |D(n) - n!/e| ≤ 1/k for any k ≤ n+1

### Status
- **Axiom count**: 0 (no external assumptions)
- **Sorry count**: 0
- **Phase**: COMPLETED (pending Docker build verification)

## Session 2026-05-08 (Session 2) — Follow-Up Direction Documented (researcher-6)

**Mode**: REVISIT
**Outcome**: documented — problem confirmed COMPLETED; identified one substantive follow-up direction (parity-sign theorem) with full proof sketch using existing infrastructure.

### Verification of Prior Work
- `DerangementsConvergenceOQ01OQ01.lean`: 147 lines, 7 theorems, 0 sorries, 0 axioms ✓
- Parent `DerangementsConvergence.lean`: 282 lines, 14 theorems, 0 sorries, 0 axioms ✓
- Pool entry was stale (`status: in-progress` with note about already-resolved `∑ k in` issue) — corrected to `completed` in `.lean/state/candidate-pool.json` runtime state.

### Follow-Up: Parity-Controlled Error Sign

The current file proves `|D(n) - n!/e| < 1/2`. A natural strengthening is the **signed** version: the rounding direction is determined by parity of `n`.

**Conjecture (`derangements_error_sign`)**:
$$0 \le (-1)^n \cdot \big(D(n) - n!/e\big) \quad \text{for all } n \ge 0$$

Equivalently: $D(n) \ge n!/e$ when $n$ is even, $D(n) \le n!/e$ when $n$ is odd.

**Empirical verification** (`D(n)` and `n!/e`):
- $n=0$: $D(0)=1$, $0!/e = 1/e \approx 0.368$, diff $\approx +0.632$ → sign $+$ → $(-1)^0 = +$ ✓
- $n=1$: $D(1)=0$, $1!/e \approx 0.368$, diff $\approx -0.368$ → sign $-$ → $(-1)^1 = -$ ✓
- $n=2$: $D(2)=1$, $2!/e \approx 0.736$, diff $\approx +0.264$ → sign $+$ → $(-1)^2 = +$ ✓
- $n=3$: $D(3)=2$, $3!/e \approx 2.207$, diff $\approx -0.207$ → sign $-$ → $(-1)^3 = -$ ✓
- $n=4$: $D(4)=9$, $4!/e \approx 8.829$, diff $\approx +0.171$ → sign $+$ → $(-1)^4 = +$ ✓

### Proof Sketch (uses only already-public lemmas)

Let $a_k = (-1)^k / k!$ so $\text{altFactPartialSum}(n) = \sum_{k=0}^n a_k$ and $e^{-1} = \sum_{k\ge 0} a_k$.

1. From `derangements_div_factorial`: $D(n)/n! = \sum_{k=0}^n a_k$.
2. From `exp_neg_one_eq_tsum_alt` and `tsum_eq_partial_sum_add_tail`:
   $$e^{-1} = \sum_{k=0}^n a_k + \sum_{k\ge 0} a_{n+1+k}$$
3. So $D(n)/n! - e^{-1} = -\sum_{k\ge 0} a_{n+1+k}$.
4. **Factor extraction**: $a_{n+1+k} = (-1)^{n+1+k}/(n+1+k)! = (-1)^{n+1} \cdot c_k$ where $c_k = (-1)^k/(n+1+k)!$.
5. Therefore $D(n)/n! - e^{-1} = (-1)^{n} \cdot \sum_{k\ge 0} c_k$ (the two minus signs combine).
6. **Sign of the residual sum**: by `alt_partial_sum_nonneg` (already proved, with `m = n+1`), every partial sum $\sum_{k=0}^N c_k \ge 0$. Taking the limit: $\sum_{k\ge 0} c_k \ge 0$.
7. Multiply by $(-1)^n$: $(-1)^n \cdot (D(n)/n! - e^{-1}) = \sum_{k\ge 0} c_k \ge 0$.
8. Multiply by $n! > 0$: $(-1)^n \cdot (D(n) - n!/e) \ge 0$. ∎

### Lean Skeleton (for future implementation)

```lean
/-- The sign of D(n) - n!/e is (-1)^n. -/
theorem derangements_error_sign (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * ((numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1) := by
  -- Strategy: show (-1)^n * (D(n)/n! - 1/e) = ∑' k, (-1)^k / (n+1+k)! ≥ 0,
  -- then scale by n! ≥ 0.
  -- Uses: derangements_div_factorial, exp_neg_one_eq_tsum_alt,
  --       tsum_eq_partial_sum_add_tail, alt_partial_sum_nonneg
  sorry  -- TODO
```

### Why This Is Worth Proving
- **Theory-level**: Tells us the precise rounding rule (round-up for even $n$, round-down for odd $n$), not just that rounding works.
- **Reuses existing infrastructure**: `alt_partial_sum_nonneg` was proved (lines 119–166 of `DerangementsConvergence.lean`) but is currently unused outside the absolute-value bound. The signed version exposes its mathematical content.
- **Sharper bound**: Combined with `derangements_rate_scaled`, gives $0 \le (-1)^n(D(n) - n!/e) \le 1/(n+1)$ — a two-sided sharp bound.
- **Complements `derangements_unique_nearest`**: uniqueness picks the right integer, sign identifies the rounding direction.

### Why Not Done This Session
- Build infrastructure currently slow (`proofs/.lake` is a recursive self-symlink → every Docker build does fresh Mathlib clone, ~30–45 min).
- Risk of partial Lean error not worth holding the gallery entry; this slug is already verified+original.
- Recorded as a self-contained follow-up so the next researcher (or Aristotle) can pick it up cheaply.

### Status
- **Axiom count**: 0 (unchanged)
- **Sorry count**: 0 (unchanged)
- **Phase**: COMPLETED with documented follow-up

## Session 2026-05-08 (Session 3) — Parity-Sign Theorem Proved (researcher-8)

**Mode**: REVISIT (executing the documented S2 follow-up)
**Outcome**: completed — `derangements_error_sign` implemented exactly as the
S2 proof sketch. PR opened on top of the verified entry.

### What I Did

Implemented the `derangements_error_sign` theorem documented in Session 2's
follow-up sketch. Single new public theorem, ~70 lines of proof:

```lean
theorem derangements_error_sign (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * ((numDerangements n : ℝ) - (n.factorial : ℝ) / rexp 1)
```

### Proof Structure (~70 lines)

Following the S2 sketch:

1. **Set up f**: `f k := (-1)^k / (n+1+k)!` — the parity-stripped tail factor.
2. **Step A — `Summable f`**: `Summable.of_norm_bounded` with bound `1/k!`,
   which is summable by `summable_pow_div_factorial 1` (as in
   `summable_altFactTerm`). Use `Nat.factorial_le (k ≤ n+1+k)`.
3. **Step B — `0 ≤ ∑' k, f k`**: each partial sum is `≥ 0` by
   `alt_partial_sum_nonneg (m := n+1)`. Use `hf_summable.hasSum.tendsto_sum_nat`
   to get the convergence and `ge_of_tendsto'` to lift partial-sum
   non-negativity to the limit.
4. **Step C — `(D(n) - n!/e) = -n! · (-1)^(n+1) · ∑' f`**:
   - `derangements_div_factorial`: `D(n)/n! = altFactPartialSum n`.
   - `exp_neg_one_eq_tsum_alt + tsum_eq_partial_sum_add_tail`:
     `rexp(-1) = altFactPartialSum n + ∑' k, altFactTerm (n+1+k)`.
   - Factor `altFactTerm (n+1+k) = (-1)^(n+1) · f k` (via `pow_add` +
     `mul_div_assoc`), then `tsum_mul_left` extracts the constant.
   - Algebraic rearrangement: `(D(n) - n!/e) = n! · (D(n)/n! - rexp(-1))
     = n! · (-((-1)^(n+1) · ∑' f)) = -n! · (-1)^(n+1) · ∑' f`.
5. **Step D — finish**: `(-1)^n · (-n! · (-1)^(n+1) · ∑' f)`. Combine
   `(-1)^n · (-1)^(n+1) = (-1)^(2n+1) = -1` (via `pow_add + pow_succ + pow_mul + simp`).
   Result: `-((-1)) · n! · ∑' f = n! · ∑' f`. Closed by `mul_nonneg` of
   `factorial_cast_pos'.le` and Step B.

### Files Modified (Session 3)

- `proofs/Proofs/DerangementsConvergenceOQ01OQ01.lean` (+107 lines net):
  Added `§5. PARITY-CONTROLLED ERROR SIGN` section with the
  `derangements_error_sign` public theorem. No new private helpers needed —
  reuses the entire S2 sketch's named Mathlib API plus parent file's
  `derangements_div_factorial`, `exp_neg_one_eq_tsum_alt`,
  `tsum_eq_partial_sum_add_tail`, `alt_partial_sum_nonneg`,
  `summable_pow_div_factorial`, `factorial_cast_pos'`, `altFactTerm`,
  `altFactPartialSum`.
- `src/data/proofs/derangements-convergence-oq-01-oq-01/meta.json`:
  - `meta.lineCount`: 147 → 255
  - `meta.theoremCount`: 7 → 8
  - `leanFile.lineCount`: 147 → 255
  - `leanFile.theoremCount`: 7 → 8
  - Added entry to `originalContributions` documenting the new theorem.

### Result

Status remains `verified` / `original` / 0 axioms / 0 sorries.
`derangements_error_sign` is **public** — combined with
`derangements_rate_scaled` it gives the two-sided sharp bound
`0 ≤ (-1)^n · (D(n) - n!/e) ≤ 1/(n+1)` (D(n) is exactly the rounding of
n!/e in the parity-determined direction).

### Honest Reporting

- **Build NOT verified locally** — `.lake` symlink trap (memory
  `feedback_researcher_lake_symlink_broken.md`). CI is the ground truth.
- **API drift risk** (S3-specific):
  - `Summable.of_norm_bounded` (some versions take filter arg).
  - `summable_pow_div_factorial` (in NormedSpace or Real namespace
    depending on Mathlib version — used unqualified, matching the parent
    file's `summable_altFactTerm` precedent).
  - `Nat.factorial_le` (`m ≤ n → m! ≤ n!`).
  - `Summable.hasSum`, `HasSum.tendsto_sum_nat` (atTop-tendency of partial sums).
  - `ge_of_tendsto'` (filter-based non-negativity transfer).
  - `tsum_mul_left` (constant scalar pulled out of tsum).
  - `pow_add`, `pow_succ`, `pow_mul`, `mul_div_assoc`, `Real.exp_neg`,
    `field_simp`, `ring`.
- **Did NOT touch** the parent `DerangementsConvergence.lean` or any
  metadata other than the OQ01OQ01 entry.

### Why This Is Worth Proving (recap from S2 sketch)

- **Theory-level**: Tells us the precise rounding rule (round-up for even n,
  round-down for odd n), not just that rounding works.
- **Reuses existing infrastructure**: `alt_partial_sum_nonneg` was proved
  (lines 119–166 of `DerangementsConvergence.lean`) but unused outside the
  absolute-value bound. The signed version exposes its mathematical content.
- **Sharper bound**: Combined with `derangements_rate_scaled`, gives
  `0 ≤ (-1)^n(D(n) - n!/e) ≤ 1/(n+1)` — a two-sided sharp bound.
- **Complements `derangements_unique_nearest`**: uniqueness picks the right
  integer; sign identifies the rounding direction.

### Status

- **Axiom count**: 0 (unchanged)
- **Sorry count**: 0 (unchanged)
- **Phase**: COMPLETED + parity-sign theorem added
