# Knowledge Base: cramers-rule-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

- **(researcher-2, 2026-06-30) Complete linear-solve count.** Extended the file
  from factorization-only counts to a COMPLETE solve `A x = b`. Added the
  triangular sum `gaussSum n = ∑_{i<n} i` with subtraction-free closed form
  `2·gaussSum n + n = n²`, the RHS forward-elimination count `rhsElimMuls` and
  back-substitution count `backSubMuls` (both `= gaussSum n`), and
  `solveMulsDivs n = gaussExactOps n + rhsElimMuls n + backSubMuls n + n`
  (the `+ n` = back-substitution divisions, one per pivot).
- **Key structural result `solve_overhead_quadratic`: `solveMulsDivs n =
  gaussExactOps n + n²`.** The RHS handling + back-substitution add *exactly* `n²`
  multiplications+divisions, so the cubic `n³/3` headline lives entirely in the
  matrix factorization. Clean closed form `3·solveMulsDivs n + n = n³ + 3n²`,
  i.e. `(n³+3n²−n)/3`. Comparison preserved: `solve_beats_cramer` (n ≥ 4).
- **Subtraction-free template reused:** the same `k·sum + remainder = closed form`
  trick (here `2·gaussSum + n = n²`) keeps the Gauss-sum induction in the ℕ
  semiring so `ring` closes the successor step. omega then combines the two
  closed-form hypotheses (`gaussExactOps_closed`, `gaussSum_closed`) treating
  `n³, n², n` as atoms to discharge `solveMulsDivs_closed` / `solve_overhead_quadratic`.

---

## Dead Ends

- `mul_le_mul_right'` for `2·n² ≤ n·n²` is deprecated (→ warning). Use
  `by gcongr; omega` instead for the `2·n² ≤ n³` step in `solveMulsDivs_le_cube`.
