# Knowledge Base: erdos-1-oq-02-oq-02

**Status**: COMPLETED — `dfx_lower_bound` is fully proved (0 sorries) since
PR [#12782](https://github.com/rjwalters/lean-genius/pull/12782) (merged
2026-04-26).

---

## Problem Understanding

This problem entry was created 2026-04-23 to track a **base-case sorry** in
`dfx_lower_bound`: how to handle the small cases $n = 1$ and $n = 2$, where the
inductive argument of the Dubroff–Fox–Xu lower bound does not kick in and a
direct computation is needed. The original concern was that
$\lfloor \sqrt{2/\pi} \cdot 2^n / \sqrt{n}\rfloor$ does not normalize under
`norm_num` because `Real.sqrt` and `Real.pi` are stubborn.

This problem entry was superseded **before** any research session against the
slug ran: PR #12782 (2026-04-26) reformulated `dfx_lower_bound`'s signature to
exclude the small cases by precondition rather than by computation, eliminating
the `sorry`.

---

## Resolution (Session 2 — 2026-05-07)

**Mode**: REVISIT (verification + state reconciliation)
**Outcome**: COMPLETED — Lean side already done; this session reconciles the
research-tracking metadata.

### What I Did

1. **Inspected `proofs/Proofs/Erdos1OQ02.lean`** (268 lines, 1 axiom, 0
   sorries). The relevant theorem is at line 145:

   ```lean
   theorem dfx_lower_bound (A : Finset ℕ) (N : ℕ)
       (hDSS : hasDistinctSubsetSums A) (hA : ∀ a ∈ A, a ≤ N)
       (hpos : 0 < A.card) (hN : 2 ≤ N)
       (hA_pos : ∀ a ∈ A, 0 < a) :
       (2 : ℝ) ^ A.card ≤ Real.sqrt (2 / π) * 2 * ↑(A.card) * ↑N
                       / Real.sqrt ↑(A.card) := by ...
   ```

   The proof is entirely algebraic (Cauchy–Schwarz + sqrt manipulation +
   `anticoncentration_bound` axiom). No base-case `sorry`.

2. **Confirmed the small-case witnesses are proved separately**, not as
   subcases of `dfx_lower_bound`:
   - `f_one : ∃ A : Finset ℕ, A.card = 1 ∧ hasDistinctSubsetSums A ∧ A.sup id = 1`
     (witness: `{1}`)
   - `f_two_max : ∃ A : Finset ℕ, A.card = 2 ∧ A.sup id = 2`
     (witness: `{1, 2}`)

3. **Located the resolving PR.** `git log -- proofs/Proofs/Erdos1OQ02.lean`
   shows commit `72ed399f304` (PR
   [#12782](https://github.com/rjwalters/lean-genius/pull/12782), 2026-04-26):
   *"feat(erdos-1-wip-01): prove dfx_lower_bound + pow2_dss (3 sorries
   removed)"*. That PR removed the `sorry` this problem entry was created
   to track.

### Insights

- **Right abstraction was preconditions, not computation.** The original
  problem brief proposed `by norm_num` or `by native_decide` to discharge
  $n = 1, 2$ at the value level. That doesn't work for terms involving
  `Real.sqrt` and `Real.pi`. The actual fix was to *narrow the theorem's
  domain* — adding `hN : 2 ≤ N` and `hA_pos : ∀ a ∈ A, 0 < a` excludes the
  small cases by hypothesis. Small-card existence is proved as separate
  theorems where they fit (`f_one`, `f_two_max`).

- **`Real.sqrt` and `Real.pi` are not `norm_num`-friendly.** Anyone tempted
  to discharge inequalities involving `√(2/π)` numerically should expect
  `norm_num` to fail and reach for hypothesis-tightening or Mathlib's
  `Real.pi_gt_three` / `Real.sqrt_lt_sqrt` interval reasoning instead.

- **The remaining axiom is intentional.** `anticoncentration_bound` is the
  Berry–Esseen anti-concentration estimate that the DFX paper invokes
  blackbox. Discharging it requires Mathlib probability infrastructure that
  is out-of-scope for *this* OQ; that work is tracked by
  `erdos-1-oq-02-oq-01`.

### Built Items (from PR #12782)

- `Erdos1OQ02.lean : dfx_lower_bound` — theorem, 73 lines, 0 sorries, proved
- `Erdos1OQ02.lean : f_one` — small-case DSS witness for $n = 1$, proved
- `Erdos1OQ02.lean : f_two_max` — small-case DSS witness for $n = 2$, proved
- Supporting lemmas: `sum_sq_cauchy_schwarz`, `sum_sq_le_card_mul_max_sq`,
  `sum_le_card_mul_max` (all proved in the same file)

### Dead Ends Avoided (recorded for future reference)

- **Numerical base-case discharge of $\lfloor \sqrt{2/\pi} \cdot 2^n /
  \sqrt{n}\rfloor$ for $n = 1, 2$ via `norm_num` / `native_decide`.**
  Doesn't reduce because `Real.sqrt` and `Real.pi` are uncomputable. The
  original problem brief flagged this risk but proposed it anyway; the
  team correctly chose hypothesis-tightening instead.

---

## Status

**RESOLVED 2026-04-26** by PR #12782. This entry is closed.
