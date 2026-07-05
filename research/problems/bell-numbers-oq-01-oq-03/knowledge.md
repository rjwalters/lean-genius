# Knowledge Base: bell-numbers-oq-01-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-04 (researcher-6) - Duplicate triage: already solved on main

**Mode**: FRESH
**Outcome**: completed (duplicate — no PR)

### What I Did
- Selected this problem (was the highest-scoring MODERATE/RICH available slot the depth-first rule pointed at after blocked/done candidates were ruled out).
- Independently derived the full induction proof (base `decide`; step: `sum_range_succ'` to peel k=0, `stirlingFirst_succ_succ` termwise, split, index-shift `A + c(n,0) = R n`, `n·c(n,0)=0` aux, fold `(n+1)·n! = (n+1)!`).
- Before writing a file, grepped `proofs/Proofs/` and found `StirlingFirstKindOQ01.lean` already ships the **byte-for-byte target**.

### Key Findings
- `proofs/Proofs/StirlingFirstKindOQ01.lean:69` `stirlingFirst_row_sum (n) : ∑ k ∈ Finset.range (n+1), Nat.stirlingFirst n k = n !` — VERIFIED, 0 sorries, git-tracked on origin/main.
- Plus the identical aux lemma `stirlingFirst_mul_zero_left:56` (`n * stirlingFirst n 0 = 0`) and bonus `stirlingFirst_row_sum_pos:104`.
- The proof strategy in that file is exactly the one I re-derived — this OQ is a redundant sibling of the `stirling-first-kind` gallery family (the problem.md even lists that family under "Related Gallery Proofs" but the seeker did not detect the existing proof).

### Files Modified
- `src/data/research/problems/bell-numbers-oq-01-oq-03.json` (status→completed, phase→COMPLETED, insight recorded)
- `research/db/knowledge.db`, `.lean/state/candidate-pool.json`, `research/candidate-pool.json` (status→completed)

### Next Steps
- None. Solved under the `stirling-first-kind` slug. Do NOT ship a duplicate `StirlingFirst*` file.
