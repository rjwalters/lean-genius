# derangements-convergence-oq-06-oq-01

**Statement**: Effective two-sided sandwich on the derangement error:
`1/(n+2) ≤ |D(n) − n!·e⁻¹| ≤ 1/(n+1)` for all n. Answers OQ-06 open question 1.

**Status**: COMPLETED — VERIFIED, 0-axiom. PR #33275.

## Session 2026-07-02 (Session 1) — FRESH — COMPLETED

### What I Did
- Selected from available pool (tractability 7). Parent `derangements-convergence-oq-06`
  (D(n)=round(n!/e)) openQuestion[0] asks for exactly this sandwich.
- Built `proofs/Proofs/DerangementsConvergenceOQ06OQ01.lean` (12 thm/lemma, 1 def, 181L)
  reusing the parent's alternating-series partial-sum envelope.

### Key Findings
- The error is EXACTLY the alternating factorial tail `T(m)=∑'k (−1)^k/(m+k)!`,
  with `|D(n)/n! − e⁻¹| = T(n+1)`.
- One recurrence does everything: `T(m) = 1/m! − T(m+1)` (peel k=0 via
  `Summable.tsum_eq_zero_add`). The parent's one-sided envelope `0 ≤ T ≤ 1/m!`
  then upgrades to two-sided: upper bound on T(m+1) → lower bound on T(m).
- Integer scale telescopes: `n!·(1/(n+1)! − 1/(n+2)!) = 1/(n+2)` exactly.

### Gotchas
- Lemma name is `Summable.tsum_eq_zero_add` (method on the summability proof),
  NOT `tsum_eq_zero_add`.
- Factoring `altFactTerm(n+1+k) = (-1)^(n+1)·(...)`: must `set m := n+1` BEFORE
  simp, else `simp [pow_add]` splits `(-1)^(n+1)` and introduces a spurious sign.
  (Parent's `alternating_tail_bound` uses the same `set m` trick.)

### Files
- proofs/Proofs/DerangementsConvergenceOQ06OQ01.lean
- src/data/proofs/derangements-convergence-oq-06-oq-01/{meta.json,annotations.json,index.ts}

### Next Steps (follow-ups, not done)
- Iterate recurrence once more for asymptotic `= 1/(n+1) − 1/((n+1)(n+2)) + O(1/n³)`.
- Extend to partial derangements D(n,r).
