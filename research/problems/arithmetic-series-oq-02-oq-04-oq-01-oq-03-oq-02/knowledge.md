# arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02

**Problem**: Prove the multiset Vandermonde identity
  `multichoose(m+n, r) = Σ_{j=0}^{r} multichoose(m,j) * multichoose(n,r-j)`

**Status**: ACT — proof written, building

## Session 2026-04-21 (Session 1)

**Mode**: FRESH
**Outcome**: proof written

### What I Did
- Surveyed Mathlib for `Nat.multichoose` infrastructure
- Key lemmas available: `multichoose_succ_succ`, `multichoose_zero_right`, `multichoose_zero_succ`, `multichoose_eq`
- No multiset Vandermonde identity in Mathlib
- Wrote double-induction proof:
  - Outer induction on `m`, inner on `r`
  - Key lemma `sum_succ_left`: Σ mc(m+1,j)*mc(n,r+1-j) = Σ mc(m,j)*mc(n,r+1-j) + Σ mc(m+1,j)*mc(n,r-j)
  - Proof uses `Finset.sum_range_succ'`, `Nat.succ_sub_succ_eq_sub`, `multichoose_succ_succ`
- Created gallery files

### Files Modified
- `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02.lean` (created)
- `src/data/proofs/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02/` (created)

### Next Steps
- Verify build succeeds
- If build fails, fix errors and rebuild
- Commit, push, create PR

## Session 2026-06-15 (Session 2) — verification + close-out

**Mode**: REVISIT
**Outcome**: COMPLETED (no churn to the proof — already shipped and verified)

### What I Did
- The Session 1 "next step: verify build" was stale. The Lean file
  `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02.lean` is **already merged to `main`** and was
  audited clean in #22746 (commit d8284214ed0), so it builds. It is registered in
  `Proofs.lean` (line 147).
- Re-audited the proof logic by hand. The engine lemma `sum_succ_left` is correct:
  peel j=0 from both range(r+2) sums (each j=0 term is `mc n (r+1)`, a shared atom),
  align indices via `r+1-(j+1) = r-j`, expand `mc(m+1)(j+1) = mc m (j+1) + mc(m+1) j`
  via `multichoose_succ_succ`, distribute with `sum_add_distrib`, close by `ring`.
  Main theorem's double induction wiring is sound.
- Confirmed all Mathlib lemma names (`multichoose_succ_succ`, `multichoose_zero_right`,
  `multichoose_zero_succ`, `multichoose_eq`) are valid at our pin — the audit-passed
  sibling `…OQ03.lean` uses the identical names.
- Confirmed gallery `meta.json` is complete: `status: verified`, `badge: original`,
  `axiomCount: 0`, `sorries: 0`, `theoremCount: 3` (2 lemmas + 1 theorem).
  `annotations.json` present.

### Conclusion
Problem is fully solved, verified, and in the gallery. No genuine residual work.
Marked COMPLETED to stop the pool from re-serving a finished entry.
