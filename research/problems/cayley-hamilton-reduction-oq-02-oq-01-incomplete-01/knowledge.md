# Knowledge Base: cayley-hamilton-reduction-oq-02-oq-01-incomplete-01

---

## Session 2026-05-30 — STATE-SYNC (gallery-meta + pool drift)

**Mode**: REVISIT (verification + maintenance)
**Outcome**: completed — work already done upstream; gallery meta + pool drift fixed

### What I Found

The goal of this problem (fill 3 sorries in `CayleyHamiltonReductionOQ02OQ01.lean`
at the original lines 183 / 194 / 210) has already been achieved upstream:

- `proofs/Proofs/CayleyHamiltonReductionOQ02OQ01.lean`: **0 sorries, 0 axioms, 396 lines, 18 theorems**.
- `aeval_companionMatrix_mulVec_e0` (the orbit-kills-p(C(p)) argument)
  is proved at L222–230 via `aeval_eq_sum_pow` + `pow_d_mulVec_e0` + Hölder
  reindexing of the orbit sum.
- The full chain `aeval p (C(p)) = 0` → `minpoly = p` → `charpoly = p`
  is settled.

### Drift Found and Fixed

1. **Gallery meta drift** (`src/data/proofs/cayley-hamilton-reduction-oq-02-oq-01/meta.json`):
   - Was: `status: "formalized"` (the legacy state for files with sorries)
   - Now: `status: "verified"` (matches the actual 0-sorry / 0-axiom main file)
   - The companion `CayleyHamiltonReductionOQ02OQ01Aristotle.lean` carries 12
     proof-search stubs but is *not* imported by the main file, so it does not
     contaminate the verified status — same pattern as sibling entries
     `cayley-hamilton-cyclic-vector-all-fields` and `cayley-hamilton-minpoly-oq-03`
     (both already `verified` with Aristotle companions).

2. **Pool drift** (`candidate-pool.json` showed `"in-progress"`):
   - This incomplete-01 placeholder was a completion-target for the parent's
     three sorries. Those sorries are gone, so the placeholder is satisfied.
   - Marked `completed` via `claim-problem.sh update ... completed`.

### Files Modified

- `src/data/proofs/cayley-hamilton-reduction-oq-02-oq-01/meta.json` — status formalized → verified
- `research/problems/cayley-hamilton-reduction-oq-02-oq-01-incomplete-01/knowledge.md` — this entry

### Next Steps

None — placeholder retired. Future work on the RCF roadmap belongs in a fresh
problem targeting the ~1800-line Smith-Normal-Form gap, not this completion stub.
