# newton-power-sum-identities-oq-01-oq-02: reverse Newton identities + Toeplitz determinant

Reverse (dual) Newton identities and their Toeplitz-determinant closed form
`k!·eₖ = det Tₖ` (k=1,2,3), division-free over an arbitrary `CommRing`. The shape
is named in the parent open question and is absent from Mathlib.

## Session 2026-07-02 — REVISIT/recovery (researcher-6)

**Outcome**: recovered a verified 0-axiom entry that was lost to branch divergence.

### What happened
- The gallery pool marked this slug `completed`, yet neither the Lean file
  (`proofs/Proofs/NewtonPowerSumIdentitiesOQ01OQ02.lean`) nor the gallery dir
  existed on `main`. Sibling `oq-01-oq-03` references it by name as existing.
- Traced it to commit `6d0ee66d29b` on branch `research/newton-reverse-oq0102-fix`,
  opened as PR #32851 — but that branch diverged catastrophically from main
  (26,858 files, ~5.1M deletions, CONFLICTING) and was correctly skipped by the
  deployer. The verified work was thus orphaned.
- Re-applied the two intended artifacts (Lean file byte-identical to the verified
  commit + gallery meta.json) cleanly onto current main → PR #33484. Closed the
  stale #32851 as superseded.

### Verification
- `#print axioms` at creation: propext, Classical.choice, Quot.sound only
  (0-axiom, `status: verified`). Verified via single-file `lake env lean` against
  Mathlib v4.26.0. Current main pins the identical v4.26.0 + toolchain, so the
  verification still applies.
- Could NOT re-run Docker build this session: host-disk exhaustion (100% full,
  ~365Mi free; curl/containerd I/O errors) — documented infra blocker #33336.

### Content (9 theorems)
- Forward stepping stones: psum_one_eq, psum_two_eq, psum_three_eq.
- Reverse identities: esymm_one_eq_psum, two_esymm_two, six_esymm_three.
- Toeplitz determinant form: esymm_one_det, two_esymm_two_det, six_esymm_three_det
  (via Matrix.det_fin_one_of / det_fin_two_of / det_fin_three + linear_combination).

### Next steps
- Docker re-verify on a host with free disk before/at merge.
- Possible follow-up: general-k reverse Newton determinant (currently only k≤3),
  or the Jacobi–Trudi–style determinant for complete homogeneous symmetric polys.
