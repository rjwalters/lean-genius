# Current State: zsqrtd-neg-two-oq-03

**Phase**: ACT (S2 ACT shipped, S3/S3b/S4 PREP all shipped; S3 ACT next — `EuclideanDomain Eisenstein` via rounding)
**Path**: full
**Since**: 2026-05-13T00:35:00Z (Session 6, researcher-4, STATE-SYNC)
**Iteration**: 6
**Researcher**: researcher-4 (Session 6 STATE-SYNC)

## Current Focus

Session 6 STATE-SYNC (researcher-4, 2026-05-13, **doc-only**): aligns
state.md with the merged PREP backlog. Four PR session-log entries
(auditor drift-sync #18462, S3 PREP #18557, S4 PREP #18573, S3b PREP
#18618) were merged into `main` after the original Session 2
state.md was written but never recorded here; the Open PRs row
also still said "(this PR) — TO BE OPENED" for S2 ACT even though
PR #18436 had merged. This sync:

1. Marks S2 ACT as MERGED (PR #18436); removes the stale
   "(this PR) — TO BE OPENED" row.
2. Adds rows for the four merged PREP / audit follow-ups
   (auditor-sync #18462, S3 PREP #18557, S4 PREP #18573, S3b PREP
   #18618).
3. Advances the Phase line to reflect that **all PREP work for S3
   and S4 is now complete** — the S3 ACT EuclideanDomain
   construction is fully pre-specified across three audit docs
   (#18557 + #18618 for S3, #18573 for S4), and the next session
   needs only a brief re-read of the audit citations before
   shipping ~200 LOC of Lean.
4. Advances the Iteration counter from 2 → 6 (each merged
   PREP/ACT/audit-sync counts as one project iteration:
   S1 OBSERVE = 1, S2 PREP = 2, S2 ACT + auditor sync = 3,
   S3 PREP = 4, S4 PREP = 5, S3b PREP = 6).
5. Lean changes: **none**. File-level counts unchanged at 13
   theorems / 2 definitions / 0 sorries / 0 axioms in
   `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (207 LOC on `main`).

## Historical Focus (S2 ACT, PR #18436, MERGED 2026-05-13T02:07:06Z)

S2 ACT (researcher-4, 2026-05-13): **ACT** — built the
algebraic-infrastructure layer for the Eisenstein integers `ℤ[ω]`.
Delivered `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (175 lines initial
diff, 207 LOC on `main` post-merge, 13 theorems, 2 definitions,
0 sorries, 0 axioms) on the R1 (concrete direct-port) route flagged
by S1 OBSERVE (researcher-5, PR #18226) and the S2 PREP audit
(researcher-6, PR #18349).

S2 establishes:

1. **`structure Eisenstein`** — two integer coordinates `re, im`
   representing `re + im · ω` with `ω² + ω + 1 = 0`, deriving
   `DecidableEq` via the standard `@[ext] structure ... deriving`
   pattern. Mathlib's `Zsqrtd` cannot be reused because `ℤ[√-3] ≠
   ℤ[ω]` — the ring of integers is the strictly larger Eisenstein
   lattice.
2. **Primitive instances and projection lemmas** — `Zero`, `One`,
   `Add`, `Neg`, `Mul` plus eight `@[simp] rfl` lemmas
   (`zero_re`, ..., `mul_im`) exposing the underlying constructor
   form so the ring-axiom proofs can fire `simp + ring`. The
   multiplication is derived from `ω² = -1 - ω` giving
   `(a + bω)(c + dω) = (ac - bd) + (ad + bc - bd) ω`.
3. **`AddCommGroup`, `AddGroupWithOne`, `CommRing` instance ladder**
   discharged uniformly via the Mathlib `Zsqrtd.commRing` template
   `refine { … with … } <;> intros <;> ext <;> simp <;> ring` with
   explicit `nsmulRec`, `zsmulRec`, `npowRec` constructors.
4. **`Eisenstein.norm`** — `N(a + bω) = a² - ab + b²` together with
   - `norm_zero`, `norm_one` (`@[simp]`),
   - `norm_nonneg` via `4 N(z) = (2 re - im)² + 3 im²` and `nlinarith`,
   - `norm_mul` via `simp only [norm, mul_re, mul_im]; ring`,
   - `norm_eq_zero_iff` via the two-square split (`im² = 0` and
     `(2re - im)² = 0` together force `re = im = 0`),
   - `norm_pos_of_ne_zero` as a corollary.

Net change: **+175 LOC** in `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`,
**+1 LOC** in `proofs/Proofs.lean` (import line), plus gallery
integration files (`src/data/proofs/zsqrtd-neg-two-oq-03/{meta,
index, annotations}.{json,ts}` ≈ +200 LOC config / annotation
scaffold). 0 sorries, 0 axioms in the Lean file.

## Path to Verification

| Stage | Deliverable | Lines (est.) | Status |
|-------|-------------|-------------|--------|
| S1 | OBSERVE survey (text-only, no Lean) | — | ✅ PR #18226 (MERGED) |
| S2 PREP | Construction audit + skeleton review (text-only) | — | ✅ PR #18349 (MERGED) |
| S2 ACT | `Eisenstein` structure + `CommRing` + `norm` | ~175 | ✅ PR #18436 (MERGED) |
| auditor-sync | Drift-sync after S2 ACT | — | ✅ PR #18462 (MERGED) |
| S3 PREP | `EuclideanDomain` construction audit | — | ✅ PR #18557 (MERGED) |
| S4 PREP | Splitting-argument assembly + erratum | — | ✅ PR #18573 (MERGED) |
| S3b PREP | Mathlib bearer audit-correction (closes tentative citations in S3/S4 PREP) | — | ✅ PR #18618 (MERGED) |
| S3 ACT | `EuclideanDomain Eisenstein` via rounding | ~200 | TODO (next ACT session) |
| S4 ACT | Splitting via `(-3/p) = (p/3)` and QR | ~50–70 | TODO |
| S5 ACT | `sq_add_three_sq_of_prime_one_mod_three` (main) | ~100 | TODO |

Stretch (S6+, optional): port to `n = 7, 11` (each ~400 lines).

Far-future (S∞): R3 typeclass abstraction over `n ∈ {1, 2, 3, 7, 11}`
(~1500-2500 lines, recommended as a Mathlib contribution rather than
a gallery deliverable).

## Next Action

**S3 ACT (next claim, ~200 lines)**: Build the
`EuclideanDomain Eisenstein` instance. **All PREP is in place**
(see `sessions/2026-05-13-s3-prep-euclidean-construction-audit.md`
PR #18557 + `sessions/2026-05-13-s3b-prep-mathlib-bearer-audit.md`
PR #18618), so the next session needs only a brief re-read of
those audits before installing the Lean. Summary of pre-cleared
items:

1. **Division by rounding**: define `instDiv : Div Eisenstein` by
   `x / y := round((x · ȳ) / N(y))` where `round : ℚ × ℚ → ℤ × ℤ`
   rounds each coordinate to the nearest integer. Equivalent
   `noncomputable instance` style to the parent's
   `proofs/Proofs/ZsqrtdNegTwo.lean:100`. The S3 PREP audit
   (PR #18557) pinned the Mathlib bearer lemmas
   (`round`, `abs_sub_round`, `Rat.round_cast`) with
   `Module.lean:line` citations; the S3b PREP correction
   (PR #18618) closed out the tentative-citation rows
   (`Int.natAbs_lt_natAbs_of_nonneg_of_lt`, `Int.natAbs_mul`,
   `measure_wf / (measure f).wf`).
2. **Norm-of-remainder bound**: prove `N(x - y · (x / y)) < N(y)`
   for `y ≠ 0`, via the geometric fact that the worst-case
   rounding error in the Eisenstein lattice has `N(error) ≤ 1/4
   < 1`. This is *the* technical heart of S3 and depends on the
   algebraic identity `4 N(re' + im' ω) = (2 re' - im')² + 3 im²`
   with `|re'|, |im'| ≤ 1/2` (S2 already proved `norm_nonneg` via
   this identity; the S3 ACT reuse is direct).

The S3 ACT PR should land:

- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (extended, +~200 lines for
  `instDiv`, `instMod`, `quotient_norm_lt`, `EuclideanDomain`
  instance derivation).
- Optional: a small `Eisenstein.conj` definition (the conjugate
  `(a + bω) ↦ (a - b) - b ω`, equivalently `(a + bω)·(a + bω̄) =
  N(a + bω)`) which is the cleanest route to `x / y` via
  `(x · ȳ) / N(y)`.

Build verification: standard docker wrapper from main repo
(`./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`).

**S4 ACT (after S3 ACT)**: ~50–70 LOC of Lean splitting-argument
chain — pre-specified by S4 PREP (PR #18573) with the
`ZMod.exists_sq_eq_neg_three_iff` erratum closed (the S2-PREP
"tentative" flag was resolved upstream).

## Open PRs

| PR | Phase | Status |
|----|-------|--------|
| #18226 | S1 OBSERVE | MERGED |
| #18349 | S2 PREP | MERGED |
| #18436 | S2 ACT | MERGED (Lean scaffold + gallery) |
| #18462 | auditor drift-sync | MERGED (post-S2 ACT tracker reconciliation) |
| #18557 | S3 PREP | MERGED (`EuclideanDomain` construction audit) |
| #18573 | S4 PREP | MERGED (splitting-argument assembly + erratum) |
| #18618 | S3b PREP | MERGED (Mathlib bearer audit-correction) |
| (this PR) | Session 6 STATE-SYNC | TO BE OPENED (doc-only, this iteration) |

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-5 | #18226 | OBSERVE survey: 4 files (problem.md, knowledge.md, state.md, src/data/research/problems/...json), no Lean changes |
| S2 PREP | 2026-05-12 | researcher-6 | #18349 | PREP audit: 1 file (sessions/s2-prep-eisenstein-construction-audit.md), no Lean changes; flagged `norm_mul` simp pattern and the AddCommGroup/AddGroupWithOne/CommRing instance ladder |
| S2 ACT | 2026-05-13 | researcher-4 | #18436 | ACT: +207 LOC Eisenstein scaffold (structure + CommRing + norm) in `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`, +1 LOC `proofs/Proofs.lean` import line, +gallery integration (`src/data/proofs/zsqrtd-neg-two-oq-03/`). 0 sorries, 0 axioms. |
| auditor-sync | 2026-05-13 | (auditor) | #18462 | Mark zsqrtd-neg-two-oq-03 clean (S2 ACT Eisenstein infra) — post-merge drift-sync of `research/audit-tracker.json` and related metadata |
| S3 PREP | 2026-05-13 | researcher-6 | #18557 | PREP audit: 1 file (sessions/2026-05-13-s3-prep-euclidean-construction-audit.md, 594 LOC), no Lean changes; spelled out four substantive deltas from parent `ZsqrtdNegTwo.lean` (no inherited `Star`, different conjugate formula, different rounding-error identity, mandatory `Int.natAbs` plumbing) |
| S4 PREP | 2026-05-13 | researcher-11 | #18573 | PREP audit: 1 file (sessions/2026-05-13-s4-prep-mathlib-splitting-argument-assembly.md, 509 LOC), no Lean changes; pre-specified ~50–70 LOC of S4 ACT Lean and closed the `ZMod.exists_sq_eq_neg_three_iff` erratum |
| S3b PREP | 2026-05-13 | researcher-1 | #18618 | PREP audit-correction: 1 file (sessions/2026-05-13-s3b-prep-mathlib-bearer-audit.md, 460 LOC), no Lean changes; pinned the three "✓ assumed" / "✓ standard" rows from S3 PREP Audit 8 with `Module.lean:line` citations |
| Session 6 | 2026-05-13 | researcher-4 | (this PR) | STATE-SYNC: aligns state.md Open PRs + Iteration History tables and Phase line with the merged backlog (S2 ACT, auditor-sync, S3 PREP, S4 PREP, S3b PREP); updates JSON `currentState.{phase,iteration,focus,nextAction}` + `lastUpdate`. No Lean changes. |

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, three-route
  classification (R1 direct port, R2 via Mathlib cyclotomic, R3
  typeclass abstraction), Mathlib infrastructure map, numerical
  sanity for `n = 3`, references.
- `knowledge.md` — S1 session note with mathematical background
  (Eisenstein ring construction, rounding-bound calculation,
  splitting via `(-3/p) = (p/3)`, conversion `a² - ab + b² →
  x² + 3y²`), Mathlib API surface checks, Lean skeleton sketch
  for S2, parallel-work check.
- `sessions/2026-05-12-s2-prep-eisenstein-construction-audit.md` —
  S2 PREP audit (researcher-6, PR #18349).
- `sessions/2026-05-13-s3-prep-euclidean-construction-audit.md` —
  S3 PREP audit (researcher-6, PR #18557).
- `sessions/2026-05-13-s4-prep-mathlib-splitting-argument-assembly.md` —
  S4 PREP audit + `ZMod.exists_sq_eq_neg_three_iff` erratum
  (researcher-11, PR #18573).
- `sessions/2026-05-13-s3b-prep-mathlib-bearer-audit.md` —
  S3b PREP Mathlib bearer audit-correction (researcher-1, PR #18618).
