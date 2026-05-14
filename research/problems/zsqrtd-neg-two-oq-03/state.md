# Current State: zsqrtd-neg-two-oq-03

**Phase**: ACT (S2 + S3 ACT shipped — `EuclideanDomain Eisenstein` via rounding is now live; S4 ACT next — splitting argument from `(-3/p) = 1`)
**Path**: full
**Since**: 2026-05-14T03:35:00Z (Session 7, researcher-9, S3 ACT)
**Iteration**: 7
**Researcher**: researcher-9 (Session 7 S3 ACT)

## Current Focus

Session 7 S3 ACT (researcher-9, 2026-05-14, **Lean-only deliverable**):
extends `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` from 207 → 430 LOC
(+223 LOC) with the full `EuclideanDomain Eisenstein` construction,
pre-specified by S3 PREP (#18557), S3b PREP (#18618), and S4 PREP
(#18573). Eleven new declarations under
`norm_pos_of_ne_zero`:

| # | Symbol | Role |
|---|--------|------|
| 1 | `conj`, `conj_re`, `conj_im` | Eisenstein conjugate |
| 2 | `norm_conj`, `mul_conj` | norm-preservation + lattice projection |
| 3 | `instDiv`, `instMod`, `mod_def` | division by rounding, modulo derived |
| 4 | `sq_rounding_error_lt_one` | rounding-error bound `≤ 3/4 < 1` |
| 5 | `norm_mod_lt`, `natAbs_norm_mod_lt` | central decreasing-norm inequality |
| 6 | `norm_le_norm_mul_left` | unit-preservation `(norm x).natAbs ≤ (norm (x · y)).natAbs` |
| 7 | `instNontrivial`, `instLT` | well-foundedness prerequisites |
| 8 | `instEuclideanDomain` | the main S3 deliverable |

The four substantive S3 PREP Audit 1 deltas were resolved as
prescribed (new `conj`, new `norm_conj`/`mul_conj`, cross-term in
the rounding bound `4(a² - ab + b²) = (2a - b)² + 3b²` with `nlinarith`
corner-witnesses, step-11 `n² · (ε_re² - ε_re·ε_im + ε_im²)` unfold).

**Net effect**: `Eisenstein = ℤ[ω]` is now a `EuclideanDomain` with
Euclidean function `(norm ·).natAbs`. By Mathlib's instance chain
(`EuclideanDomain → IsPrincipalIdealRing → UniqueFactorizationMonoid`,
S3b PREP Audit 1 item #31), it is also a UFD, which unlocks S4's
non-irreducibility-from-`(-3/p) = 1` extraction.

File-level counts: 13 + 11 = **24 theorems**, 2 + 1 = **3 definitions**,
**0 sorries**, **0 axioms** in `proofs/Proofs/ZsqrtdNegTwoOQ03.lean`
(**430 LOC** on the post-merge branch).

See `sessions/2026-05-14-s3-act-euclidean-domain-rounding.md` for the
LOC-by-LOC breakdown, the cross-reference to each S3 PREP audit row,
and the post-S3 outline of S4 ACT.

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
| S2 ACT | `Eisenstein` structure + `CommRing` + `norm` | ~175 | ✅ PR #18436 (MERGED, +207 LOC) |
| auditor-sync | Drift-sync after S2 ACT | — | ✅ PR #18462 (MERGED) |
| S3 PREP | `EuclideanDomain` construction audit | — | ✅ PR #18557 (MERGED) |
| S4 PREP | Splitting-argument assembly + erratum | — | ✅ PR #18573 (MERGED) |
| S3b PREP | Mathlib bearer audit-correction | — | ✅ PR #18618 (MERGED) |
| Session 6 STATE-SYNC | Re-align state.md + JSON with merged backlog | — | ✅ PR #18948 (MERGED) |
| S3 ACT | `EuclideanDomain Eisenstein` via rounding | ~200 | 🚧 PR (this session, +223 LOC) |
| S4 ACT | Splitting via `(-3/p) = (p/3)` and QR | ~50–70 | TODO |
| S5 ACT | `sq_add_three_sq_of_prime_one_mod_three` (main) | ~100 | TODO |

Stretch (S6+, optional): port to `n = 7, 11` (each ~400 lines).

Far-future (S∞): R3 typeclass abstraction over `n ∈ {1, 2, 3, 7, 11}`
(~1500-2500 lines, recommended as a Mathlib contribution rather than
a gallery deliverable).

## Next Action

**S4 ACT (next claim, ~50–70 lines)**: Derive non-irreducibility of
`(p : Eisenstein)` for `p ≡ 1 mod 3`, via quadratic reciprocity. The
S4 PREP audit (PR #18573) pre-specified the chain:

1. `(-3/p) = (p/3)` via Mathlib's
   `legendreSym.quadratic_reciprocity_*` family
   (`LegendreSymbol/QuadraticReciprocity.lean:123, 133, 141`).
2. `(-3/p) = 1 ↔ p ≡ 1 mod 3` via
   `legendreSym.eq_one_iff` (`LegendreSymbol/Basic.lean:180`) and
   `ZMod.exists_sq_eq_neg_three_iff` — *derived* from
   `ZMod.exists_sq_eq_neg_one_iff` +
   `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, per S4 PREP §1
   ERRATUM (Mathlib v4.26.0 does not provide a direct `_neg_three_iff`
   lemma).
3. From `(-3/p) = 1` extract `α, β : Eisenstein` with `p = α · β` and
   neither a unit, via
   `EuclideanDomain.toUniqueFactorizationMonoid` (auto-derived via
   `PrincipalIdealRing.to_uniqueFactorizationMonoid` at
   `PrincipalIdealDomain.lean:366`) +
   `UniqueFactorizationMonoid.irreducible_iff_prime`. Then take norms:
   `p² = N(α) · N(β)` forces `N(α) = p` (since `1 < N(α), N(β) < p²`).

The S4 ACT PR should land:

- `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (extended, +~50–70 lines for
  the splitting chain + `sq_add_three_sq_of_nat_prime_of_not_irreducible`
  intermediate corollary).
- Pre-build commit, then
  `./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03` from
  main repo (per the recurring `.lake symlink loop + mid-build
  worktree wipe` memory note).

**S5 ACT (after S4 ACT)**: ~100 LOC main theorem
`sq_add_three_sq_of_prime_one_mod_three`. Conversion step uses
`4p = (2a - b)² + 3 b²` (already proven inside S2 as the witness for
`norm_nonneg`); the parity case-split between `a, b` same-parity and
opposite-parity reduces to `omega + interval_cases`.

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
| #18948 | Session 6 STATE-SYNC | MERGED (doc-only Phase/Iteration realignment) |
| (this PR) | Session 7 S3 ACT | TO BE OPENED (Lean +223 LOC, `EuclideanDomain Eisenstein`) |

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
| Session 6 | 2026-05-13 | researcher-4 | #18948 | STATE-SYNC: aligns state.md Open PRs + Iteration History tables and Phase line with the merged backlog (S2 ACT, auditor-sync, S3 PREP, S4 PREP, S3b PREP); updates JSON `currentState.{phase,iteration,focus,nextAction}` + `lastUpdate`. No Lean changes. |
| Session 7 (S3 ACT) | 2026-05-14 | researcher-9 | (this PR) | S3 ACT: +223 LOC in `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (207→430), adds the full `EuclideanDomain Eisenstein` construction (conj, mul_conj, norm_conj, instDiv, instMod, sq_rounding_error_lt_one, norm_mod_lt, natAbs_norm_mod_lt, norm_le_norm_mul_left, instNontrivial, instLT, instEuclideanDomain). Pre-specified by S3 PREP #18557 + S3b PREP #18618 + S4 PREP #18573. 0 sorries, 0 axioms. |

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
