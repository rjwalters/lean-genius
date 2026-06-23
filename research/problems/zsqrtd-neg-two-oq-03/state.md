# Current State: zsqrtd-neg-two-oq-03

**Phase**: ACT (S16 PREP shipped — Step 3 paste-ready Lean skeleton + 7-bearer audit; **doc-only**; remaining Step 3 ACT)
**Path**: full
**Since**: 2026-06-01 (S15 ACT — Step 2 discharge; was S14 PREP 2026-06-01T00:00Z)
**Iteration**: 15 (S15 ACT was iter 14; this S16 PREP is iter 15 doc-only)
**Researcher**: researcher-1 (Session 16 PREP, 2026-06-02)

## S16 PREP (researcher-1, 2026-06-02, doc-only)

Refines S14 PREP §6 prose (Step 3 outline) into a paste-ready Lean
skeleton. Pins 7 Mathlib bearers for the Step 3 UFD non-irreducibility
chain at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged from S15 ACT). Makes the parity-canonicalization helper
(`exists_odd_sq_eq_neg_three_int`, ~6 LOC) explicit, and surfaces the
R4 size-bound subtlety that S14 §6 hand-waved.

**Paste-ready ~45 LOC main + ~6 LOC helper** for the target lemma
`sq_add_three_sq_of_nat_prime_of_not_irreducible (p : ℕ) [Fact p.Prime]
(hp_ne_two : p ≠ 2) (hp_ne_three : p ≠ 3) (hp_mod_3 : p % 3 = 1) :
∃ α : Eisenstein, Eisenstein.norm α = (p : ℤ)`. Three sub-sorries
scoped for the next ACT picker (3 LOC + 3 LOC + 10 LOC).

**Bearer table (all @ pinned SHA, §3 of session log)**:
- `legendreSym.eq_one_iff` `LegendreSymbol/Basic.lean:178`
- `ZMod.intCast_zmod_cast` `Data/ZMod/Basic.lean:215` (`@[norm_cast]`)
- `PrincipalIdealRing.to_uniqueFactorizationMonoid` `PrincipalIdealDomain.lean:345` (instance)
- `UniqueFactorizationMonoid.irreducible_iff_prime` `UniqueFactorizationDomain/Defs.lean:132`
- `EuclideanDomain.toPrincipalIdealDomain` (typeclass instance, auto)
- `Int.emod_emod_of_dvd` `Mathlib/Data/Int/Defs.lean`
- `Int.dvd_iff_emod_eq_zero` `Mathlib/Data/Int/GCD.lean`

**ACT-readiness gate**: 7/8 GREEN + 1/8 AMBER (Docker sibling-container
risk; S15 ACT shipped on same image yesterday so corruption is intermittent).
**File state**: 559 LOC unchanged (md5 `eb66b1ebb766b7459bbd8e18af41a61d`);
0 sorries, 0 axioms. **No Lean edits, no Docker build, no meta.json edits.**

Session log:
`sessions/2026-06-02-s16-prep-step3-bearer-audit-and-paste-ready-skeleton.md`.

## S15 ACT (researcher-1, 2026-06-01, Docker-verified)

Discharged S4 ACT Step 2 (`legendreSym_neg_three_eq_one_iff`) per the S14
PREP §5 paste-ready skeleton, plus the supporting helper
`legendreSym_three_eq_one_iff_p_mod_three_eq_one` and 2 hoisted decide
helpers needed to dodge "free variable" errors from `decide` inside the
namespace.

**Patch**:

1. **Helper `legendreSym_three_eq_one_iff_p_mod_three_eq_one`** (~28 LOC):
   reduces `(p/3) = 1 ↔ p % 3 = 1` for `p ≠ 3`. Uses `legendreSym.eq_one_iff'`
   + `ZMod.natCast_mod` + case split on `p % 3 ∈ {1, 2}`.
2. **Helper `legendreSym_neg_three_eq_one_iff`** (~30 LOC, S4 ACT Step 2):
   uses Step 1 (`legendreSym_neg_three`) + `legendreSym.at_neg_one` + case
   split on `p % 4 ∈ {1, 3}` with `ZMod.χ₄_nat_*_mod_four` +
   `legendreSym.quadratic_reciprocity_*_mod_four`. The `(3 : ℤ)` vs
   `((3 : ℕ) : ℤ)` coercion mismatch from QR's RHS is bridged by an
   `h3cast` shim.
3. **Hoisted helpers** (~10 LOC, outside `namespace Proofs`):
   `two_ne_zero_zmod_three : (2 : ZMod 3) ≠ 0` and
   `not_isSquare_two_zmod_three : ¬ IsSquare (2 : ZMod 3)`. In-namespace
   `by decide` was failing with "Expected type must not contain free
   variables"; hoisting to file-top resolved it.

**Build iteration log** (4 Docker iters):

| Iter | Issue | Fix |
|------|-------|-----|
| 1 | `χ₄_*_one_mod_four` unknown identifier | Namespace prefix `ZMod.` |
| 2 | `decide` failed "free variables" on `∀ x : ZMod 3, x * x ≠ 2` | Hoisted helper outside namespace |
| 3 | QR arg-order swap + `(3 : ℤ)` vs `((3 : ℕ) : ℤ)` coercion | Swapped + added `h3cast` shim |
| 4 | Type mismatch False vs `p % 3 = 1` | `.elim` on the contradiction |
| ✓ | — | All 3058 jobs succeed |

**File metrics**:

| Metric | Pre-S15 | Post-S15 | Δ |
|--------|---------|----------|---|
| LOC | 465 | 559 | +94 |
| sorries | 0 | 0 | 0 |
| axioms | 0 | 0 | 0 |
| theorems (grep count) | ~32 (drift, acknowledged S14 PREP §7) | 36 | +4 |

**Build**: **VERIFIED via Docker — 3058 jobs successful, single-file
target `Proofs.ZsqrtdNegTwoOQ03`, 0 errors, 11s incremental.**

**Bearer 0-drift**: lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
unchanged. All S14 PREP §4 bearers (`legendreSym.at_neg_one`,
`ZMod.χ₄_nat_*_mod_four`, `legendreSym.quadratic_reciprocity_*_mod_four`,
`legendreSym.eq_one_iff'`, `ZMod.natCast_mod`) verified at the pinned SHA
locations.

**Gallery `meta.json` updates**:
- `meta.lineCount` 465 → 559 (mirrors PR #21522 convention)
- `meta.theoremCount` 24 → 36 (also closes the S14 PREP §7 drift)
- `leanFile.lineCount` / `leanFile.theoremCount` mirror

**Sibling-coordination**: no open PRs on this slug at S15 ACT push time.

See `sessions/2026-06-01-s15-act-step2-discharge-legendresym-neg-three-iff.md`
for the full memo.

## Current Focus

Session 11 STATE-SYNC (researcher-3, 2026-05-16, **doc-only**): catches up
the 3-PR merge wave from 2026-05-15 — **PR #19008** (S3 ACT, Lean +219 LOC,
3058 Docker jobs clean, merged 23:28:55Z), **PR #19186** (S8 PREP — PR
coordination + stranded-branch follow-up + S4 PREP line-erratum, doc-only,
merged 22:56:14Z), and **PR #19189** (S4 PREP r2 — post-#19008 line-shift
refresh + Mathlib SHA re-pin, doc-only, merged 22:56:04Z). Bumps state.md
iteration counter 7 → 10, refreshes the Lean inventory block, retires the
"(this PR) | Session 7 S3 ACT | TO BE OPENED" row from Open PRs, marks
the S3 ACT row in Path to Verification as ✅, appends 3 new rows to
Iteration History, and updates `Next Action` to include the S4 PREP r2
erratum (`legendreSym.at_neg` does not exist in Mathlib v4.26.0 — use
`legendreSym.mul` + `at_neg_one` decomposition instead) and the stranded-
branch absorption decision (whether to integrate the 2 extra `@[simp]`
`mul_conj_re`/`mul_conj_im` lemmas).

### On-disk reality (current `origin/main`, 2026-05-16)

| File | LOC | Theorems | `def` | `instance` | Sorries | Axioms |
|------|-----|----------|-------|------------|---------|--------|
| `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` | **426** | **29** | **2** | **12** (7 plain + 5 `noncomputable`) | **0** | **0** |

(Counts via `grep -cE "^(theorem\|lemma\|protected (theorem\|lemma)\|@\[simp\] (theorem\|lemma))"`,
`grep -cE "^(noncomputable )?(def\|instance)"`, `grep -c sorry`,
`grep -c "^axiom "` against the post-#19008 main file.)

Drift vs. the iter-7 state.md head block (which framed Session 7 as
"this PR" with "207 → 430 LOC, +223 LOC, 24 theorems, 3 definitions"):

* LOC: 430 (state.md projection) → **426** on disk (-4 LOC, minor finalisation drift).
* Theorems: 24 (state.md) → **29** on disk (+5; review-time additions of `@[simp] sub_re`/`sub_im` plus the conj projection lemmas).
* `def`: 3 (state.md) → **2** on disk (-1; `norm` is a `def`, `ofInt` is a `def`; the third "definition" in state.md's tally was an instance counted under the def label).
* Sorries: 0 / Axioms: 0 — unchanged.

### Historical Focus (Session 7 S3 ACT, PR #19008, MERGED 2026-05-15T23:28:55Z)

Session 7 S3 ACT (researcher-9, author-time 2026-05-14): extends
`proofs/Proofs/ZsqrtdNegTwoOQ03.lean` from 207 → 426 LOC (+219 LOC
post-review) with the full `EuclideanDomain Eisenstein` construction,
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
| S3 ACT | `EuclideanDomain Eisenstein` via rounding | +219 LOC | ✅ PR #19008 (MERGED 2026-05-15T23:28:55Z, 3058 Docker jobs clean) |
| S8 PREP | PR coord audit + stranded-branch follow-up + S4 PREP line-erratum | — | ✅ PR #19186 (MERGED 2026-05-15T22:56:14Z, doc-only) |
| S4 PREP r2 | Post-#19008 line-shift refresh + Mathlib SHA re-pin | — | ✅ PR #19189 (MERGED 2026-05-15T22:56:04Z, doc-only) |
| Session 11 STATE-SYNC | Catch up 3-PR merge wave | — | ✅ PR #19494 (MERGED 2026-05-16, doc-only) |
| Session 12 PREP | JSON drift fix + bearer re-spot-check + S4 ACT paste-ready | — | ✅ PR #19600 (MERGED 2026-05-16, doc-only) |
| S4 ACT Step 1 | `legendreSym_neg_three` + 2 stranded `@[simp]` projection lemmas (`mul_conj_re`, `mul_conj_im`) | +39 LOC | ✅ PR #21226 (MERGED 2026-05-30) |
| mechanic lineCount sync | Gallery `meta.json` `lineCount` 426→465 | — | ✅ PR #21522 (MERGED 2026-05-31, gallery-meta) |
| Session 14 PREP | Step 2 derivation tableau + state-sync (this PR) | — | 🚧 PR (this session, doc-only) |
| S4 ACT Step 2 | `legendreSym_neg_three_eq_one_iff (p ≠ 2) (p ≠ 3) : (-3/p) = 1 ↔ p % 3 = 1`; paste S14 PREP §5 skeleton | ~50 | TODO (`χ₄_nat_one_mod_four` ZModChar.lean:L89; `χ₄_nat_three_mod_four` ZModChar.lean:L94; `legendreSym.at_neg_one` Basic.lean:L272; `quadratic_reciprocity_one_mod_four` QR.lean:L134; `quadratic_reciprocity_three_mod_four` QR.lean:L142; 2 `decide`-able sub-sorries on `legendreSym 3 p = 1 ↔ p % 3 = 1`) |
| S4 ACT Step 3 | Extract `α : Eisenstein` with `norm α = p` from `IsSquare (-3 : ZMod p)`; parity case-split on `x_int` | ~30 | TODO (per S14 PREP §6; `legendreSym.eq_one_iff` Basic.lean:L178 + `PrincipalIdealRing.to_uniqueFactorizationMonoid` PID.lean:L345 + `irreducible_iff_prime`) |
| S5 ACT | `sq_add_three_sq_of_prime_one_mod_three` (main) | ~100 | TODO |

Stretch (S6+, optional): port to `n = 7, 11` (each ~400 lines).

Far-future (S∞): R3 typeclass abstraction over `n ∈ {1, 2, 3, 7, 11}`
(~1500-2500 lines, recommended as a Mathlib contribution rather than
a gallery deliverable).

## Next Action

**S17+ ACT — Step 3 (~51 LOC, paste-ready)**: Apply the
**S16 PREP §5** paste-ready Lean skeleton (`sq_add_three_sq_of_nat_prime_of_not_irreducible`,
+ helper `exists_odd_sq_eq_neg_three_int` from §4) to
`proofs/Proofs/ZsqrtdNegTwoOQ03.lean` after the existing
`legendreSym_neg_three_eq_one_iff` (line 558). Discharge the three
sub-sorries scoped in S16 PREP §5:

1. `hne0` (~3 LOC): `((-3 : ℤ) : ZMod p) ≠ 0` ⇐ `p ≠ 3` via `ZMod.natCast_self_eq_zero_iff`.
2. `hp_coprime_4` (~3 LOC): `Nat.Coprime p 4` for odd prime via `interval_cases` + `Nat.Prime.gcd_eq_iff`.
3. Size-bound finisher (~10 LOC): force `norm α = p` from `p ∣ norm α`
   + `0 < norm α` + `norm α < p²` (via `|y| ≤ (p-1)/2`).

7 Mathlib bearers pinned at SHA `2df2f0150c…` (S16 PREP §3). Risk
classes R1–R4 inventoried (S16 PREP §6). Build-verify via
`./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03` (re-check
sibling Docker container `lean-build-57602` first; S15 ACT succeeded
on the same image yesterday).

**Historical S4 ACT plan (now superseded by S16 PREP §5 skeleton)**:
Derive non-irreducibility of `(p : Eisenstein)` for `p ≡ 1 mod 3`,
via quadratic reciprocity. The S4 PREP audit (PR #18573)
pre-specified the chain — **with the S4 PREP r2 erratum (PR #19189)
line-shifted and the fictitious `legendreSym.at_neg` symbol removed**:

1. `(-3/p) = (p/3)` via Mathlib's
   `legendreSym.quadratic_reciprocity_*` family
   (`LegendreSymbol/QuadraticReciprocity.lean:123, 133, 141` per S4 PREP §2.1;
   **PR #19189 §1 confirms file SHA `d552964d25f71d13ca515b3fc90d62c35cb500c2` at
   Mathlib v4.26.0 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**).
   Decomposition follows `legendreSym.mul` + `at_neg_one` (NOT the
   fictitious `at_neg` flagged by S4 PREP r2 erratum).
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

**Stranded-branch absorption decision (open from S8 PREP §1)**: PR
#19186 §1 identified a stranded branch
`origin/research/zsqrtd-neg-two-oq03-s3-act-1778799640` (commit
`af4b879f30e`, never opened as a PR) that contains the same algebraic
content as PR #19008 plus 2 extra `@[simp]` projection lemmas
(`mul_conj_re`, `mul_conj_im`). Recommended deferred-pencilwork: next
ACT-touching iteration can pick these 2 lemmas up as part of S4 ACT
(or as a tiny standalone PREP). Conflict-free with PR #19008 as
`@[simp]` projection lemmas on `mul_conj` (which exists at line 238 of
the current file).

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
| #19008 | Session 7 S3 ACT | MERGED 2026-05-15T23:28:55Z (Lean +219 LOC, `EuclideanDomain Eisenstein`, 3058 Docker jobs clean) |
| #19186 | Session 8 PREP — coord + stranded follow-up + S4 PREP line-erratum | MERGED 2026-05-15T22:56:14Z (doc-only) |
| #19189 | Session 8 S4 PREP r2 — post-#19008 line-shift refresh + Mathlib SHA re-pin | MERGED 2026-05-15T22:56:04Z (doc-only) |
| #19494 | Session 11 STATE-SYNC — catch up 3-PR merge wave | MERGED 2026-05-16 (doc-only) |
| #19600 | Session 12 PREP — JSON drift fix + bearer re-spot-check + S4 ACT paste-ready | MERGED 2026-05-16 (doc-only) |
| #21226 | Session 13 S4 ACT incremental — Step 1 `legendreSym_neg_three` + 2 stranded `@[simp]` lemmas | MERGED 2026-05-30 (Lean +39 LOC, 426→465 LOC, 29→32 theorems, 0 sorries, 0 axioms) |
| #21522 | mechanic lineCount mirror 426→465 | MERGED 2026-05-31 (gallery-meta) |
| (this PR) | Session 14 PREP — Step 2 derivation tableau + state-sync (doc-only) | TO BE OPENED |

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
| Session 7 (S3 ACT) | 2026-05-14 author / 2026-05-15 merged | researcher-9 | #19008 | S3 ACT: +219 LOC in `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (207→426 on disk; state.md had projected 430), adds the full `EuclideanDomain Eisenstein` construction (conj, mul_conj, norm_conj, instDiv, instMod, sq_rounding_error_lt_one, norm_mod_lt, natAbs_norm_mod_lt, norm_le_norm_mul_left, instNontrivial, instLT, instEuclideanDomain). Pre-specified by S3 PREP #18557 + S3b PREP #18618 + S4 PREP #18573. 3058 Docker jobs clean. 0 sorries, 0 axioms. |
| Session 8 PREP | 2026-05-15 author / 2026-05-15 merged | researcher-1 | #19186 | S8 PREP coordination audit: 1 file (sessions/2026-05-14-s8-prep-coordination-and-stranded-followup.md, 223 LOC), no Lean changes. Flagged PR #19008 as mergeable-but-stalled (would later merge ~32 min later in the same drain wave) and identified the stranded branch `origin/research/zsqrtd-neg-two-oq03-s3-act-1778799640` (commit `af4b879f30e`) carrying 2 extra `@[simp]` projection lemmas (`mul_conj_re`, `mul_conj_im`). |
| Session 8 S4 PREP r2 | 2026-05-15 author / 2026-05-15 merged | researcher-11 | #19189 | S4 PREP r2: 1 file (sessions/2026-05-14-s4-prep-r2-post-s3act-line-shift-refresh.md, 364 LOC), no Lean changes. Refreshed S4 PREP §2 line tables for post-#19008 line shifts; re-pinned Mathlib bearer SHAs against pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; surfaced the **S4 PREP §2.1 erratum**: `legendreSym.at_neg` does NOT exist in Mathlib v4.26.0 — only `at_neg_one`/`at_neg_two` exist. Operational impact zero (S4 PREP §3 sketch already decomposes via `legendreSym.mul` + `at_neg_one`). |
| Session 11 STATE-SYNC | 2026-05-16 | researcher-3 | #19494 | STATE-SYNC: catches up the 3-PR merge wave (#19008 + #19186 + #19189), bumps iteration counter 7 → 10, refreshes Lean inventory block (29 theorems / 2 defs / 12 instances / 0 sorries / 0 axioms / 426 LOC; note: on-disk `definitionCount` is `3` not `2`, see S12 PREP §10), reaffirms 3 Mathlib bearer SHAs at the v4.26.0 pin, retires "(this PR) | Session 7 S3 ACT | TO BE OPENED" row, updates Path to Verification + Open PRs + Iteration History tables, propagates S4 PREP r2 erratum into Next Action, and records the stranded-branch absorption decision (deferred pencilwork for next ACT-touching iter). 0 Lean / knowledge.md / problem.md / JSON edits. |
| Session 12 PREP | 2026-05-16 | researcher-9 | #19600 | PREP: 1 NEW session memo (`sessions/2026-05-16-s12-prep-json-drift-fix-bearer-respotcheck-s4-act-paste-ready.md`, ~450 LOC), state.md head + Open PRs + Path-to-Verification + Iteration History edits (~±60 LOC), and JSON `currentState.{phase,since,iteration,focus,nextAction,lastUpdate}` + `leanFiles[0].theoremCount` + top-level `lastUpdate` updates (~±10 LOC). Closes JSON drift left by S11 STATE-SYNC (#19494), re-spot-checks 4-file bearer table at HEAD `ecb47b35601` against Mathlib pin `2df2f0150c…` (IDENTICAL), surfaces 4 NEW line-citation drift findings (QR `quadratic_reciprocity` L107 not L123; QR `_one_mod_four` L134 not L133; PID `to_uniqueFactorizationMonoid` L345 not L366; Basic `eq_one_iff` L178 not L180), and lands a paste-ready ~60-LOC S4 ACT skeleton with 1 acknowledged sorry on `exists_sq_eq_neg_three_iff` (R3, ~15 LOC). Reaffirms stranded-branch absorption (#19186 §1 — 2 `@[simp]` lemmas folded into S4 ACT). Docker B1 INFRA blocker noted (daemon hung under host disk pressure). 0 Lean / 0 meta.json / 0 problem.md / 0 knowledge.md edits. |
| Session 13 S4 ACT incremental | 2026-05-30 | researcher-1 | #21226 | ACT: 3 declarations to `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` (426→465 LOC, +39 LOC). (1) `@[simp] mul_conj_re : (z * conj z).re = norm z` and (2) `@[simp] mul_conj_im : (z * conj z).im = 0` — stranded-branch `@[simp]` projection lemmas absorbed per S8 PREP §1 + S12 PREP §6 (each one-line `rw [mul_conj]`). (3) `legendreSym_neg_three (p : ℕ) [Fact p.Prime] : legendreSym p (-3) = legendreSym p (-1) * legendreSym p 3` — Step 1 of the S4 splitting argument (3-LOC body via `rw [show ((-3 : ℤ) = (-1) * 3) by norm_num, legendreSym.mul]`). Net delta: +3 theorems (29→32), 0 new sorries, 0 new axioms. Build-verified per PR description. |
| mechanic lineCount sync | 2026-05-31 | (mechanic) | #21522 | Gallery `meta.json` `lineCount` mirror 426→465 (1-character mechanic fix matching PR #21226's on-disk delta). Note: `theoremCount` 24→32 mirror still pending (S14 PREP §7 records the drift; future-mechanic pickup, NOT in S14 PREP scope). |
| Session 14 PREP | 2026-06-01 | researcher-1 | (this PR) | PREP: 1 NEW session memo (`sessions/2026-06-01-s14-prep-step2-derivation-tableau-state-sync.md`, ~350 LOC), state.md state-sync (~±50 LOC catching up #21226/#21522 + adding S4 ACT Step 2 + Step 3 rows to Path to Verification), and slug JSON `currentState.{phase,since,iteration,focus,nextAction,lastUpdate}` + top-level `lastUpdate` (~±15 LOC). Closes state.md drift left by 3-PR gap (#19600 + #21226 + #21522 unrecorded in state.md head). Re-confirms Mathlib pin `2df2f0150c…` at current HEAD `8bf8a7b3552`. Re-spot-checks bearer table at `~/GitHub/mathlib4@2df2f0150c…` — all S12 PREP §4 citations confirmed correct; adds 6 new rows for the χ₄ family (ZModChar.lean L89/L94/L99/L104), `ZMod.exists_sq_eq_neg_one_iff` (Basic.lean L279), and the QR helper `exists_sq_eq_neg_two_iff` (parent-template hook, QR.lean L80). Lands a fully tableau'd Step 2 derivation: 4-cell `p mod 12` case-split showing `(-3/p) = 1 ↔ p % 3 = 1` (S14 PREP §4) — the `p mod 4` dependence cancels between `(-1/p)` and `(3/p)` because QR for `3` (with `3 % 4 = 3`) introduces the matching sign flip. Paste-ready ~50-LOC Lean skeleton with risk class R1–R4 inventory (§5) factoring out the sub-lemma `legendreSym_three_eq_one_iff_p_mod_three_eq_one`. Step 3 outline refreshed (~30 LOC, parity case-split on `x_int` via the `x_int² + 3 = 4(y² + y + 1)` for `x_int = 2y + 1` route, §6). 8-item ACT-readiness gate all GREEN (§8). 0 Lean / 0 gallery meta.json / 0 problem.md / 0 knowledge.md edits; acknowledges gallery meta.json `theoremCount` 24→32 drift as mechanic-pickup. |

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
- `sessions/2026-05-14-s8-prep-coordination-and-stranded-followup.md` —
  S8 PREP coordination audit (researcher-1, PR #19186).
- `sessions/2026-05-14-s4-prep-r2-post-s3act-line-shift-refresh.md` —
  S4 PREP r2 post-#19008 refresh + erratum (researcher-11, PR #19189).
- `sessions/2026-05-14-s3-act-euclidean-domain-rounding.md` —
  S3 ACT EuclideanDomain construction (researcher-9, PR #19008).
- `sessions/2026-05-16-s11-state-sync-post-19008-19186-19189-merge-wave.md` —
  Session 11 STATE-SYNC post-drain catch-up (researcher-3, PR #19494).
- `sessions/2026-05-16-s12-prep-json-drift-fix-bearer-respotcheck-s4-act-paste-ready.md` —
  Session 12 PREP (researcher-9, PR #19600): JSON drift fix +
  4-file bearer re-spot-check + S4 ACT paste-ready ~60-LOC skeleton
  with 1 acknowledged sorry + 4 NEW line-citation drift findings +
  Docker B1 blocker note + 8-item ACT-readiness gate (7 GREEN + 1
  RED-INFRA).
- `sessions/2026-06-01-s14-prep-step2-derivation-tableau-state-sync.md` —
  **Session 14 PREP** (this PR; researcher-1): state-sync post-#21226/#21522
  + bearer table refresh (all S12 PREP citations confirmed at pin
  `2df2f0150c…`; +6 χ₄ family rows) + fully tableau'd Step 2 derivation
  (4-cell `p mod 12` case-split showing `(-3/p) = 1 ↔ p % 3 = 1`,
  `p mod 4` dependence cancels via matching QR sign flip) + ~50-LOC
  paste-ready Lean skeleton (R1–R4 inventory, 2 `decide`-able sub-sorries
  factored into `legendreSym_three_eq_one_iff_p_mod_three_eq_one`)
  + Step 3 outline refresh (~30 LOC, parity case-split on `x_int`
  via `x_int² + 3 = 4(y² + y + 1)` for odd `x_int`) + 8-item
  ACT-readiness gate (8/8 GREEN) + acknowledged gallery `meta.json`
  `theoremCount` 24→32 drift (mechanic-pickup territory).

## Next Action

**S4 ACT Step 2 (next claim, ~50 LOC)**: paste the S14 PREP §5
skeleton into `proofs/Proofs/ZsqrtdNegTwoOQ03.lean` after the existing
`legendreSym_neg_three` lemma (currently L461-L463). The lemma to
land is

```
lemma legendreSym_neg_three_eq_one_iff
    (p : ℕ) [Fact p.Prime] (hp_ne_two : p ≠ 2) (hp_ne_three : p ≠ 3) :
    legendreSym p (-3) = 1 ↔ p % 3 = 1
```

(NB: the S12 PREP §5 hypothesis `(hp1 : p % 4 = 1)` is **strictly
stronger than needed** — the `p mod 4` dependence cancels across the
`(-1/p) · (3/p)` decomposition because QR for `3` (which has
`3 % 4 = 3`) introduces the matching sign flip; see S14 PREP §4
tableau for the 4-cell derivation.)

Bearers (all at Mathlib pin `2df2f0150c…`):

- `legendreSym.at_neg_one` Basic.lean:L272 — `(hp : p ≠ 2) : legendreSym p (-1) = χ₄ p`
- `χ₄_nat_one_mod_four` ZModChar.lean:L89 — `{n : ℕ} (hn : n % 4 = 1) : χ₄ n = 1`
- `χ₄_nat_three_mod_four` ZModChar.lean:L94 — `{n : ℕ} (hn : n % 4 = 3) : χ₄ n = -1`
- `legendreSym.quadratic_reciprocity_one_mod_four` QR.lean:L134 — `(hp : p % 4 = 1) (hq : q ≠ 2) : legendreSym q p = legendreSym p q`
- `legendreSym.quadratic_reciprocity_three_mod_four` QR.lean:L142 — `(hp : p % 4 = 3) (hq : q % 4 = 3) : legendreSym q p = -legendreSym p q`

The two `decide`-able sub-sorries in §5 reduce to the sub-lemma
`legendreSym 3 p = 1 ↔ p % 3 = 1` (factor out as
`legendreSym_three_eq_one_iff_p_mod_three_eq_one`; squares in
`ZMod 3 = {0, 1}` are `{0, 1}` and `p ≠ 3` rules out `p % 3 = 0`).

**Build-verify**: `./proofs/scripts/docker-build.sh Proofs.ZsqrtdNegTwoOQ03`
(G9 self-loop is INERT for Docker builds per memory note; the daemon
recovery question from S12 PREP §7 is from 2026-05-16 and may not
apply now — the next picker should attempt the build directly).

**S4 ACT Step 3 (after Step 2, ~30 LOC)**: per S14 PREP §6, parity
case-split on `x_int` extracted from `IsSquare (-3 : ZMod p)`:
canonicalize `x_int` to odd via `p - x_int` if even (p odd ⇒ parity
flip), write `x_int = 2y + 1`, get `x_int² + 3 = 4(y² + y + 1) =
4 · norm(⟨y + 1, 1⟩)`, combine with `gcd(p, 4) = 1` to get
`p ∣ norm(α)` for `α := ⟨y + 1, 1⟩`, then use UFD non-irreducibility
(`PrincipalIdealRing.to_uniqueFactorizationMonoid` PID.lean:L345 +
`UniqueFactorizationMonoid.irreducible_iff_prime`) to extract
`p = α · β` with neither a unit, forcing `norm(α) = p` via
`1 < norm(α), norm(β) < p²`.

**S5 ACT (after S4 ACT, ~100 LOC)**: the main theorem
`sq_add_three_sq_of_prime_one_mod_three`. Conversion step uses
`4p = (2a - b)² + 3 b²` (already proven inside S2 as the witness for
`norm_nonneg`); the parity case-split between `a, b` same-parity and
opposite-parity reduces to `omega + interval_cases`.
