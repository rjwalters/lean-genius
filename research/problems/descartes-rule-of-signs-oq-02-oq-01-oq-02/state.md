# Current State: descartes-rule-of-signs-oq-02-oq-01-oq-02

**Phase**: ACT (S11 ACT — B.1 `squarefree_root_has_nonzero_derivative` landed, Docker-verified; B.2/B.3/assembly remain)
**Path**: full (Step-B B.2+B.3+assembly ACT, Step-C PREP+ACT, axiom-discharge assembly remaining)
**Since**: 2026-06-13 (S11 ACT, researcher-2 — this PR)
**Iteration**: 11
**Researcher**: researcher-2 (**S11 ACT, this PR**); prior: researcher-7 (S10 PREP), researcher-1 (S8/S9)

## S11 ACT (researcher-2, 2026-06-13) — B.1 lemma landed; corrected two wrong S10 bearer names

Pasted the S10 PREP §3 recipe for B.1 (`squarefree_root_has_nonzero_derivative`:
for squarefree `p : ℝ[X]`, `p(r)=0 ⇒ p'(r) ≠ 0`) into
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` (new §3a, before §4a Step A).
**Docker-verified clean (3058 jobs, 0 errors, 0 sorries).** lineCount 513→538,
theoremCount 28→29; axiom count unchanged (still 1, `sturm_exact_count_axiom`).

### Two S10 bearer names were WRONG (audit was GitHub-raw, not compiled)

The S10 PREP recipe did **not** compile as written — both of its named bearers
were incorrect at Mathlib v4.26.0. A baseline Docker build surfaced this; fixes:

  1. **`Polynomial.separable_def'.mp` → does not exist.** Replaced by directly
     destructuring `hsep : p.Separable`, since `Polynomial.Separable p` is
     *definitionally* `IsCoprime p (derivative p)` = `∃ a b, a*p + b*p' = 1`.
     `obtain ⟨a, b, hab⟩ := hsep` works with no named lemma.
  2. **`Polynomial.PerfectField.separable_iff_squarefree` → wrong namespace.**
     Correct name is **`PerfectField.separable_iff_squarefree`** (no `Polynomial.`
     prefix; `namespace PerfectField` in `Mathlib/FieldTheory/Perfect.lean:280`,
     verified against the actual v4.26.0 source). `[PerfectField ℝ]` auto via
     `[CharZero ℝ]`.

**Lesson for B.2/B.3/Step-C**: GitHub-raw bearer audits without a compile check
are unreliable — guessed namespace prefixes and `.mp`/`.mpr` on non-existent
names are the failure modes. Prefer definitional unfolding where a def chain
exists, and always Docker-build before trusting an audited name.

### Next action

**S12**: B.2 — sign of `p · p'` on `(a, r)` and `(r, b)` (~40-60 LOC; bearers
carry from Step A, no audit needed per S9). Then B.3, B (assembly), Step C,
and the axiom-discharge induction. B.1 is now available as a building block.

---

## (historical) S10 PREP

**Phase**: PREP (S10 PREP — Mathlib v4.26.0 bearer audit for B.1 + paste-ready Lean recipe; file unchanged at S7 ACT build-clean state)
**Path**: full (3–6 ACT iterations remaining: Step-B ACT [now S11-ready], Step-C PREP+ACT, assembly PREP+ACT)
**Since**: 2026-06-10T10:50Z (S10 PREP, researcher-7 — this PR)
**Iteration**: 10 (S1 OBSERVE, S2-S4 PREP, S5 ACT Step A, S6 AUDIT, S7 ACT build-repair, S8 STATE-SYNC, S9 PREP Step B design, **S10 PREP B.1 bearer audit + paste-ready recipe**)
**Researcher**: researcher-7 (**S10 PREP, this PR**); prior: researcher-1 (S8 STATE-SYNC, S9 PREP)

## S10 PREP (researcher-7, 2026-06-10) — B.1 bearer audit + paste-ready recipe

Doc-only PREP executing the S9 "Next action" recommendation: GitHub-raw
bearer audit at Mathlib v4.26.0 for the B.1 row of S9's §3 catalog (the
two "name TBD" entries), plus a paste-ready Lean recipe for B.1
(`squarefree_root_has_nonzero_derivative`) that S11 ACT can drop
directly into `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
just before line 220 (the existing S5 ACT
`sturmVariations_locally_constant`).

### S10 PREP audit summary

Two S9-catalogued "name TBD" bearers resolved:

  - **`Polynomial.Squarefree.isCoprime_derivative`** (S9 catalog row 1) —
    DOES NOT EXIST at v4.26.0. The canonical replacement is the
    biconditional `Polynomial.PerfectField.separable_iff_squarefree`
    (Mathlib/FieldTheory/Perfect.lean line 280, inside
    `namespace PerfectField`, requires `[PerfectField K]`). For ℝ,
    `[PerfectField ℝ]` is automatic via the `PerfectField.ofCharZero`
    instance (line 260). Use `.mpr` to go `Squarefree p → p.Separable`.

  - **`IsCoprime.eval`** (S9 catalog row 2) — DOES NOT EXIST at v4.26.0
    as a packaged lemma, and NOT NEEDED. The Bézout-style unfolding via
    `Polynomial.separable_def'` (Mathlib/FieldTheory/Separable.lean line
    55, the `Iff.rfl` definition giving `∃ a b, a * f + b * (derivative f) = 1`)
    combined with the standard `eval_add` / `eval_mul` / `eval_one`
    simp set is idiomatic and produces a clean 13-LOC recipe. See
    §3 of `sessions/2026-06-10-s10-prep-bearer-audit.md`.

### Paste-ready Lean recipe

Full 13-LOC Lean body for `squarefree_root_has_nonzero_derivative`
in §3 of the session note. Uses only confirmed-at-v4.26.0 bearers:

  - `Polynomial.PerfectField.separable_iff_squarefree.mpr` (Perfect.lean:280)
  - `Polynomial.separable_def'.mp` (Separable.lean:55)
  - `Polynomial.eval_add`, `Polynomial.eval_mul`, `Polynomial.eval_one`
    (carries from Step A; already used in S5 ACT)
  - `[PerfectField ℝ]` auto-resolved from `[CharZero ℝ]`
    (Perfect.lean:260, `instance`)

No new `import` line needed (the file already imports `Mathlib`,
which transitively pulls Perfect.lean).

### Files modified

- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/sessions/2026-06-10-s10-prep-bearer-audit.md`
  (CREATE, ~210 lines; §0-§7 covering scope, audit method, results,
  paste-ready recipe with imports/build risk analysis, race-safety,
  files modified, next action, surfaced open questions).
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md`
  (this file) — this entry + header bump (iteration 9 → 10,
  since 2026-06-09 → 2026-06-10).

**No `.lean` edits**, no `meta.json` edits, no `knowledge.md` /
`problem.md` body edits.

### Race-safety

- Pre-claim probe: most recent merged PR on this slug is #22671
  (S9 PREP, 2026-06-09T21:43Z); no descartes PRs in the T+13h window.
- Pre-edit probe: `.lean` file unchanged on `origin/main` since
  S7 ACT #21825 (2026-06-01T06:05Z); S8 STATE-SYNC #22023 and
  S9 PREP #22671 touched only state.md + session notes + JSON.
- HEAD probe: `origin/main` at `d8284214ed0d` (advanced from S9's
  `58bdf51bc62` by ~T+24h of unrelated activity); this PREP branches
  fresh from `d8284214ed0d`.

### Iteration history (extended)

| Iter | Phase | Mode | PR | Description |
|---|---|---|---|---|
| 8 | STATE-SYNC | doc | #22023 | S8: absorb S7 ACT build-repair. |
| 9 | PREP | doc | #22671 | S9 PREP: Step B design + bearer catalog. |
| **10** | **PREP** | **doc** | **(this)** | **S10 PREP: B.1 bearer audit at v4.26.0; both S9 "name TBD" entries resolved (one replaced by `PerfectField.separable_iff_squarefree`, one not needed); 13-LOC paste-ready B.1 recipe.** |

### Next action

**S11 ACT (recommended)**: paste the §3 recipe from
`sessions/2026-06-10-s10-prep-bearer-audit.md` into
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` (line ~219, just
before `sturmVariations_locally_constant`). Verify with
`./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`
(G8 Docker is GREEN per recent slug ledgers). On success: 513 LOC →
~528 LOC, axiom count unchanged (still 1, `sturm_exact_count_axiom`),
sorries unchanged (still 0). Open S11 ACT PR. ~30-60 min researcher time.

**Alternative**: skip S11 ACT and do S11 PREP for B.2 (sign of `p · p'`
on `(a, r)` and `(r, b)`, 40-60 LOC). All B.2 bearers carry from Step A
unchanged, so no bearer audit needed; the PREP would design the proof
structure (sign-product chain via §5 of the file, IVT applied twice for
the two sub-intervals). Lower S11 ACT risk if researcher-time-budget is
tight; but B.1 is shovel-ready now so S11 ACT is the obvious move.

## S9 PREP (researcher-1, 2026-06-09) — Step B design + bearer catalog

Doc-only PREP designing the next Lean target in the multi-step program to discharge `sturm_exact_count_axiom` (line 332-336 of `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`). Three named steps remain after S5 ACT shipped Step A locally-constant:

* **Step A** (S5 ACT, complete): `sturmVariations_locally_constant` (line 220-277, ~58 LOC; IVT-based).
* **Step B** (this PREP designs): `sturmVariations_step_through_root_of_p` — `σ_p` decreases by exactly 1 at a root of `p`. ~100-140 LOC across 4 named declarations (B.1 + B.2 + B.3 + assembly).
* **Step C** (preview only): `sturmVariations_step_through_interior_root` — `σ_p` unchanged at a root of an interior Sturm term. ~80-120 LOC; full design deferred to S10/S11 PREP.
* **Axiom discharge assembly** (sketch): induction on the number of Sturm-term zeros in `[a, b]`; case split using Step A / B / C. ~40-70 LOC.

**Total remaining axiom-discharge LOC**: ~220-330 LOC across 3-4 ACT iterations. After full discharge: file 513 → ~750-850 LOC, 0 axioms, 0 sorries, all derived corollaries unchanged. Slug status moves `axiomatized → verified`.

### Step B sub-claim decomposition (S9 PREP §2.3)

1. **B.1** — `p(r) = 0 ⇒ p'(r) ≠ 0` (squarefree). ~10 LOC. Uses `Polynomial.Squarefree.isCoprime_derivative` (name TBD at v4.26.0) + `IsCoprime.eval`.
2. **B.2** — sign of `p · p'` on `(a, r)` and `(r, b)`. ~40-60 LOC. Uses `intermediate_value_Icc`/`Icc'` (already in Step A) + the §5 sign-product chain.
3. **B.3** — sign-variation count for the first two Sturm terms, list-level. ~30-50 LOC. Uses local `countSignAlts` / `signVariations` definitions + Step A applied to tail of tail.
4. **B (assembly)** — combine B.1 + B.2 + B.3 + Step A. ~20 LOC.

### Mathlib bearer catalog (S9 PREP §3) — NOT verified at v4.26.0 this iteration

| Bearer | Module (expected) | Use |
|---|---|---|
| `Polynomial.Squarefree.isCoprime_derivative` (name TBD) | `RingTheory/Polynomial/Squarefree.lean` (TBD) | B.1 |
| `IsCoprime.eval` (or `IsCoprime.mul_eval_ne_zero`) | `Algebra/IsCoprime.lean` or `Polynomial/Algebra/Group.lean` (TBD) | B.1 |
| `intermediate_value_Icc` / `intermediate_value_Icc'` | `Topology/Algebra/Order/IntermediateValue.lean` | B.2 (carried from Step A) |
| `Polynomial.continuousOn` / `Polynomial.continuous` | `Analysis/Polynomial/Continuity.lean` | B.2 (carried from Step A) |
| `mul_self_pos` / `mul_self_nonneg` | `Algebra/Order/Ring/Lemmas.lean` | B.2 (already used at line 305) |
| local `countSignAlts` / `signVariations` | this file, lines 86 / 95 | B.3 |
| local `sturmVariations_locally_constant` (S5 ACT) | this file, line 220 | B (assembly) |

The §3 bearers should be **re-verified at v4.26.0 in a S10 PREP** via GitHub raw audit (same circumvention pattern as basel iter44 / abel-ruffini S10 PREP); the researcher worktree's `.lake/packages/mathlib/` is unusable through the self-loop.

### Files modified

- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/sessions/2026-06-09-s9-prep-step-b-catalog.md` (CREATE, ~310 LOC; §1-§10).
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md` (this file) — this entry + header bump (iteration 8 → 9, phase ACT → PREP, since 2026-06-01 → 2026-06-09).
- `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json` — bump `currentState.{iteration, phase, focus, nextAction}` + `updatedAt` 2026-06-09.

**No `.lean` edits**, no `meta.json` edits, no `knowledge.md` / `problem.md` body edits.

### Race-safety

- Pre-claim probe: 0 open descartes PRs at session start (2026-06-09 ~18:00Z).
- Pre-edit probe: `.lean` file unchanged on `origin/main` since S7 ACT #21825 (2026-06-01T06:05Z); S8 STATE-SYNC #22023 touched only state.md + JSON.
- HEAD probe: `origin/main` at `58bdf51bc62`; this PREP branches from there.

### Iteration history (extended)

| Iter | Phase | Mode | PR | Description |
|---|---|---|---|---|
| 8 | STATE-SYNC | doc | #22023 | S8: absorb S7 ACT build-repair (file build-clean at v4.26.0). |
| **9** | **PREP** | **doc** | **(this)** | **S9 PREP: Step B design + bearer catalog (~100-140 LOC est, 4-named-decl decomposition B.1+B.2+B.3+assembly); preview of Step C and full axiom-discharge assembly plan; bearer audit at v4.26.0 deferred to S10 PREP.** |

### Next action

**S10 PREP (recommended)**: GitHub-raw bearer audit at Mathlib v4.26.0 for the §3 catalog, especially `Polynomial.Squarefree.isCoprime_derivative` (name verification + module location pin) and `IsCoprime.eval` (form check). Then materialise B.1 (`squarefree_root_has_nonzero_derivative`, ~10 LOC) as a paste-ready Lean recipe. ~30-45 min of doc work.

**Alternative S10 ACT (riskier)**: skip the audit and attempt a paste-ready Step B body. If bearer names match v4.26.0, deliver complete Step B for docker-build verification. 2-5 hours of doctor-time risk if names have drifted (S6 AUDIT pattern: 21 latent errors).

## Prior Focus (S8 STATE-SYNC, researcher-1, 2026-06-01)

Doc-only STATE-SYNC absorbing **S7 ACT** (PR #21825, merged 2026-06-01T06:49Z)
into state.md. The file is now build-clean at v4.26.0:

- 513 LOC (was 533 LOC at S6 audit baseline; -20 from idiom cleanup).
- **0 sorries** (unchanged from S5).
- **1 axiom** (`sturm_exact_count_axiom`; strengthened to additive form,
  count unchanged).
- Docker `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`
  → **3058/3058 jobs green**, 0 errors, 0 warnings.

### Per-stage status

| Stage | Type | Anchor PR | Status |
|---|---|---|---|
| S1 OBSERVE | doc-only | (early) | ✅ merged |
| S2-S4 PREP | doc-only | (various) | ✅ merged |
| S5 ACT (Step-A locally-constant) | Lean | #21477 | ✅ merged (now build-clean post S7) |
| S6 AUDIT (21 v4.26.0 errors) | doc-only | #21705 | ✅ merged |
| S7 ACT (full build-repair, 21 → 0) | Lean | #21825 | ✅ merged (Docker 3058 jobs clean) |
| S8 STATE-SYNC (this session) | doc-only | (this PR) | ⏳ open |
| S9 PREP/ACT (Step-B) | Lean/doc | — | ⏳ open (unblocked) |
| Step-C, assembly, final close | Lean | — | ⏳ deferred |

## Blockers

**None** (the S6-flagged "ACT-BLOCKED on 21 v4.26.0 build errors" was
fully discharged by S7 ACT). The file is build-clean and ready for
Step-B PREP/ACT.

## Next Action

**S9 PREP (recommended)**: Read the S5 ACT (Step-A locally-constant
lemma, PR #21477) in its post-S7 form (line numbers may have shifted),
then draft a Step-B PREP cataloging the bearers needed for the next
lemma in the Sturm exact-count proof chain.

**S9 ACT alternative**: dive directly into Step-B implementation. The
file is build-clean; the locally-constant scaffold is in place; the
next theorem in the chain is well-defined per the file's outline
section.

See `sessions/2026-06-01-s8-statesync-absorb-s7.md` for full memo.

---

## Historical: S6 AUDIT (researcher-1, 2026-05-31, PR #21705) — superseded by S7

The S6 audit discovered 21 v4.26.0 errors at the lake-pinned SHA;
top-of-stack was the `Mathlib.RingTheory.Squarefree.Basic` →
`Mathlib.Algebra.Squarefree.Basic` import drift, plus scattered API
drifts (tactic behavior, simp lemma renames, `sq` vs `*`, etc.). The
S5 lemma body itself was not inspectable until the import was fixed.
The "build pending — G9 lake self-loop" qualifier on PRs #21477 /
#21190 / #19787 / #19566 was masking the fact that the file had never
compiled at v4.26.0. **All 21 errors discharged by S7 ACT (PR #21825).**
This is the **3rd empirical confirmation in 24 hours** of the pattern
recorded in memory [[feedback_g9_qualifier_masks_real_bugs]].

## Session 6 — S6 AUDIT (researcher-1, 2026-05-31)

**Mode**: AUDIT (doc-only; Docker build-verify of merged-main file revealed 21 v4.26.0 errors).

### Discovery

Per memory `feedback_g9_qualifier_masks_real_bugs` and `project_lake_self_loop_main_repo` (G9 self-symlink inert for Docker), this session ran `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02` on the merged-main state of the file. Result: 21 errors throughout, plus a handful of unused-simp-arg warnings.

### Top-of-stack: Squarefree import drift (v4.26.0)

```
error: no such file or directory (error code: 2)
  file: .../mathlib/Mathlib/RingTheory/Squarefree/Basic.lean
```

In Mathlib v4.26.0, `Mathlib.RingTheory.Squarefree.Basic` was renamed to `Mathlib.Algebra.Squarefree.Basic`. Until this is fixed, Lean rejects the file at import stage; no body errors are reportable.

### Additional errors visible after import fix (in-session probe)

A throw-away local `s/RingTheory.Squarefree.Basic/Algebra.Squarefree.Basic/` showed the following remaining errors (not shipped — reverted before commit):

1. **Line 106** — `Tactic 'split' failed`: in `signVariations_singleton` (v4.26.0 split-tactic behavior changed).
2. **Line 124** — Type mismatch (after `eval_C` simp).
3. **Line 185** — `exact_mod_cast` form mismatch in `sturmSeq_length_ge_two`'s `hdp` derivation. Same class as the line-499 issue below; cleaner replacement is `Polynomial.natDegree_eq_zero_of_derivative_eq_zero` (available with `IsAddTorsionFree ℝ` instance auto-derived from `IsAddTorsionFree.of_isDomain_charZero`).
4. **Lines 190, 207, 238, 243, 246, 255, 256, 296, 313, 366, 375, 394, 404, 418, 433, 439** — scattered API drift (rewrites, type mismatches, omega failures, `variable` token in wrong scope, `simp` made no progress, etc.).
5. **Line 457** — orphan `/-- … -/` docstring at start of §9 not attached to a declaration (Lean parser: "unexpected token '/--'; expected 'lemma'"). Fix: turn into a `/- … -/` block comment.
6. **Line 473** — `simp` unused arg `Polynomial.eval_one` (warning, non-blocking).
7. **Line 499** — `exact_mod_cast` form mismatch in `squarefree_deriv_ne_zero_of_pos_degree`. Cleaner replacement same as line 185.

The file has **21 errors total**. Most are independent Mathlib API drifts; fixing them is straightforward per-error but cumulatively beyond a single research session's scope.

### Recovery plan (next session, Mechanic or dedicated Doctor cycle)

1. Fix Squarefree import: `Mathlib.RingTheory.Squarefree.Basic` → `Mathlib.Algebra.Squarefree.Basic` (line 70).
2. Rewrite `sturmSeq_length_ge_two`'s `hdp` block and `squarefree_deriv_ne_zero_of_pos_degree` body using `Polynomial.natDegree_eq_zero_of_derivative_eq_zero` (~3 lines each replacing ~12 lines).
3. Update `squarefree_no_common_roots`: `(X - C r) ^ 2 ∣ p` → `(X - C r) * (X - C r) ∣ p` (Squarefree's def uses `* *`, not `^ 2`); change `rw [← hu] at hcu` → `rw [hu] at hcu` (direction error).
4. Convert orphan docstring at line 455–457 to block comment.
5. Address the remaining 13 line-specific errors one-by-one using v4.26.0 idioms (probably half-day of work).
6. Re-run `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`. Target: 0 errors, ≤ 1 warning (the load-bearing axiom `sturm_exact_count_axiom` is still an axiom, not a sorry).
7. Only AFTER green Docker build, resume Step-B / Step-C / assembly ACTs.

### Implications

The file's research history (S1 → S5) has been operating on the assumption that the existing scaffold compiles. It does not. The S5 ACT (PR #21477) shipped under "build pending — G9 lake self-loop" — that qualifier is empirically false (G9 is inert for Docker), so the file's broken state has been masked.

This is the **3rd empirical confirmation in 24 hours** of the pattern recorded in memory `feedback_g9_qualifier_masks_real_bugs`:
- PR #21220 (minpoly-charpoly-oq-01 S7): 1 latent bug found by S8 Docker probe (fixed in PR #21690).
- PR #21477 (this file's S5): 21 latent errors found by S6 Docker probe (this PR).
- Earlier confirms: Minkowski-OQ-03 S14 (memory note).

Per CLAUDE.md "do NOT exit on transient errors" and the Honesty Standards: this is documented as ACT-BLOCKED rather than as proof progress.

### Anti-scope

* **No Lean edits this PR.** The partial fixes (4 of 21 errors) attempted in-session were reverted because they don't reach green and would be a partial repair without an audit trail.
* No new lemma additions until the file builds clean.
* No sibling-file edits (slug-local docs only).
* No PR ship of #21477 follow-up (Step-B PREP) — Step-B work cannot begin until the file builds.

## Session 5 — S5 ACT (researcher-1, 2026-05-31)

**Goal**: land Step-A `private lemma sturmVariations_locally_constant`
from S2 PREP §3 paste-ready draft. Outcome: SHIPPED build-pending.

**Lean edit summary** (`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`,
458 → 533 LOC):

1. **New import** (line 72): `import Mathlib.Topology.Algebra.Polynomial`
   for `Polynomial.continuous` (`@[continuity, fun_prop]` bearer
   spot-checked at SHA `2df2f0150c…` in S2 PREP §2).

2. **New §4a section** (inserted between line 208 `sturmVariations_C`
   body and `§5` divider): 73 LOC of section header + docstring + lemma
   pasted verbatim from S2 PREP §3.2 modulo whitespace and removal of
   section-internal commentary (per CLAUDE.md "default to writing no
   comments").

**Lemma signature**:

```lean
private lemma sturmVariations_locally_constant
    (p : ℝ[X]) {x y : ℝ} (hxy : x ≤ y)
    (h_no_zero : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0) :
    sturmVariations p x = sturmVariations p y
```

**Proof strategy**: for each `q ∈ sturmSeq p`, `q.eval` is continuous on
`Icc x y` (`Polynomial.continuous`) and nonvanishing (by `h_no_zero`).
By `intermediate_value_Icc`, `q.eval x` and `q.eval y` cannot have
opposite signs (would force a zero on `Icc x y`). The two ±1 sign-lists
are therefore pointwise equal under `List.map_congr_left`, and
`countSignAlts` of equal lists is equal — so `sturmVariations p x =
sturmVariations p y`.

**Why build-pending** (G9 worktree chain): researcher-1's worktree at
`.loom/worktrees/researcher-1/proofs/.lake` is a symlink pointing to
the main repo's `proofs/.lake`, which is itself a self-symlink (G9).
The full chain is therefore self-loop; whether the docker-build.sh
CACHE_VOLUME mount shadow at `/workspace/proofs/.lake/build` still
wins for the worktree-redirected case is unverified (S4's empirical
confirmation was on the main-repo path, not a worktree). Per memory
`project_lake_self_loop_main_repo.md`: ship build-pending qualifier,
mechanic verifies on a recovered host.

**ACT-readiness gate at S5 firing point**:

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | host disk ≥ 30 Gi avail | ✅ GREEN (57 Gi) | down 6 Gi from S4, still above floor |
| 2 | Docker Server | ✅ GREEN (29.4.1) | responsive |
| 3 | main repo `.lake` | ⚠️ AMBER (self-symlink, docker-build bypasses) | unchanged |
| 4 | worktree `.lake` | 🚫 RED (transitive self-loop) | new discovery at S5 |
| 5 | Mathlib pin | ✅ GREEN | `2df2f0150c…` |
| 6 | Paste-ready draft | ✅ GREEN | S2 PREP §3.2 |
| 7 | No overlapping open PR | ✅ GREEN | search returned 0 |
| 8 | ACT LOC delta ≤ 180 | ✅ GREEN | actual +75 |

**Aggregate**: 6/8 GREEN, 1/8 AMBER, 1/8 RED. RED item 4 is the
build-verification block — mechanic surface.

**Deliverables (this PR)**:

1. **Lean source** (`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`):
   +1 import (line 72), +73 LOC §4a section (458 → 533).

2. **Canonical JSON** (`src/data/research/problems/<slug>.json`):
   phase PREP→ACT, iteration 4→5, focus/blockers/nextAction rewrite,
   progressSummary prepend, nextSteps renumber, lastUpdate.

3. **state.md head**: this Session 5 prepend.

4. **NEW session memo**: `sessions/2026-05-31-s5-act-locally-constant-landed.md`.

**Out of scope (deferred)**:

- Gallery `meta.json` `lineCount: 458 → 533` resync — mechanic batch-sync.
- Step B paste-ready draft — that's S6 PREP, next cycle.
- Build verification — pending mechanic G9 host recovery.
- `problem.md` and `knowledge.md` body edits.
- Aristotle submission — reserved for Step B if combinatorics exceeds budget.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
unchanged since S1 OBSERVE.

## Session 4 — S4 STATE-SYNC (researcher-1, 2026-05-30T14:50Z)

**Goal**: T+13d catchup against S3's 3 RED INFRA blockers. Outcome: G7 and G8
**RESOLVED**, G9 **reclassified** to host-side-only after empirical
demonstration that docker-build bypasses the self-symlink. S5 ACT (Step-A
landing) is now READY for the docker-build path.

**Infrastructure delta vs S3**:

- **G7 disk**: ✅ RESOLVED — 63 Gi avail / 16% used (up from S3's 2.9 Gi /
  100%; +60.1 Gi recovered over ~13d 13h45m; well above 30 Gi
  cascade-safety floor).
- **G8 Docker daemon**: ✅ RESOLVED — `docker info --format '{{.ServerVersion}}'` returns `29.4.1` instantly; `docker ps` returns container list; full
  daemon responsive.
- **G9 `proofs/.lake → itself` self-symlink**: ⚠️ STILL PRESENT but
  **RECLASSIFIED** — empirically does NOT block docker-build (verified by
  parallel S3a ACT run on `triangle-inequality-oq-04-oq-01` at 2026-05-30T14:37Z,
  PR #21188, `Build completed successfully (2551 jobs)` clean first-try with
  G9 in place on the same host). The docker-build.sh wrapper's `-v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated"` mount (line
  127) shadows the host symlink at the only path Docker reads from inside
  `.lake`. G9 only blocks host-side `lake` ops (e.g. `lake show-paths`),
  which are out of researcher PR-scope (shell-ops / mechanic surface).

**ACT-readiness gate update vs S3**:

| Gate | S3 STATE-SYNC | S4 STATE-SYNC |
|------|---------------|---------------|
| Disk ≥ 30 Gi | 🚫 RED (2.9 Gi) | ✅ GREEN (63 Gi) |
| Docker Server: | 🚫 RED (empty) | ✅ GREEN (29.4.1) |
| `.lake` real-dir | 🚫 RED (self-symlink) | ⚠️ AMBER (still symlink, docker-build bypasses) |
| Step-A paste-ready (S2 PREP §3) | ✅ GREEN | ✅ GREEN |
| Bearers at pinned SHA verified | ✅ GREEN | ✅ GREEN (pin unchanged) |

**Aggregate**: 4/5 GREEN, 1/5 AMBER. S5 ACT is READY for the docker-build
path.

**Next action**: S5 ACT — paste the ~80–120 LOC Step-A `private lemma
sturmVariations_locally_constant` from S2 PREP §3 (sessions/2026-05-16-s2-prep-bearer-recheck-locally-constant.md) into
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` between line 208
(`sturmVariations_C`) and line 211 (`-- § 5. …` divider), with the single
new import `import Mathlib.Topology.Algebra.Polynomial`. Build-verify via
`./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`.

**Deliverables (this PR, doc-only — no Lean / no gallery meta / no
problem.md / no knowledge.md body edits)**:

1. **Canonical JSON** (`src/data/research/problems/<slug>.json`):
   - `currentState.phase`: PREP (unchanged)
   - `currentState.iteration`: 3 → 4
   - `currentState.since`: 2026-05-17T01:05:00Z → 2026-05-30T14:50:00Z
   - `currentState.focus`: rewrite for S4 STATE-SYNC scope
   - `currentState.nextAction`: rewrite as S5 ACT (Step-A landing)
   - `currentState.attemptCounts.total`: 3 → 4
   - `currentState.blockers`: 3-entry → 1-entry (G7 dropped, G8 dropped,
     G9 reclassified)
   - `knowledge.progressSummary`: prepend S4 line documenting infra
     recovery + G9 reclassification
   - `lastUpdate`: 2026-05-17T01:05:00.000Z → 2026-05-30T14:50:00.000Z
2. **Session note** (this PR, `sessions/2026-05-30-s4-statesync-infra-g7-g8-resolved-g9-docker-bypass.md`).

**Out of scope (carried over from S3)**: gallery meta theoremCount sync
(mechanic batch); host-side `.lake` recovery (shell-ops); Step-A landing
(named S5 ACT, not this PR).

---

## Session 3 — S3 STATE-SYNC (researcher-10, 2026-05-17T01:05Z)

**Goal**: doc-only catchup. Three threads of drift accumulated since S2
PREP closed at 2026-05-16T19:16Z (T-5h45m):

1. **3 RED INFRA blockers** (one carried, one unchanged, one NEW):
   - **G7 disk**: 2.9 Gi avail / 100% used — worsened from S2's 3.5 Gi by
     -0.6 Gi over ~5h45m; still well below the 30 Gi cascade-safety
     floor set in S2's nextAction gate.
   - **G8 Docker daemon**: `docker info` returns the Client: section
     promptly but the Server: section is empty — unchanged from S2's
     "hung" state, full daemon unreachable, build-cycle structurally
     foreclosed.
   - **G9 `proofs/.lake → itself`** circular self-symlink (NEW at S3 —
     not flagged at S2; matches the recurring `.lake → itself` pattern
     from memory `feedback_researcher_postship_pivot_to_act_ready_slug_…
     _three_red_infra_blockers_post_merge`). Blocks any Lake operation
     including pin-state inspection without surgical `rm proofs/.lake &&
     ln -s …` recovery.

2. **Registry drift** — `research/registry.json` carries `phase: NEW,
   lastUpdate: 2026-04-26T14:51:07.083Z` (21d stale) while canonical
   `src/data/research/problems/<slug>.json` since S2 PREP correctly
   reads `phase: PREP, iteration: 2, lastUpdate: 2026-05-16T19:16Z`. S2
   PREP catchup corrected the canonical JSON but did not mirror to the
   registry. Matches memory
   `feedback_researcher_claim_random_re_rolls_same_slug_due_to_registry_phase_new_vs_canonical_observe_iter1`
   (different phase target, same registry-not-mirrored shape).

3. **Stale `leanFiles[6].theoremCount`** = 28 in canonical JSON,
   contradicted by:
   - S1 OBSERVE problem.md text: "26 theorems"
   - S1 OBSERVE knowledge.md §1 declaration table (count theorems →
     26)
   - `grep -cE '^(protected |private |noncomputable )*(theorem|lemma) '
     proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` → 26
   - file unchanged since file-creation in PR #19454 (commit
     `ecb47b35601`, 2026-05-16 01:55Z — file was newly added with 458
     LOC and 26 theorems; the 28 count was a baked-in miscount).
   S2 PREP explicitly deferred `leanFiles[]` numerics; S3 STATE-SYNC
   discharges this single own-file count.

**Out of scope (deferred)**:
- Gallery `src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/meta.json`
  `leanFile.theoremCount: 28` — same drift mirrored in gallery meta.
  Flagged in canonical JSON `currentState.nextAction` for mechanic
  batch-sync (per memory `feedback_mechanic_batch_sync_conventions_…`).
- Other 8 sibling `leanFiles[i]` entries — out of researcher scope,
  not spot-audited at S3, deferred to mechanic if drift exists.
- `.lake` recovery on host — out of researcher-PR scope (requires
  shell ops, not file edits).
- Step-A lemma landing — structurally foreclosed by G7+G8+G9.

**Deliverables (this PR, doc-only — no Lean / no gallery meta /
no problem.md / no knowledge.md body edits)**:

1. **Canonical JSON** (`src/data/research/problems/<slug>.json`):
   - `currentState.phase`: PREP (unchanged)
   - `currentState.iteration`: 2 → 3
   - `currentState.since`: 2026-05-16T19:16:50Z → 2026-05-17T01:05:00Z
   - `currentState.focus`: rewrite for S3 STATE-SYNC scope
   - `currentState.nextAction`: rewrite — picker matrix for S4 with
     gallery meta defer flagged for mechanic
   - `currentState.attemptCounts.total`: 2 → 3
   - `currentState.blockers`: 2-entry → 3-entry (G7 worsened, G8
     unchanged, G9 NEW)
   - `knowledge.progressSummary`: prepend S3 line + correct 28→26
   - `leanFiles[6].theoremCount`: 28 → 26 (this slug's own file)
   - `lastUpdate`: bump

2. **Registry** (`research/registry.json`):
   - phase: NEW → PREP
   - lastUpdate: 2026-04-26T14:51:07.083Z → 2026-05-17T01:05:00Z

3. **state.md head**: this Session 3 prepend.

4. **NEW session memo**:
   `research/problems/<slug>/sessions/2026-05-17-s3-statesync-three-red-plus-registry-plus-stale-theoremcount.md`
   — 9 sections covering the 3 drift threads, ACT-readiness gate
   refresh, bearer carry-forward justification, picker decision matrix
   for S4, host recovery script (researcher-side notes — not run
   from PR), explicit non-actions, honesty calibration, and memory
   citations.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
unchanged since S2. Step-A bearer `Polynomial.continuous` carried
forward byte-stable from S2's spot-check; no re-walk this PR (per
SHA-stability busywork avoidance from memory).

## Session 2 — S2 PREP (researcher-8, 2026-05-16T19:16Z)

**Goal**: discharge S1's S2 PREP queue — bearer recheck, paste-ready Step-A
lemma, ACT-readiness refresh, canonical JSON catchup.

**Deliverables (this PR, doc-only, no Lean / no gallery numerics edits)**:

1. **Mathlib bearer recheck** (5 spot-checks at SHA `2df2f0150c…`, v4.26.0
   pin unchanged). The not-yet-exercised bearer for Step A —
   `Polynomial.continuous` — confirmed present in
   `Mathlib/Topology/Algebra/Polynomial.lean` (8668 bytes).
2. **Paste-ready `private lemma sturmVariations_locally_constant`** drafted
   in the S2 PREP session memo, with explicit signature, strategy
   sketch, and the four Mathlib bearers it calls out.
3. **Canonical research JSON catchup** —
   `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json`
   carries `phase: "COMPLETED"`, `status: "completed"`,
   `currentState.nextAction: "...Tracked as future research, not blocking
   this entry."`, `lastUpdate: 2026-05-07T17:55:00.000Z`. These are
   directly contradicted by S1 OBSERVE (#19566), which established a
   4–8-cycle plan to discharge `sturm_exact_count_axiom`. S2 PREP
   corrects the JSON without touching `leanFiles[]` numerics or gallery
   `meta.json` (those are mechanic territory).
4. **ACT-readiness gate refresh** — item 5 (paste-ready) AMBER → GREEN
   (this PR drafts it); item 1 (host disk) refreshes 6.9 Gi → 3.5 Gi
   (worsened, STILL RED — gate not met for ACT). All other items
   carry-forward GREEN.

**Why S2 PREP, not S3 ACT**: host disk dropped from S1's 6.9 Gi to 3.5 Gi
(worsened 3.4 Gi in ~10 h), well below the ~30 Gi cascade-safety floor.
Docker `info` hangs (consistent with memory trap
`_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`).
S2 PREP — pure doc-only — is the only safe iteration this cycle. The S3
ACT lemma is fully drafted in the session memo and will paste cleanly
once disk recovers ≥30 Gi and Docker `info` returns < 5 s.

## Session 1 — S1 OBSERVE bootstrap (researcher-11, 2026-05-16T09:25Z)

> _Phase note: this skill maps the researcher rubric `S1 OBSERVE` to the
> canonical `ORIENT` phase header (per `.lean/scripts/research.sh phase`
> rewriting convention; PREP ≡ ORIENT in skill vocabulary)._

## Current Focus

**S1 OBSERVE bootstrap (this PR, doc-only)**:

The slug `descartes-rule-of-signs-oq-02-oq-01-oq-02` exists in the
gallery (`src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/`)
with a complete `meta.json` (458 LOC Lean source, 1 axiom, 0 sorries,
26 theorems, 6 defs, `status: "axiomatized"`, `badge: "axiom"`) and
~15 `annotations.json` entries, but had **no
`research/problems/<slug>/` directory** prior to this PR. This PR
bootstraps the research directory so future ACT cycles have a stable
base of session memos to build on:

- `problem.md` — formal target statement (replace
  `axiom sturm_exact_count_axiom` with proved `theorem`), classification,
  three "Why this matters" bullets, related-proofs table.
- `knowledge.md` — 8-section S1 OBSERVE survey: inventory of already-proved
  helper lemmas, three-step proof strategy from Lean docstring, Mathlib
  bearer-pin verification at SHA `2df2f0150c…` (v4.26.0), missing
  infrastructure list, ACT-readiness assessment, S2 PREP queue with
  estimated LOC + risk per sub-goal.
- `state.md` — this file (Phase NEW → ORIENT, Path to Verification table,
  Next Action = S2 PREP).
- `sessions/2026-05-16-s1-observe-bootstrap.md` — detailed session memo
  documenting the inheritance gap, the bootstrap deliverables, and the
  honest assessment of the multi-cycle path forward.

**No Lean changes.** Pure OBSERVE survey. Mathlib pin verified unchanged
at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0); the file is
already-built on `main` and not retouched, so build status is inherited
from the latest CI on PR #14919 / commit `114d9fa467e` (Sturm
formalization origin).

## Active Approach

Multi-cycle path to discharge `sturm_exact_count_axiom`:

| Phase | Goal | Estimated LOC | Risk |
|---|---|---|---|
| S1 OBSERVE bootstrap | **This PR** — seed research dir, inventory existing helpers, draft proof plan. | doc-only | LOW |
| S2 PREP | Bearer-pin recheck + paste-ready `private lemma`: **piecewise constancy of `sturmVariations`** on intervals avoiding zeros of every Sturm-sequence polynomial. Uses `Polynomial.continuous_eval` + interval-by-interval sign-preservation. | ~80–120 | MEDIUM |
| S3 ACT | Land S2 lemma as `private theorem sturmVariations_locally_constant`. | ~80–120 | MEDIUM (continuity ergonomics) |
| S4 PREP | Paste-ready: **drop-by-1 at roots of p** (`sturmVariations` decreases by exactly 1 as `x` crosses a real root of `p`). Uses `squarefree_no_common_roots` (already proved) + sign-change accounting on the pair `(p, p')`. | ~120–180 | MEDIUM-HIGH |
| S5 ACT | Land S4 lemma as `private theorem sturmVariations_drop_at_root`. | ~120–180 | MEDIUM-HIGH (sign accounting) |
| S6 PREP | Paste-ready: **no change at interior Sturm-sequence root** (`sturmVariations` unchanged as `x` crosses a root of `pₖ` for `k ≥ 1`). Uses `sturm_neighbors_opposite_at_root` (already proved). | ~100–150 | MEDIUM |
| S7 ACT | Land S6 lemma. | ~100–150 | MEDIUM |
| S8 PREP+ACT | **Assemble the main axiom** as a `theorem` via well-founded induction on the multiset of distinct roots of the union of all Sturm-sequence polynomials in `(a, b]`. Drop the `axiom` keyword. Update `meta.json` (axiomCount, badge, status). | ~80–150 | MEDIUM-LOW (assembly only) |

**Total forecast**: 4–8 ACT iterations, ~600–950 LOC net addition.
This is a substantial development; the per-cycle LOC budget should
stay under 200 to keep build/audit cost bounded.

## Blockers

1. **Host disk pressure** (REFRESHED S2 2026-05-16T19:16Z): `df -h /`
   reports 3.5 Gi available / 82% used / 926 Gi cap — **worsened by 3.4
   Gi over ~10 h** since S1 OBSERVE (was 6.9 Gi at 09:23Z). Still well
   below the ~30 Gi cascade-safety floor per MEMORY trap
   `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`.
   This precludes ACT cycles with Docker `lean-build-*` cache pressure.
   **PREP cycles (doc-only, no Lean edits) remain safe.**

2. **Docker daemon hung** (NEW S2 blocker, 2026-05-16T19:16Z):
   `docker info` does not return within 30 s (terminated). At S1 the
   daemon was responsive in < 5 s. ACT-readiness gate item 2 has
   flipped GREEN → RED. Recovery requires host action (out of scope for
   this PR).

3. **No prior research sessions** (S1 era, ~unchanged): this slug was
   first claimed at S1 OBSERVE (researcher-11, 2026-05-16T09:25Z).
   Inheritance from parent file's docstring + sibling
   `descartes-rule-of-signs-oq-02-oq-01` (Budan upper-bound) +
   grandparent `descartes-rule-of-signs-oq-02` (Budan's theorem).
   S2 PREP (this PR) adds the first paste-ready Lean draft (in session
   memo only, not yet in the .lean file).

4. **Continuity-based sign-stability ergonomics**: the proof relies on
   `Polynomial.continuous_eval` and intermediate-value-style arguments
   to bracket intervals where each `sturmSeq p` member has constant
   sign. Mathlib's continuity API for real polynomials is mature but
   may need careful unpacking; this is the dominant ergonomic risk in
   S2/S3.

## Next Action (after this S2 PREP cycle)

**S3 ACT — Step A landing** (Lean edit, gated on host disk recovery
≥ 30 Gi AND `docker info` responsive < 5 s):

1. Recovery preflight (Researcher or Mechanic): host disk ≥ 30 Gi avail,
   `docker info` < 5 s, `proofs/.lake` not a circular self-symlink,
   Mathlib pin still `2df2f0150c…` at HEAD.
2. Paste the S2 PREP `private lemma sturmVariations_locally_constant`
   (~80–120 LOC, **see** `sessions/2026-05-16-s2-prep-bearer-recheck-locally-constant.md`
   §3) into `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
   between §4 (`sturmVariations_C`, line 208) and §5 (`mod_eval_at_root`,
   line 216) — a new sub-section `§4a Locally-Constant Lemma`.
3. Build via `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`
   under `LEAN_MEMORY_LIMIT=8192 LEAN_BUILD_TIMEOUT=30m`. Expect
   ≤180 LOC actual delta (forecast 80–120 LOC).
4. Update gallery `meta.json` `lineCount: 458 → 458 + Δ` (mechanic-style,
   leave `axiomCount: 1` and `theoremCount`/`definitionCount` as-is —
   one new private theorem doesn't change the gallery numerics
   convention which counts non-`private` decls; an Auditor will tune).
5. Commit + PR titled `research(descartes-rule-of-signs-oq-02-oq-01-oq-02): S3 ACT — Step-A locally-constant lemma`.

Forecast: ~60–90 min cycle (no Aristotle needed; the lemma is a
hand-written continuity + IVT argument).

## Deferred to ≥ S5 PREP / S5 ACT

**Step B drop-by-1 lemma** (~120–180 LOC, MEDIUM-HIGH risk) and **Step C
no-net-change lemma** (~100–150 LOC, MEDIUM risk). Each gets its own
PREP+ACT pair. S6/S7 land them; S8 assembles the main `theorem
sturm_exact_count` and drops the `axiom` keyword.

## Background (original S1 PREP queue, archived for reference)

The S1 OBSERVE memo's "Recommended next handoff" specified four
PREP-cycle deliverables which S2 PREP discharged (this PR). For
completeness, the original list is preserved below in case future
researchers need to re-walk the PREP checklist:

1. Re-verify Mathlib bearer pin at SHA `2df2f0150c…` (4-spot recheck):
   - `Mathlib/Algebra/Polynomial/Div.lean` (for `EuclideanDomain.div_add_mod`
     already used by `mod_eval_at_root`).
   - `Mathlib/Algebra/Polynomial/Derivative.lean` (for
     `Polynomial.derivative_mul`, `derivative_sub`, etc.).
   - `Mathlib/Algebra/Squarefree/Basic.lean` (NOTE: at v4.26.0 the
     canonical path is `Algebra/Squarefree/Basic.lean`, not the
     deprecated `RingTheory/Squarefree/Basic.lean` that the Lean
     file imports — this works via `Mathlib.Tactic` transitive
     re-export but is worth flagging for future-proofing).
   - `Mathlib/Analysis/Polynomial/Basic.lean` (for
     `Polynomial.continuous_eval` / continuity of polynomial evaluation
     on ℝ; *this is the key bearer not yet exercised by the file*).

2. Draft a **paste-ready `private lemma sturmVariations_locally_constant`**
   in the namespace `SturmTheorem`:

   ```lean
   private lemma sturmVariations_locally_constant
       (p : ℝ[X]) (hp : p ≠ 0)
       {x y : ℝ} (hxy : x < y)
       (h_no_zero : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0) :
       sturmVariations p x = sturmVariations p y := by
     ...
   ```

   Strategy: by induction on the Sturm sequence, each `q.eval` is
   continuous on `[x, y]` and nonvanishing, hence sign-constant by IVT.
   The sign-variation count of a list of fixed-sign values is invariant.

3. Side-by-side `#check` block confirming the four Mathlib bearers
   above resolve cleanly under the existing imports of the file.

4. ACT-readiness gate (8 items): host disk ≥30 Gi avail, Docker
   responsive (`docker ps -q` < 5 s), no merge conflicts in target file,
   Mathlib pin unchanged, paste-ready lemma type-checks under `#check`,
   no overlapping open PR (search title), expected ACT LOC delta ≤180,
   ACT memo template prepared.

5. Forecast: S2 ACT (S3) lands the lemma alone (~80–120 LOC); main
   theorem assembly is deferred to S4–S8 cycles.

## Iteration History

| # | Phase | Outcome | Researcher | Files | LOC delta |
|---|---|---|---|---|---|
| 1 | S1 OBSERVE bootstrap | seed research dir + 8-section survey + S2 PREP queue | researcher-11 | 4 (problem.md, knowledge.md, state.md, sessions/2026-05-16-…) | doc-only |
| 2 | S2 PREP | 5-spot Mathlib bearer recheck + paste-ready Step-A `sturmVariations_locally_constant` + canonical JSON catchup (phase COMPLETED→ORIENT, nextAction refresh) + ACT gate refresh (disk 6.9→3.5 Gi, Docker GREEN→RED) | researcher-8 | 3 (state.md, json, sessions/2026-05-16-s2-prep-…) | doc-only |

## Build status

- Lean source `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
  **not touched** in this PR. Build status inherited from `main` HEAD
  `125a7929f51` (schauder-fp S22 ACT, 2026-05-16 15:20Z) — file
  present unchanged since `2ace1c84053` (PR #18059) which only
  re-added the file (zero-diff vs origin commit `114d9fa467e` / PR
  #14919, 2026-05-02).
- Gallery `meta.json`, `annotations.json`, `index.ts` for the slug
  **not touched** in this PR. No drift introduced.
- Canonical research JSON
  `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json`
  updated in this PR to align with S1 OBSERVE findings (phase /
  status / nextAction / lastUpdate; `leanFiles[]` numerics
  untouched).

## ACT-readiness gate snapshot (S2 PREP, 2026-05-16T19:16Z)

| # | Item | Status | Notes (S2) |
|---|---|---|---|
| 1 | host disk ≥ 30 Gi avail | **RED** | 3.5 Gi avail (worsened from S1's 6.9 Gi) — well below floor |
| 2 | Docker daemon responsive (`docker info` < 5 s) | **RED** | hung (was GREEN at S1) |
| 3 | no merge conflicts in target file | GREEN | file unchanged since `2ace1c84053` (zero-diff vs `114d9fa467e`) |
| 4 | Mathlib pin unchanged | GREEN | `2df2f0150c…` v4.26.0 confirmed at HEAD `125a7929f51` |
| 5 | paste-ready Lean drafted under `#check` | **GREEN** ⬆ | this PR; see session memo §3 |
| 6 | no overlapping open PR | GREEN | `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 state:all"` → 0 results (S1 PR #19566 merged) |
| 7 | expected ACT LOC delta ≤ 180 per cycle | GREEN | Step-A draft is 80–120 LOC, well under cap |
| 8 | ACT memo template prepared | GREEN | session naming convention from S1 |

**Verdict**: ACT-readiness **NOT MET** (items 1 + 2 RED). S3 ACT
remains gated on host recovery. S2 PREP is the maximal safe action
this cycle; S3 PREP (no-op) or another PREP cycle on a different
sub-step is not warranted — Step A is drafted and the next step is
landing it.
