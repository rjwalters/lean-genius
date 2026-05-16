# Current State

**Phase**: ACT (S3 SCAFFOLD + S4 PREP merged; capstone discharge skeleton paste-ready against `main`)
**Since**: 2026-05-15T23:26:58Z (S3 ACT SCAFFOLD merge anchor)
**Last Updated**: 2026-05-16T03:35Z (Iteration 13, researcher-11)
**Iteration**: 13

## Iteration 13 (researcher-11, 2026-05-16) — S5 STATE-SYNC

**Outcome**: STATE-SYNC (doc-only) — post-S4-PREP-merge catch-up: state.md head + JSON `currentState` block + `attemptCounts` (off-by-12 corrected) + 12-bearer drift recheck (4 fresh round-trips + 8 byte-stable, 0 drift) + S5 ACT-readiness gate 8/8 GREEN.

### What I added

- `sessions/2026-05-16-s5-state-sync-post-s4-prep-merge.md` (NEW, ~310 LOC) — post-merge snapshot, 12-row bearer drift recheck (§3), 8/8 GREEN ACT-readiness gate (§4), iteration ledger consolidated through Iter 13 (§5), orthogonality manifest (§6), strict-honesty footprint (§7).
- This `state.md` head: phase header refresh + Since + Iteration 11→13 + Iteration 12 + Iteration 13 sections inserted above preserved Iter 11 block.
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`: `currentState.phase`/`since`/`lastUpdated`/`iteration`/`focus`/`nextAction` refresh + `attemptCounts.total` 1→13 (off-by-12 fix) + `knowledge.progressSummary` tail + `knowledge.nextSteps[0]` rewrite.

### Why a STATE-SYNC now

PR #19253 (S4 PREP, researcher-3) merged 2026-05-15T18:03:22Z. PR #19068 (S3 ACT SCAFFOLD, researcher-8) merged 2026-05-15T23:26:58Z. state.md + JSON head still read Iter 11 (SCAFFOLD pre-merge); the next ACT picker has no single-source view of the post-S4-PREP gate state. This STATE-SYNC corrects that and pins the gate at 8/8 GREEN with the §4 paste-ready ~75-LOC skeleton as the next single-step ACT.

### Next action (S5 ACT)

Paste S4 PREP §4 ~75-LOC capstone skeleton into `proofs/Proofs/Sqrt2MinpolyOQ03.lean` between L72 and L73 (replace L71 `  sorry` body with the discharge chain). Recommended Option A from S4 PREP §4.3 discriminant-bridge matrix: `PowerBasis.norm_gen_eq_coeff_zero_minpoly` + `integralBasis` bridge (3 + 2 LOC). Docker-build expecting `[7745/7745]` (~12s warm). Failure modes: see S4 PREP §6 R1-R5; this STATE-SYNC §4b adds R6 (NumberField hidden field) — pre-mitigated via SCAFFOLD's L48 `to_charZero := inferInstance`.

### Files modified

- `research/problems/sqrt2-minpoly-oq-03/state.md` (this file head)
- `src/data/research/problems/sqrt2-minpoly-oq-03.json`
- `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-16-s5-state-sync-post-s4-prep-merge.md` (NEW)

## Iteration 12 (researcher-3, 2026-05-15) — S4 PREP (merged 2026-05-15T18:03:22Z, PR #19253)

**Outcome**: PREP (doc-only) — bearer-pin all 12 capstone bearers at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` + 2 NEW bearer findings (`PowerBasis.norm_gen_eq_coeff_zero_minpoly`, `Algebra.norm_algebraMap`) collapsing §3.x norm chain from ~20 LOC to 3 LOC + paste-ready ~75-LOC S5 ACT capstone skeleton with 3-option discriminant-bridge matrix (§4.3).

### What was added

- `sessions/2026-05-15-s4-prep-bearer-pin-and-paste-ready-skeleton.md` (849 LOC):
  - §1 Lake SHA confirmation + lake-pinned methodology.
  - §2 12-bearer pin-verification grid (capstone, discriminant, norm, AdjoinRoot, IsTotallyReal).
  - §2.3 NEW finding: `PowerBasis.norm_gen_eq_coeff_zero_minpoly` (`Norm/Basic.lean:65`) + `Algebra.norm_algebraMap` (`Norm/Defs.lean:100-103`).
  - §4 Paste-ready ~75-LOC S5 ACT capstone skeleton.
  - §4.3 3-option discriminant-bridge matrix (A: PowerBasis-norm + integralBasis bridge / B: trace matrix on Zsqrtd 2 / C: defer to PREP-2's Zsqrtd→𝓞 iso).
  - §6 Risk register R1-R5 (3 of 5 mitigated by NEW bearers).

No edits to other files (pristine doc-only); composes cleanly with then-OPEN PR #19068.

## Iteration 11 (researcher-8, 2026-05-14) — S3 ACT SCAFFOLD

**Outcome**: ACT — created `proofs/Proofs/Sqrt2MinpolyOQ03.lean` (70 LOC,
1 strategic sorry on capstone, Docker-verified 7744 jobs).

### What I added

- `proofs/Proofs/Sqrt2MinpolyOQ03.lean`:
  - `noncomputable abbrev X_sq_sub_two : ℚ[X] := X ^ 2 - C 2`
  - `noncomputable abbrev Q_sqrt2 : Type := AdjoinRoot X_sq_sub_two`
  - `instance : Fact (Irreducible X_sq_sub_two) := ⟨Sqrt2Minpoly.irred_X_sq_sub_two⟩`
    (re-uses parent gallery's Eisenstein-via-Gauss irreducibility)
  - `instance : NumberField Q_sqrt2` constructed explicitly via
    `PowerBasis.finite (AdjoinRoot.powerBasis ...)` for the `to_finiteDimensional`
    field; `to_charZero := inferInstance` (from `Algebra ℚ`).
  - `theorem Q_sqrt2_classNumber_eq_one : NumberField.classNumber Q_sqrt2 = 1 := by sorry`
    (strategic capstone, with PREP-3..8 discharge plan documented inline).

### Docker verification

3 Docker iterations:
1. Build 1: 7744 jobs clean + 1 cosmetic `simpa→simp` linter warning + expected sorry warning.
2. Build 2: applied `simpa → simp` fix; surfaced an `unused simp arg` warning.
3. Build 3: removed unused arg; clean 7744 jobs with only the expected
   strategic-sorry warning at line 69.

### Why S3 ACT SCAFFOLD now (not yet another PREP)

The slug carried 9 merged S2 PREP sessions (S1 OBSERVE + S2 PREP-1..9), all
doc-only, accumulating a sorry-free 128-LOC design ready for S3 ACT (per
PREP-8 §6 / PREP-9 §8). Per memory rule
`feedback_researcher_docs_only_chain_silent_parent_regression`, ≥4 consecutive
doc-only PREPs without a Docker build risks silent Mathlib v4.26.0 surface
drift. Converting the design into Lean code (even with the capstone sorry) is
the natural next step — the scaffold delivers:

1. **A Docker-verified instance stack** that downstream sessions can rely on.
2. **An explicit `NumberField Q_sqrt2` instance** via `AdjoinRoot.powerBasis`,
   confirming Mathlib's `to_finiteDimensional` field synthesizes from a
   `PowerBasis` at v4.26.0 (a non-trivial instance derivation that PREP-1
   implicitly assumed but never compiled).
3. **The `Fact` discharge pattern** confirms that the parent's
   `Sqrt2Minpoly.irred_X_sq_sub_two` typechecks against `X^2 - C (2 : ℚ)`
   without a coercion-glyph mismatch.
4. **A capstone target** for the next session(s) to incrementally fill in
   per the PREP-3..8 discharge plan.

### Files modified

- `proofs/Proofs/Sqrt2MinpolyOQ03.lean` — new (70 LOC, 1 sorry, 0 axioms)
- `research/problems/sqrt2-minpoly-oq-03/state.md` — this file
- `src/data/research/problems/sqrt2-minpoly-oq-03.json` — phase OBSERVE → ACT,
  iteration 1 → 11, currentState refresh
- `research/problems/sqrt2-minpoly-oq-03/sessions/2026-05-14-s03-act-scaffold.md`
  (this iteration's session log)

### Anti-targets (this S3 ACT SCAFFOLD explicitly does NOT do)

1. **Does not implement the discriminant chain** (PREP-3/4/5/6 territory).
   The strategic sorry on the capstone defers `disc Q_sqrt2 = 8`,
   `minkowskiBound`, and `IsTotallyReal` to S4 ACT.
2. **Does not implement `IsTotallyReal Q_sqrt2`** (PREP-7/8 §4.1 has the
   25-LOC direct route via `AdjoinRoot.ringHom_ext`). Deferred to S4.
3. **Does not modify gallery `meta.json`** — slug not yet a gallery entry
   (no `src/data/proofs/sqrt2-minpoly-oq-03/` directory). Deferred until
   the capstone sorry is discharged and the proof is verified-with-0-sorries.
4. **Does not bundle deprecation fixes for unrelated proofs.** Pristine new
   `proofs/Proofs/Sqrt2MinpolyOQ03.lean`.

### Next action (S4 ACT step 1: discriminant chain)

Implement `NumberField.discr Q_sqrt2 = 8` per the PREP-4 verbatim norm chain
(via `Algebra.discr_powerBasis_eq_norm` applied to the power basis
`{1, AdjoinRoot.root}`). Estimated ~20 LOC. After that, `IsTotallyReal Q_sqrt2`
(~25 LOC, PREP-8 §4.1 direct route) and the Minkowski-bound chain
(~50 LOC, PREP-1).

### PREP chain consolidated (after S3 ACT SCAFFOLD)

| Iter | PR | Phase | Coverage |
|---:|---:|---|---|
| 1 | #18223 | S1 OBSERVE | Problem framing, tractability triage, references |
| 2 | #18340 | S2 PREP-1 | `isPrincipalIdealRing_of_abs_discr_lt` entry point |
| 3 | #18371 | S2 PREP-2 | Euclidean route via `Zsqrtd.GaussianInt` template |
| 4 | #18454 | S2 PREP-3 | `discr_powerBasis_eq_norm` high-level chain |
| 5 | #18479 | S2 PREP-4 | Verbatim norm chain (disc = 8) |
| 6 | #18526 | S2 PREP-5 | Integer-basis bridge audit + name correction |
| 7 | #18600 | S2 PREP-6 | Monogenic-Eisenstein shortcut (𝓞 = ℤ[√2]) |
| 8 | #18666 | S2 PREP-7 | `IsTotallyReal` API pin + Route C 54-LOC skeleton |
| 9 | #18710 | S2 PREP-8 | `ringHom_ext` discharge of PREP-7 §3.4; 128-LOC plan |
| 10 | #18762 | S2 PREP-9 | Lake-pinned SHA verification of PREP-8 §7 risks |
| **11** | **(this PR)** | **S3 ACT SCAFFOLD** | **70-LOC Lean file: type + instances + capstone sorry; Docker 7744 jobs clean** |

### Honest assessment

This S3 ACT SCAFFOLD does not advance the **mathematical** content beyond
PREP-1..9 — it just commits the design to Lean syntax that compiles. The
significant value-add is:

- Confirming the `AdjoinRoot.powerBasis` route to `NumberField Q_sqrt2`
  actually elaborates at v4.26.0.
- Confirming the parent `Sqrt2Minpoly.irred_X_sq_sub_two` exports
  with the right namespace + glyph form for `Fact ⟨...⟩`.
- Producing a Docker-buildable starting point so downstream sessions
  iterate on the actual capstone proof, not on imports/instance friction.

The capstone strategic sorry remains. The slug is **not yet `verified`**
(1 sorry, 0 axioms); estimated 3-4 sessions remaining to discharge per
PREP-8 §6's 128-LOC plan.

### Race-safety note

Pre-claim (2026-05-14 15:00 UTC):
- `gh pr list --search "sqrt2-minpoly-oq-03 in:title" --state open` returned 0.
- This iteration follows PREP-9 (#18762, merged 2026-05-13 11:57 UTC) by ~27h
  — well outside any race window.
- Pre-push probe will re-verify immediately before push.

Post-claim release: `release sqrt2-minpoly-oq-03` will be invoked from main
repo cwd per `feedback_researcher_claim_problem_sh_worktree_cwd_footgun.md`.
