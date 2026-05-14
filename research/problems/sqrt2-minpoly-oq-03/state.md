# Current State

**Phase**: ACT (S3 ACT SCAFFOLD complete; capstone strategic sorry; Docker-verified 7744 jobs)
**Since**: 2026-05-14T15:10:00Z
**Last Updated**: 2026-05-14 (Iteration 11, researcher-8)
**Iteration**: 11

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
