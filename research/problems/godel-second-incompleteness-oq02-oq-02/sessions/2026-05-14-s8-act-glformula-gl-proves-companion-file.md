# S8 ACT — `GLFormula` + `GL_proves` companion Lean file (build-verified)

**Session**: 2026-05-14, researcher-9
**Phase**: S8 ACT (first Lean code on this slug — modulo concurrent S2-α ACT PR #19037)
**Slug**: godel-second-incompleteness-oq02-oq-02
**Build status**: ✅ verified — `Proofs.GodelSecondIncompletenessOQ02GLSyntax` (2 jobs, 3.0s)
**Companion PR**: #19037 (OPEN, S2-α ACT — orthogonal; this PR is independent of impl_formula / D2 / D3)

## 0. Why now

The state.md (after the 2026-05-13 STATE-SYNC #18918) ranked S8 ACT as
**READY** and independent of S2-α: "S8 — `GLFormula` + `GL_proves` ... ~40–80
LOC, 0 axioms, low–medium build risk, **READY** — narrow, well-scoped."

The S2-α companion-file ACT (PR #19037 by researcher-12) was pushed
2026-05-14 11:33 UTC and is currently OPEN. It is **strictly orthogonal** to
S8 ACT: S2-α adds object-level `impl_formula : Formula → Formula → Formula`
plus D2/D3/impl_mp axioms on the PA side; S8 ACT introduces the modal-side
inductive type `GLFormula` and the syntactic derivability predicate
`GL_proves`. The two files share no symbols and either can land first.

Per S9 PREP #18623 §7 (audit of S8 PREP §9), the file is designed with
**zero parent-file imports** — `GLFormula` only depends on `Nat` and
core-Lean inductive machinery. The file is therefore also independent of
the parent's pre-existing v4.26.0 orphan-docstring build issue (which
PR #19037 fixes en passant); my Docker target builds with 2 jobs (just
my new file).

## 1. What this PR ships

### 1a. New file (only Lean change in this PR)

`proofs/Proofs/GodelSecondIncompletenessOQ02GLSyntax.lean` — ~95 LOC raw
(including docstring + blank lines); ~55 LOC source per S9 §7 budget.

Contents:

- `abbrev PropAtom : Type := Nat` — atom universe (countably infinite, as
  Solovay's completeness requires).
- `inductive GLFormula : Type` — 4 constructors `atom / falsum / impl / box`,
  `deriving DecidableEq, Repr`.
- `def GLFormula.not (p : GLFormula) : GLFormula := .impl p .falsum` — derived
  negation.
- `inductive PropAxiom : GLFormula → Prop` — Łukasiewicz schemas k1/k2/k3.
- `inductive GL_proves : GLFormula → Prop` — Hilbert-style derivability with
  5 constructors: `taut`, `k`, `lob`, `mp`, `nec`.

**No `@[simp]` constructor-rename lemmas** (S9 §3 recommendation).
**No subst constructor** — substitution is admissible by schema parametricity
(S8 PREP §5; Avron 1991, Kracht 1999 §3.1).

### 1b. Manifest update

`proofs/Proofs.lean` — single-line addition `import
Proofs.GodelSecondIncompletenessOQ02GLSyntax` immediately after
`import Proofs.GodelSecondIncompletenessOQ02`. Mechanical, no semantic
impact.

### 1c. Docs

This session note + state.md ACT-tracker update + JSON `currentState` /
`knowledge.nextSteps` resync. No edits to `problem.md`, `knowledge.md`,
or any prior session note.

## 2. Build verification

Command:

```bash
./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02GLSyntax
```

Result:

```
✔ [2/2] Built Proofs.GodelSecondIncompletenessOQ02GLSyntax (3.0s)
Build completed successfully (2 jobs).
[90s] Building...

=== Build succeeded ===
```

Log: `.loom/logs/researcher-9-godel2-glsyntax-build.log` (will be archived
post-commit).

**Why only 2 jobs**: the file has zero parent imports and zero Mathlib
imports — both per S9 PREP §7 recommendation. The only build artefacts
are (1) the GLSyntax `.olean` and (2) the Lake/Mathlib bootstrap target.
This is the maximally-decoupled landing path.

## 3. Design adherence to PREP chain

This ACT lands exactly the file structure recommended by S9 PREP §7
(audited refinement of S8 PREP §9):

| S9 PREP §7 / §8 acceptance criterion         | S8 ACT compliance |
|----------------------------------------------|-------------------|
| Zero parent-file imports                     | ✅ verified — no `import Proofs.*` |
| Zero Mathlib imports                         | ✅ verified — no `import Mathlib.*` |
| Name `GLFormula` (not `ModalFormula`)        | ✅ — matches S7/S8/S9 PREP consensus |
| Use Łukasiewicz schemas (Option B, not A/C)  | ✅ — `PropAxiom` has k1, k2, k3 only |
| 4 GLFormula constructors                     | ✅ — atom, falsum, impl, box |
| 5 GL_proves constructors                     | ✅ — taut, k, lob, mp, nec |
| `deriving DecidableEq, Repr` on GLFormula    | ✅ — verified by `deriving DecidableEq` survey from S9 §4 |
| No `@[simp]` constructor renames             | ✅ — both omitted per S9 §3 |
| No `subst` constructor                       | ✅ — substitution is admissible (S8 PREP §5) |
| 0 sorries, 0 new axioms                      | ✅ — strictly pure ADTs |
| Total LOC ≤ 80 (source, excluding docstring) | ✅ — ~55 LOC source, ~95 LOC with docstring |
| Update `state.md` to record S8 ACT           | ✅ — see state.md changes |

This ACT does **not** edit the parent file `GodelSecondIncompletenessOQ02.lean`,
matching S8 PREP §12 anti-targets and avoiding any merge conflict with
PR #19037 (which does edit the parent for the orphan-docstring fix).

## 4. Forward chain unblocked

| Downstream stage | Pre-S8-ACT  | Post-S8-ACT | Net change |
|------------------|-------------|-------------|------------|
| S2-α companion   | READY       | open in PR #19037 | (orthogonal) |
| S4 Löb           | gated on S2-α | gated on S2-α merge | unchanged |
| S5 Kripke (`forces`) | gated on S8 | **NOW READY** | unblocked |
| S5b PREP (ModalFormula→GLFormula rename in S5 PREP) | doc-only, doable | **NOW PRIORITY** | actionable |
| S7 arith soundness | gated on S2-α+S8 | gated on PR #19037 merge | half-unblocked |
| S10 translate    | gated on S2-α+S8 | gated on PR #19037 merge | half-unblocked |

The two ACT-prerequisite chains (S2-α and S8) are now both either landed
(S8, this PR) or in-PR (S2-α, #19037). The next sensible session is
**S5b PREP** (a doc-only rename of `ModalFormula → GLFormula` in S5 PREP)
or — once PR #19037 merges — S4 Löb ACT or S10 translate ACT.

## 5. Orthogonality and race avoidance

Race check at push time:

| Open PR on slug | Files touched | Overlap with this PR |
|-----------------|---------------|----------------------|
| #19037 (S2-α ACT) | `Proofs.lean` (+1 line), `GodelSecondIncompletenessOQ02.lean` (+2/-2), new `GodelSecondIncompletenessOQ02Companion.lean` (+227), session note, state.md, JSON | `Proofs.lean` line position (different insertion point) + state.md/JSON (different sections) |

**Merge-order considerations**:

- The two PRs both add a line to `proofs/Proofs.lean` — different lines, no
  textual overlap. The second-to-merge will rebase cleanly because the
  inserts are at adjacent but distinct positions.
- The two PRs both edit `state.md` — both add an "S2-α ACT (PR #19037)" /
  "S8 ACT (this PR)" row to the chronological session table. Whichever
  merges first will leave a `git rebase` opportunity for the second.
- The two PRs both edit the JSON `currentState` field — same mechanical
  rebase pattern.
- **No `proofs/Proofs/Godel*.lean` file conflicts**: PR #19037 adds
  `GodelSecondIncompletenessOQ02Companion.lean` and edits
  `GodelSecondIncompletenessOQ02.lean` (the parent); this PR only adds
  `GodelSecondIncompletenessOQ02GLSyntax.lean` (a new file) and touches
  `Proofs.lean`.

No conflict expected at GitHub-merge time; either PR can merge first.

## 6. Axiom and assumption ledger

This PR introduces:

| Item                  | Type      | Count |
|-----------------------|-----------|-------|
| New `axiom` declarations | object-language axioms | **0** |
| Structure-encoded assumption fields | assumption-bearing fields | **0** |
| `sorry` placeholders   | proof obligations | **0** |
| Inductive type declarations | pure ADTs | 3 (`GLFormula`, `PropAxiom`, `GL_proves`) |
| Definitions           | pure functions / abbreviations | 2 (`PropAtom` abbrev, `GLFormula.not`) |

Per CLAUDE.md §"Axiom Integrity Policy": no axioms, no structure fields
carrying mathematical assumptions. This is a pure-syntax foundation file.

## 7. Honesty notes

- **First Lean ACT on this slug** (modulo concurrent PR #19037). The 9
  merged PREPs (S1, S1b, S4–S11) were all doc-only.
- **Build is verified, not pending**. The Docker build succeeded with 2 jobs.
  No `(build pending)` suffix on the PR title.
- **No claim that this resolves Solovay**. It ships the syntactic foundation;
  downstream stages (S4 Löb, S5 Kripke, S7 arith soundness, S10 translate)
  consume `GL_proves` to build out the soundness direction. The completeness
  direction remains blocked by the opaque-`Provable` architectural flag
  per S6 PREP #18497.
- **The file deliberately has zero parent imports.** This is a tightening
  recommendation from S9 PREP §2.1–§2.2 — it decouples S8 ACT's build from
  the parent's pre-existing v4.26.0 orphan-docstring issue (which PR #19037
  fixes en passant). After PR #19037 merges, the parent will build
  cleanly; my file is already build-clean today.
- **No content-level edits to parent files or other slugs.** The only file
  this PR adds is `GodelSecondIncompletenessOQ02GLSyntax.lean`; the only
  edit outside the slug's `research/` directory is the 1-line import in
  `proofs/Proofs.lean`.

## 8. Files changed in this PR

| File                                                                                                  | Change | Notes |
|-------------------------------------------------------------------------------------------------------|--------|-------|
| `proofs/Proofs/GodelSecondIncompletenessOQ02GLSyntax.lean`                                            | new    | ~95 LOC raw / ~55 LOC source per S9 §7 spec |
| `proofs/Proofs.lean`                                                                                  | +1     | `import Proofs.GodelSecondIncompletenessOQ02GLSyntax` |
| `research/problems/godel-second-incompleteness-oq02-oq-02/sessions/2026-05-14-s8-act-glformula-gl-proves-companion-file.md` | new    | this note |
| `research/problems/godel-second-incompleteness-oq02-oq-02/state.md`                                   | modify | add S8 ACT row + update Phase + ACT readiness map |
| `src/data/research/problems/godel-second-incompleteness-oq02-oq-02.json`                              | modify | `currentState`, `knowledge.builtItems`, `knowledge.nextSteps`, `knowledge.progressSummary` |

No other files touched. No `meta.json` edits (this PR does not modify any
gallery proof entry — the GLSyntax companion file is research-side
infrastructure, not a standalone galleried proof).

## 9. References

- **S8 PREP (#18566)**: `sessions/2026-05-13-s8-prep-glformula-gl-proves-hilbert-design.md`
- **S9 PREP (#18623)**: `sessions/2026-05-13-s9-prep-s8-act-audit-and-naming-reconciliation.md`
- **S5 PREP (#18473)**: `sessions/2026-05-13-s5-prep-kripke-semantics-gl-segerberg.md` (downstream consumer of `GLFormula` via `forces`)
- **S7 PREP (#18523)**: `sessions/2026-05-13-s7-prep-arith-soundness-induction-design.md` (downstream consumer of `GL_proves` via induction)
- **S10 PREP (#18678)**: `sessions/2026-05-13-s10-prep-realization-function-design-and-s9-prep-sibling-audit.md` (downstream consumer of `GLFormula` via `translate`)
- **PR #19037** (concurrent, OPEN, researcher-12): S2-α ACT companion `impl_formula + D2/D3/impl_mp` (orthogonal to this PR)
- **Boolos, G. (1993).** *The Logic of Provability*. Cambridge University Press. Chs. 1–2.
- **Mendelson, E. (2015).** *Introduction to Mathematical Logic*, 6th ed. CRC Press. §1.6, Theorem 1.2 (Kalmár's k1+k2+k3+MP completeness).
- **Łukasiewicz, J. (1929).** *Elements of Mathematical Logic*.
- **Smoryński, C. (1985).** *Self-Reference and Modal Logic*. Springer. §1.
- **Solovay, R. (1976).** "Provability interpretations of modal logic." *Israel J. Math.* 25(3–4), 287–304.
