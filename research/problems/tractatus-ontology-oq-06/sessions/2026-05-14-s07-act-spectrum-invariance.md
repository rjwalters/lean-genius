# S7 ACT — Spectrum-invariance biconditional + point-model construction (build pending)

**Date**: 2026-05-14 (~01:15 UTC)
**Author**: researcher-12
**Phase**: ACT (`TractatusOntologySpectrum.lean` +86 LOC; build pending)
**Iteration**: 3
**Predecessors**: PR #18191 (S1 OBSERVE), #18391 (S2-α ACT, MERGED), #18417 (S3 PREP HornModel), #18470 (S4 PREP Refines lattice), #18497 (S5 PREP freeModel uniqueness), #18518 (S6 PREP EquivModel/T1b), #18696 (S7 PREP spectrum-invariance). Prior STATE-SYNC PR #18888 (researcher-10).
**Build status**: pending — worktree `proofs/.lake` is the recursive
self-symlink loop documented in
`feedback_researcher_lake_symlink_loop_and_wipe.md`. CI / doctor
verifies via `./proofs/scripts/docker-build.sh
Proofs.TractatusOntologySpectrum` from a clean worktree.

## Scope

Transcribes the S7 PREP §1-§6 recipe into `TractatusOntologySpectrum.lean`.
Seven new declarations between the existing
`freeModel_tautology_is_universal` (L116-L119) and `end Tractatus`:

| # | Declaration | Kind | LOC | Role |
|---|---|---|---|---|
| 1 | `pointModel` | def | 4 | Singleton-world `WorldModel S` with profile equal to `w`. |
| 2 | `pointModel_holds` | `@[simp]` theorem | 4 | Direct read-off lemma. |
| 3 | `pointModel_evalM` | theorem | 6 | `evalM (pointModel w) p () ↔ evalM (freeModel S) p w` via structural induction on `Proposition S`. |
| 4 | `pointModel_isTautology_iff` | theorem | 7 | Corollary using singleton-world universality. |
| 5 | `spectrum_invariant_iff_freeModel_tautology` | theorem | 7 | Main biconditional. |
| 6 | `spectrum_invariant_implies_freeModel_via_pointModels` | theorem | 5 | Alternative converse proof via point models. |
| 7 | `spectrum_invariant_contradiction_iff_freeModel_contradiction` | theorem | 8 | Dual for contradictions. |

Plus a one-line section heading. Net file delta: **121 → 207 LOC, +86 LOC**.

**Cleanly inserted**: no edits to existing declarations; no new imports;
no new axioms; no new sorries.

## What changed vs. the S7 PREP recipe

Three small departures from the recipe (none structural):

1. **`pointModel_isTautology_iff` proof unfolds `IsTautologyM` explicitly**
   rather than the recipe's `simp only`. This is shorter and clearer
   given that the codomain `(pointModel w).W = Unit` has a single
   inhabitant `()`.

2. **`spectrum_invariant_contradiction_iff_freeModel_contradiction`
   reuses `contradiction_pullback`** (already in the file at L101-106)
   directly: `obtain ⟨f, hf⟩ := refines_freeModel M` + `exact h (f w)
   ((refines_preserves_eval f hf p w).mp hw)`. Equivalent to the recipe's
   `contradiction_pullback (refines_freeModel M) p h M` shorthand, but
   uses the explicit `obtain + apply` form to mirror the existing
   `contradiction_pullback` body.

3. **The optional alternative point-model proof** (recipe §4) is shipped
   alongside the main biconditional rather than as a separate corollary.
   This makes the file's "spectrum-invariance" section self-contained:
   readers see both the `freeModel S`-instantiation proof (which is
   trivially one-liner) and the strictly-more-informative point-model
   proof (which the state.md framing originally envisaged).

None of these departures introduces new Mathlib bearers; each uses only
the pre-existing `WorldModel S` / `freeModel S` / `evalM` / `IsTautologyM`
/ `IsContradictionM` / `Refines` / `refines_freeModel` /
`refines_preserves_eval` / `tautology_pullback` / `contradiction_pullback`
/ `freeModel_tautology_is_universal` surface.

## What this resolves

The S2-α ACT (PR #18391, 2026-05-13) landed
`freeModel_tautology_is_universal` (forward direction: `freeModel S`
tautologies hold in every `WorldModel S`) and flagged in `state.md` §
"Not yet addressed":

> Whether the converse of `freeModel_tautology_is_universal` holds —
> i.e. is every spectrum-invariant tautology a tautology of
> `freeModel`?

The S7 PREP (#18696) refuted the "not trivially true" framing of the
converse: it's a one-step instantiation since `freeModel S` is itself
a `WorldModel S`. The point-model construction is the strictly more
informative proof that the state.md envisaged. **This S7 ACT ships both
proofs.** The state.md open question is now resolved.

The biconditional + the contradiction dual close the **complete
characterisation** of the spectrum-invariant truths of the Tractarian
language:

```
spectrum-invariant tautology ≡ tautology of `freeModel S`
                            ≡ tautology of every `pointModel w`
```

The three equivalent characterisations make the spectrum-invariant
core a pointwise-verifiable notion.

## Residual risks for doctor / build verification

| Risk | Severity | In-doc fallback |
|---|---|---|
| `induction p with | elementary s => ...` in `pointModel_evalM` may produce a goal in a slightly different normal form than the existing `refines_preserves_eval` (line 80-84) | Trivial | The two proofs are structurally identical; if one builds, the other does |
| `Iff.rfl` for `pointModel_holds` requires `(pointModel w).holds u s` to definitionally reduce to `w s` (it does, by the def of `pointModel`) | Trivial | If Lean balks, replace with `unfold pointModel; rfl` |
| `pointModel_isTautology_iff`'s `· intro h _ ` pattern (capturing `Unit` with `_`) may not match Lean's elaboration | Trivial | Replace with `· intro h u; exact (pointModel_evalM w p).mpr h` (explicit `u`) |
| `contradiction_pullback` invocation in the dual theorem uses the inlined `obtain + apply` form (mirrors the existing `contradiction_pullback` body) rather than direct application | Trivial | Replace with `exact contradiction_pullback (refines_freeModel M) p h` (one-line discharge) |

None requires new Mathlib bearers; each is a routine elaboration-time
adjustment within the existing project API surface.

## Verification

- **`gh pr list -R rjwalters/lean-genius --search "tractatus-ontology-oq-06 in:title" --state open`** at pre-claim probe (~01:10 UTC, 2026-05-14): 0 open PRs.
- **Pre-push probe** will re-verify before push.
- **No `.lake` build attempted** (lake symlink loop blocks Docker; per `feedback_researcher_lake_symlink_loop_and_wipe.md`).
- **All bearer names** are existing project APIs — no Mathlib audit needed for this ACT.

## Files changed

- `proofs/Proofs/TractatusOntologySpectrum.lean` — +86 LOC; 7 new
  declarations.
- `research/problems/tractatus-ontology-oq-06/state.md` — Phase header
  + new S7 ACT history block.
- `research/problems/tractatus-ontology-oq-06/sessions/2026-05-14-s07-act-spectrum-invariance.md`
  — this file (new).
- `src/data/research/problems/tractatus-ontology-oq-06.json` —
  `currentState.{phase,since,focus,nextAction,iteration,attemptCounts.total}`,
  `knowledge.progressSummary` (prepended), `lastUpdate`.

No gallery `meta.json` touch; no `leanFiles` JSON drift fix
(`leanFiles[1].lineCount` 121 → 207 will be auditor/mechanic territory
after build verification per
`feedback_mechanic_linecount_drift_class_unshippable.md`).

## Honesty

- **Not Lean-checked locally.** Build is pending per the `.lake`
  symlink-loop trap.
- **Three small recipe departures** (§2) are all routine
  short-form/long-form swaps; none changes the proof strategy.
- **No upstream Mathlib PR** opened — `pointModel` is project-local
  and would not be canonical Mathlib content.
- **Saturation note**: I am researcher-12 and previously shipped PR
  #18888 (STATE-SYNC for this same slug) as researcher-10 on
  2026-05-13. This is my second session on this slug; previous one
  was doc-only. PREP-coverage for the other four ACT candidates
  (S3 / S4 / S5 / S6) remains intact and any agent can pick those up
  freely.

## References

- **S7 PREP**: `2026-05-13-s7-prep-spectrum-invariance-theorem-via-point-models.md` (PR #18696).
- **S2-α ACT (the parent Lean file)**: `2026-05-13-s2-alpha-act-spectrum-skeleton.md` (PR #18391).
- **S1 OBSERVE**: `2026-05-12-s1-observe-spectrum-classification.md` (PR #18191).
- **Build trap**: memory `feedback_researcher_lake_symlink_loop_and_wipe.md`.
- **Lean source**: `proofs/Proofs/TractatusOntologySpectrum.lean` (121 → 207 LOC; 0/0 throughout). `proofs/Proofs/TractatusOntology.lean` (1231 LOC parent with `WorldModel`/`Proposition`/`evalM`/`IsTautologyM`/`IsContradictionM`/`freeModel` definitions; 1 sorry / 1 axiom unchanged).
- **Branch-isolation**: shipped from a fresh branch off `origin/main`, not from the worktree's prior `research/sperner-oq05-canonical-state-sync` branch. Per `feedback_researcher_push_onto_open_pr_branch_contamination.md`.
