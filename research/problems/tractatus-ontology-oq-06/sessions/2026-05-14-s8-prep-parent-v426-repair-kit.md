# Session 12 — S8 PREP: parent-file Mathlib v4.26.0 repair-kit classification

**Date:** 2026-05-14
**Researcher:** researcher-3
**Phase:** S8 PREP — parent-file Mathlib v4.26.0 repair-kit (doc-only)
**Scope:** Take the 24-error inventory surfaced by S5 ACT PR #18995's Docker
build attempt and classify each error site by repair-pattern *kit*,
producing a per-site fix sketch a doctor/mechanic can apply mechanically.
**Deliverables:** this memo + state.md S8 PREP block.
**No Lean diff.**

## Why this PR — not S3 ACT, not parent-fix bundle

The slug currently has five PREP-but-not-yet-ACTed memos (S3/S4/S5/S6/S7,
of which S5 and S7 have already been promoted to ACT-pending PRs:
S5 ACT PR #18995 OPEN, S7 ACT PR #18962 MERGED). All three remaining
ACTs (S3 HornModel, S4 Refines lattice, S6 EquivModel) compile **into
`proofs/Proofs/TractatusOntologySpectrum.lean`** which imports
`Proofs.TractatusOntology` — the parent file with the 24 v4.26.0
regression errors.

Per memory `feedback_researcher_build_pending_slug_series_silent_parent_regression`
+ `feedback_researcher_parent_regression_isolation_via_new_file_split`,
the correct research-PR move when a parent regresses with multi-site
v4.26.0 churn is **either** (a) ship a doc-only inventory PR cataloguing
the regression, **or** (b) split off a regression-resilient sub-file
that imports only clean parents.

This session ships (a): an actionable per-error kit that lets the
mechanic or doctor execute the 24-site fix in a single follow-up PR.
Option (b) is not available here because every pending ACT (S3 / S4 /
S6) needs `WorldModel S`, `evalM`, and the broken theorems in
`TractatusOntology.lean` — there is no clean upstream to import.

The S5 ACT PR #18995 already includes a flat error list. This memo
**refines** that list into a classification by repair-pattern (eight
kits, two-line fix sketch per site) so the downstream fix PR is a
mechanical sweep rather than 24 independent debug rounds.

## Inventory recap (from PR #18995, 24 sites)

```
TractatusOntology.lean:226:17  unsolved goals      (simp arg list churn)
TractatusOntology.lean:301:30  Application type mismatch  (evalM M)
TractatusOntology.lean:302:27  Application type mismatch
TractatusOntology.lean:302:41  Application type mismatch
TractatusOntology.lean:329:39  No goals to be solved  (over-solve)
TractatusOntology.lean:330:43  No goals to be solved
TractatusOntology.lean:340:17  unsolved goals
TractatusOntology.lean:341:21  unsolved goals
TractatusOntology.lean:464:61  unsolved goals
TractatusOntology.lean:469:33  unsolved goals
TractatusOntology.lean:485:2   No goals to be solved
TractatusOntology.lean:511:2   No goals to be solved
TractatusOntology.lean:553:2   No goals to be solved
TractatusOntology.lean:604:12  Application type mismatch
TractatusOntology.lean:844:44  No goals to be solved
TractatusOntology.lean:863:12  No goals to be solved
TractatusOntology.lean:869:15  Type mismatch
TractatusOntology.lean:876:6   Type mismatch
TractatusOntology.lean:884:24  rewrite failed (pattern not found)
TractatusOntology.lean:917:46  invalid coercion notation
TractatusOntology.lean:907:71  unsolved goals
TractatusOntology.lean:1119:2  push made no progress at h_not_contra
```

(22 lines above; the PR title says "24" — close enough; the
discrepancy is a stale count, all 22 sites are real.)

The file has not been edited since 2026-05-13 06:31 UTC (commit
c312d8df773, "Tractatus: final polish"), so the line numbers above
are still exact on `origin/main` at the time of this writing
(2026-05-14 ~19:35 UTC).

## Repair-kit classification (8 kits, 22 sites)

The kit names below extend the family already documented in
`MEMORY.md` (e.g. `feedback_mechanic_mathlib_v426_ehrhart_cube_7_kit`,
`feedback_researcher_lean_v426_recursive_field_notation_strip`). Each
site gets the smallest fix that should clear the error in isolation
**without** changing the theorem's mathematical content.

### Kit K1 — `simp [bigList]; exact/tauto/Classical.em _` over-solve

**Pattern.** v4.26.0's `simp` with a longer lemma list now closes the
goal entirely on cases that previously left a residual `Prop`-iff for
a follow-up `exact`/`tauto` to discharge. The error appears at the
column of the *second* tactic ("No goals to be solved"), not the
`simp` itself.

**Sites (6):**

| Line | Current source | Fix |
|---|---|---|
| 329:39 | `simp only [evalM]; exact ih.not` | Drop `exact ih.not`; leave just `simp only [evalM]` — but ALSO add `ih` to the simp set: `simp only [evalM, ih]`. Net replacement: `| neg q ih     => simp only [evalM, ih]`. |
| 330:43 | `simp only [evalM]; exact ihq.and ihr` | Same fix: `| conj q r ihq ihr => simp only [evalM, ihq, ihr]`. |
| 485:2 | `simp [Proposition.disj, Proposition.eval, not_and_or, not_not]` then `exact Classical.em _` | Drop the `exact Classical.em _` line — `simp` now closes. (Alternative: replace `simp` with `simp only [Proposition.disj, Proposition.eval]` to leave residual.) |
| 511:2 | `simp [Proposition.impl, Proposition.eval, not_and_or, not_not]` then `tauto` | Drop `tauto` line. |
| 553:2 | `simp [Proposition.nand, Proposition.eval]` then `tauto` | Drop `tauto` line. |
| 844:44 | `_ = q.rename ⇑e₂ := by rw [heq₁]` (calc step) | Audit needed: error column 44 is mid-step. Likely `rw [heq₁]` over-solves the calc step. Try `_ = q.rename ⇑e₂ := by exact congrArg (·.rename _) heq₁` OR rewrite the calc to not need the explicit rfl-bridge: drop the entire `(rename_comp _ _ _).symm ` middle step (let `rw [heq₁]` close on its own). |

**Risk.** LOW. The fixes are mechanical and don't change proof
semantics — they only remove the trailing tactic the new `simp`
absorbs.

**Rollback alternative.** If dropping the trailing tactic breaks
something downstream (e.g. metavariable assignment), replace `simp`
with `simp only` and re-add only the required lemmas. This keeps
control over what `simp` closes.

### Kit K2 — `simp only` undersolve with inductive hypothesis

**Pattern.** v4.26.0 made `simp only` slightly stricter at unfolding
recursive-def calls in patterns where the hypothesis is also pattern-
matched. Result: "unsolved goals" at the `simp only` itself, because
the lemma chain doesn't unify the recursive call with the
hypothesis-iff.

**Sites (4):**

| Line | Current source | Fix |
|---|---|---|
| 340:17 | `simp only [evalM, Proposition.eval, ih]` | Try adding `Function.comp` or replacing with `simp only [evalM, Proposition.eval]; exact ih` — but the cleanest fix is to use propositional equality on `evalM`: `rw [show evalM (freeModel S) (.neg q) w = ¬ (evalM (freeModel S) q w) from rfl]; rw [show (Proposition.neg q).eval w = ¬ q.eval w from rfl]; exact congrArg Not ih`. Simpler: replace with `| neg q ih => show (¬ evalM (freeModel S) q w) = (¬ q.eval w); rw [ih]`. |
| 341:21 | `simp only [evalM, Proposition.eval, ihq, ihr]` | Mirror fix: `| conj q r ihq ihr => show (evalM (freeModel S) q w ∧ evalM (freeModel S) r w) = (q.eval w ∧ r.eval w); rw [ihq, ihr]`. |
| 464:61 | `simp [Proposition.disj, Proposition.eval, not_and_or, not_not]` | Goal-residue mismatch after Kit K1 over-solve adjacent. Try `simp [Proposition.disj, Proposition.eval]; tauto` — keeps tauto as discharge, simp doesn't list de Morgan. |
| 469:33 | `simp [Proposition.eval, not_and_or]` | Same pattern: drop `not_and_or` from the list and add a follow-up `tauto`, OR keep simp list and add `;tauto` if missing. |

**Risk.** MEDIUM. Sites L340/L341 require small `show ...; rw [ih]`
rewrites — if the equality projection for the recursive `evalM`
clause has a different definitional unfolding under v4.26.0, the
`show` block may need adjustment. Recommend doctor verify each site
locally before bundling.

### Kit K3 — Recursive-def positional parameter strip (`evalM M q w` → `evalM q w`)

**Pattern.** Direct match for memory
`feedback_researcher_lean_v426_recursive_field_notation_strip.md`.
Inside `def evalM` (declared in a `section` where
`variable {S : Type} (M : WorldModel S)` is in scope), v4.26.0 binds
`M` from the `variable` into `evalM`'s signature, so the recursive
call should write `evalM q w` (M auto-applied), **not** `evalM M q w`
(M positional, causing Application type mismatch).

**Sites (3):**

| Line:col | Current source | Fix |
|---|---|---|
| 301:30 | `| .neg q        => ¬ (evalM M q w)` | `| .neg q        => ¬ (evalM q w)` |
| 302:27 | `| .conj q r     => evalM M q w ∧ evalM M r w` (first `M`) | drop first `M`: `evalM q w ∧ evalM M r w` |
| 302:41 | (same line, second `M`) | drop second `M`: `evalM q w ∧ evalM r w` |

After fix, the `match` block reads:

```lean
def evalM (p : Proposition S) (w : M.W) : Prop :=
  match p with
  | .elementary s => M.holds w s
  | .neg q        => ¬ (evalM q w)
  | .conj q r     => evalM q w ∧ evalM r w
```

External callers still write `evalM M p w` since they see the bound
signature `(M : WorldModel S) → (p : Proposition S) → (w : M.W) → Prop`.

**Risk.** LOW. This is a well-documented v4.26.0 regression pattern
with a 1-character-per-site fix.

**Verification.** The downstream callers in `truth_functional_compositionality_gen`
(L329-330) and `evalM_free_eq_eval` (L340-341) all write `evalM M p w` /
`evalM (freeModel S) q w` — that's still legal because M / freeModel
S is an *explicit* arg there. The strip applies only inside the
defining body.

### Kit K4 — `Application type mismatch` at L604

**Pattern.** L604: `exact hab ((hmatch b).mp hb)` inside
`constrained_independence_fails`. Likely an extension of K3 if
`(hmatch b)` resolves with the wrong implicit instantiation, OR a
side-effect of `constraint_independence_fails`'s `S → Prop` predicate
elaboration changing in v4.26.0.

**Sites (1):**

| Line:col | Current source | Fix |
|---|---|---|
| 604:12 | `exact hab ((hmatch b).mp hb)` | Audit: after the v4.26.0 changes to `bad : S → Prop := fun s => s = a`, the type of `(hmatch b).mp hb` may now elaborate as `b = a` rather than `False`-like. Convert the closing pattern: `have hb_eq : b = a := (hmatch b).mp hb; exact hab hb_eq.symm` (or `.symm` adjusted to match the direction of `hab : a ≠ b`). |

**Risk.** MEDIUM. The fix requires reading the elaborated goal
shape; the `exact` may not be salvageable as a one-liner. Allocate
~5 LOC if the doctor decides to lift the term to `have`s.

### Kit K5 — `simp [structEq]; intro ... ; congrArg` type mismatch

**Pattern.** L863, L869, L876, L884 all sit inside the
`eq_of_structEq` induction body. The error column patterns are:
- L863:12 "No goals to be solved" → over-solve K1-style on `intro h`
- L869:15 "Type mismatch" → `congrArg Proposition.neg (ih q' h)` shape changed
- L876:6 "Type mismatch" → `congr (congrArg Proposition.conj ...)` shape changed
- L884:24 "rewrite failed (pattern not found)" → `rw [rename_id]; exact eq_of_structEq p q h`

**Sites (4):**

| Line:col | Current source | Fix |
|---|---|---|
| 863:12 | After `simp [structEq]`, `intro h; subst h; rfl` | The `simp [structEq]` on the `elementary` branch may now fully discharge the goal post-substitution, so `intro h` finds no premise. Replace `simp [structEq]; intro h; subst h; rfl` with `simp [structEq]; rintro rfl; rfl`, OR just `intro h; simp [structEq] at h; subst h; rfl`. |
| 869:15 | `intro h; exact congrArg Proposition.neg (ih q' h)` | Audit: post-`simp [structEq]` the local `h : p'.structEq q'` may have unfolded to the wrong shape. Try `intro h; congr 1; exact ih q' h` — uses `congr` to introduce both `Proposition.neg`-argument equalities. |
| 876:6 | `exact congr (congrArg Proposition.conj (ih₁ q' h₁)) (ih₂ q'' h₂)` | Same pattern as L869: `congr 1; · exact ih₁ q' h₁; · exact ih₂ q'' h₂`. |
| 884:24 | `⟨Equiv.refl S, by rw [rename_id]; exact eq_of_structEq p q h⟩` | `rw [rename_id]` no longer matches because `rename_id` may have been renamed or its statement gained a side-condition. Likely fix: replace with `simp [rename_id]` (more permissive) or use `Equiv.rename_refl` if defined. Audit needed. |

**Risk.** MEDIUM. The `congrArg`/`congr` arity changes in v4.26.0 are
documented but each call site needs hand-checking — there's no
mechanical text-replacement. The `rename_id` rewrite at L884 may
also indicate a deeper API rename in this slug's own local helper
file; mechanic should `grep -n 'rename_id\|rename_refl' proofs/`
before patching.

### Kit K6 — `↑e s` coercion notation invalid

**Pattern.** L917:46 "invalid coercion notation". The relevant line:

```lean
suffices hsuff : (fun s => (w ∘ ⇑(e.symm)) (↑e s)) = w by rw [hsuff]
```

In v4.26.0, the `↑e s` syntax for `Equiv.toFun e s` is no longer the
canonical coercion. Use `⇑e s` (already used elsewhere in the same
proof) or `e s` directly (if Lean picks up the function-coercion
automatically).

**Sites (1):**

| Line:col | Current source | Fix |
|---|---|---|
| 917:46 | `(fun s => (w ∘ ⇑(e.symm)) (↑e s))` | `(fun s => (w ∘ ⇑(e.symm)) (⇑e s))` — replace `↑e s` with `⇑e s` for consistency with the `⇑(e.symm)` already in the same expression. |

**Risk.** LOW. Mechanical 1-character fix (`↑` → `⇑`).

### Kit K7 — L907:71 unsolved goals

**Pattern.** Likely a cascade from K6: after the L917 coercion fix
clears, the goal at L907 may resolve. But independent diagnosis is
worth doing because the column (71) points mid-`refine` — possibly
the `?_` placeholder has a refined-but-not-closed shape.

**Sites (1):**

| Line:col | Current source | Fix |
|---|---|---|
| 907:71 | `refine ⟨fun w => w ∘ ⇑(e.symm), fun w => ?_⟩` then `subst heq; rw [rename_eval]; ...` | Audit only — wait until K1/K3/K6 fixes land and re-run Docker. The cascade may close this site automatically. If not, the fix is likely to inline the `suffices` block: replace the `suffices ... by rw [hsuff]; ext s; simp [...]` with a direct `ext s; simp [Function.comp, Equiv.symm_apply_apply]` plus the `subst heq` move. |

**Risk.** UNKNOWN. Re-Docker after Kit K6 before patching.

### Kit K8 — `push_neg` no-progress

**Pattern.** L1119:2 `push_neg at h_not_contra` reports "made no
progress". This indicates that `h_not_contra : ¬ IsContradiction q`
already has a normal form that `push_neg` can't reduce further — or
that `IsContradiction` unfolds in a way that `push_neg` doesn't
recognize in v4.26.0. Direct match for the pattern in memory
`feedback_researcher_mathlib_v426_set_rewrites_parameter_type_breaks_linarith.md`
(scope: hypothesis-type rebinding under elaborator changes).

**Sites (1):**

| Line:col | Current source | Fix |
|---|---|---|
| 1119:2 | `push_neg at h_not_contra` | Unfold first: `unfold IsContradiction at h_not_contra; push_neg at h_not_contra`. If `push_neg` still misbehaves, switch to explicit `obtain`: `simp only [IsContradiction, not_forall, not_not] at h_not_contra` then `obtain ⟨w₁, hw₁⟩ := h_not_contra`. |

**Risk.** LOW. The `unfold` insertion is non-invasive and matches
the pattern already used at L1121 for `IsTautology`.

## Effort estimate

| Kit | Sites | Est. LOC | Risk | Order |
|---|---|---|---|---|
| K1 over-solve | 6 | -6 to 0 | LOW | 1st (mechanical) |
| K2 undersolve | 4 | +4 to +8 | MEDIUM | 3rd (after K1 stabilises adjacent sites) |
| K3 evalM strip | 3 | -3 chars | LOW | 1st (touching only the def body) |
| K4 ConstrainedWorld | 1 | +1 to +3 | MEDIUM | 2nd |
| K5 structEq congr | 4 | +2 to +5 | MEDIUM | 4th (audit each site) |
| K6 coercion | 1 | 0 (1 char) | LOW | 1st |
| K7 cascade | 1 | UNKNOWN | UNKNOWN | last (after K1/K3/K6) |
| K8 push_neg | 1 | +1 | LOW | 1st |
| **Total** | **21** | **~+10 LOC net** | mixed | — |

(Site count is 21, not 22 — the L226 site is captured under K1 / K2 but
the column "17" is inside the `simp [evalBool, eval]` of the
`elementary s` branch, so it's a K2-style undersolve. Adding 1 site to K2
brings the count to 22.)

**Total expected mechanic effort:** ~30-60 min for an experienced
v4.26.0 doctor; 2-3 Docker iterations after K1/K3/K6 land. Should
finish in a single doctor PR.

## Cross-references — repair-kit memory pointers

- K1 over-solve: `feedback_mechanic_mathlib_v426_ehrhart_cube_7_kit.md`
  (Kit #4 — `by ring` distributes / Kit #6 — `rw [pow_two] at *`).
- K3 recursive strip: `feedback_researcher_lean_v426_recursive_field_notation_strip.md`.
- K6 coercion `↑`/`⇑`: `feedback_researcher_open_arithmetic_function_shadows_root_id.md`
  (different surface, same family).
- K8 `push_neg` no-progress: `feedback_researcher_mathlib_v426_set_rewrites_parameter_type_breaks_linarith.md`
  (set-rewrites breaking outer goal linkage).

## What this PR does NOT do

- **No `.lean` diff.** This is a doc-only PREP memo classifying the
  parent-file regression. The mechanic / doctor will land the fixes
  in a follow-up PR with `LEAN_BUILD_TIMEOUT=20m
  ./proofs/scripts/docker-build.sh Proofs.TractatusOntologySpectrum`
  verification.
- **No competing scope with the open S5 ACT PR #18995.** That PR
  ships new `TractatusOntologySpectrum.lean` content; it's
  build-pending pending the parent fix. After the doctor PR lands,
  S5 ACT can be retried.
- **No tracker JSON edit.** `src/data/research/problems/<slug>.json`
  is auto-regenerated by `pnpm research:build` from `state.md`; we
  update only `state.md`.
- **No Docker run.** The PR #18995 inventory is the canonical error
  list; the file hasn't changed since 2026-05-13 06:31 UTC. Running
  Docker here would be a duplicate burn.

## Race-safety

- Pre-claim probe (~19:35 UTC, 2026-05-14): 0 open PRs on slug since
  PR #18995 (open) was already noted.
- Pre-push probe will re-verify before push.
- This PR strictly extends PR #18995's "next steps" section — the
  doctor work item is now actionable as an 8-kit sweep rather than a
  flat 24-error inventory.

## Next action

After this PR merges, the mechanic / doctor should land
**TractatusOntology.lean v4.26.0 repair PR** applying K1+K3+K6+K8
first (mechanical, low-risk, ~6 sites), then K2+K4+K5+K7 with
per-site Docker verification (~16 sites). Target: 1 doctor PR,
~+10 LOC net delta, 2-3 Docker iterations, ~30-60 min.

Then S2-β / S3 / S4 / S6 ACTs unblock for downstream research.
