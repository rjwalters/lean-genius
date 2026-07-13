# S6 ACT — `hasSBP_of_isDiscrete : [IsDiscrete C] → HasSBP C` (vacuous sufficient condition, build verified)

**Date**: 2026-05-14 (~15:50 UTC)
**Researcher**: researcher-9
**Mode**: ACT (Lean addition + state.md / JSON update + session note)
**Phase target**: keeps phase `ACT`; iteration 6 → 7; corpus 3 → 4 public theorems
**Status**: pristine orthogonal to S5/S5b-e PREP chain + S6 BUILD UNBLOCKER (PR #18980 merged 2026-05-14 03:01 UTC). 0 open PRs on slug at push time.

## 0. Why this S6 ACT

State.md (post S6 BUILD UNBLOCKER) flagged S6 as the "sufficient-condition
direction (Banaschewski–Brümmer 1986)" and sketched two candidate hypothesis
shapes:

- **Path (A) Literal split-mono**: `[HasSplitMonos C] → HasSBP C`, with the
  claim "a mono with a section is an iso, so this forces `Mono = Iso`,
  making SBP vacuous". State.md flagged the sketch with `sorry`.
- **Path (B) Regular-mono variant**: requires `Mathlib.RegularMono` API.

On inspecting the path (A) sketch, I found that its motivating claim is
**not literally true**: a mono `m` that also admits a retraction `r` (i.e.,
`m ≫ r = 𝟙_X`) does **not** generally become an iso. Concrete counterexample
in `Type u`: the inclusion `{0} ↪ {0,1}` is mono and admits a retraction
(any function `{0,1} → {0}`), but is not an iso. The error in the natural
proof attempt is a direction-of-mono-cancellation slip: Lean's `Mono f`
cancels equations of the form `g ≫ f = h ≫ f` (with `f` on the **right**),
not `f ≫ g = f ≫ h` (with `f` on the **left**). So
`m ≫ (r ≫ m) = m ≫ 𝟙_Y` does **not** collapse to `r ≫ m = 𝟙_Y` under
`m`'s mono-ness.

The actually-correct vacuous hypothesis is **"every morphism in `C` is
iso"**, which is Mathlib's existing `[IsDiscrete C]` typeclass (at most one
morphism between objects, with morphisms forcing object equality). Mathlib
provides `isIso_of_isDiscrete : IsIso f` for any `f` in such a category
(`Mathlib/CategoryTheory/Discrete/Basic.lean:342` at v4.26.0 pin `2df2f01`).

So the S6 ACT deliverable is `hasSBP_of_isDiscrete : [IsDiscrete C] → HasSBP C`,
a 1-tactic-line generalization of `hasSBP_Discrete` (S4 ACT) beyond
`C = Discrete α` to any `IsDiscrete` category. The deliverable also
corrects state.md's path (A) sketch and points S7 at three concrete
non-vacuous follow-ups.

## 1. Mathlib API audit at pinned SHA `2df2f01` (v4.26.0)

```bash
$ gh api -H "Accept: application/vnd.github.v3.raw" \
    "repos/leanprover-community/mathlib4/contents/Mathlib/CategoryTheory/Discrete/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    | grep -n "IsDiscrete\|isIso_of_isDiscrete"
326:/-- A category is discrete when there is at most one morphism between two objects,
327:in which case they are equal. -/
328:class IsDiscrete (C : Type*) [Category C] : Prop where
329:  subsingleton (X Y : C) : Subsingleton (X ⟶ Y) := by infer_instance
330:  eq_of_hom {X Y : C} (f : X ⟶ Y) : X = Y
333:instance Discrete.isDiscrete (C : Type*) : IsDiscrete (Discrete C) where
342:instance isIso_of_isDiscrete {X Y : C} (f : X ⟶ Y) : IsIso f :=
343:  ⟨eqToHom (IsDiscrete.eq_of_hom f).symm, by cat_disch⟩
```

The `IsDiscrete` typeclass and the `isIso_of_isDiscrete` instance are both
present at the pin. `Discrete α` automatically satisfies `IsDiscrete` via
the `Discrete.isDiscrete` instance.

No imports beyond the already-present `Mathlib.CategoryTheory.Discrete.Basic`
are required.

## 2. The shipped Lean delta

Single edit to `proofs/Proofs/SchroederBernsteinOQ01.lean`:

- Top-of-file `/- ... -/` module docstring: updated "S5 ACT (this PR)"
  framing to "S6 ACT (this PR)" with the new theorem listed, and rewrote
  "Future phases" to reflect S7+ direction.
- End-of-namespace addition (~40 LOC total: 33 docstring lines + 7 theorem
  lines):

```lean
/-! ## S6 ACT — `[IsDiscrete C] → HasSBP C` (vacuous sufficient condition)
...
-/

/-- **S6 ACT — vacuous sufficient condition for SBP**: any `[IsDiscrete C]`
category has the Schroeder-Bernstein property. Generalizes `hasSBP_Discrete`
beyond `C = Discrete α`. -/
theorem hasSBP_of_isDiscrete (C : Type*) [Category C] [IsDiscrete C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩
```

Net delta:
- **+1 public theorem** (`hasSBP_of_isDiscrete`).
- **+~40 LOC** (33 docstring + 7 theorem).
- **0 sorries, 0 axioms, 0 imports added** (uses existing `Mathlib.CategoryTheory.Discrete.Basic`).
- **0 changes to `hasSBP_Discrete`** — kept intact for backward-compat with
  the existing S4 ACT proof pattern. The new theorem coexists as a
  generalization, not a replacement.

## 3. Docker-build verification

**Pre-claim baseline** at `origin/main` (companion intact, S6 BUILD
UNBLOCKER applied):

```bash
$ ./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01
Build completed successfully (3069 jobs).
```

**Post-edit verification** with `hasSBP_of_isDiscrete` added:

```bash
$ ./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01
✔ [3069/3069] Built Proofs.SchroederBernsteinOQ01 (5.8s)
Build completed successfully (3069 jobs).
```

Same job count (3069), confirming no transitive-import expansion. Build
verified in **1 Docker iteration** (no rebuild needed; the proof typechecked
on first attempt).

## 4. Why the path (A) sketch in prior state.md was wrong

State.md path (A) claimed:

> Add `class HasSplitMonos (C : Type*) [Category C] := splitMonoOfMono :
> ∀ {X Y : C} (m : X ⟶ Y) [Mono m], SplitMono m` and prove
> `[HasSplitMonos C] → HasSBP C`. The proof is ~10 lines (a mono with a
> section is an iso), but the *informativeness* is low: the hypothesis
> forces `Mono = Iso`, making SBP vacuous.

The motivating claim "a mono with a section is an iso" is **false** for
general categories. `SplitMono m` in Mathlib provides
`retraction : Y → X` with `m ≫ retraction = 𝟙_X`. This makes `m`
mono and `retraction` a split epi, but does **not** make `m` an iso.
To make `m` an iso we additionally need `retraction ≫ m = 𝟙_Y` (so
`retraction` is a section of `m`), which the hypothesis does not provide.

Counterexample: in `Type`, the inclusion `i : {0} → {0,1}` is mono. The
function `r : {0,1} → {0}` with `r(0) = r(1) = 0` is a retraction
(`r ∘ i = id_{0}`). But `i ∘ r ≠ id_{0,1}` (since `(i ∘ r)(1) = i(0) = 0 ≠ 1`).
So `i` is not iso.

The natural proof attempt fails because Lean's `Mono f` cancels equations
of the form `g ≫ f = h ≫ f` (with `f` on the **right** of `≫`,
i.e., the "first" position in left-to-right composition order). Starting
from `m ≫ r = 𝟙_X` and trying to derive `r ≫ m = 𝟙_Y`, one might write:

```
m ≫ (r ≫ m) = (m ≫ r) ≫ m = 𝟙_X ≫ m = m = m ≫ 𝟙_Y
```

and want to cancel `m` from the LEFT to conclude `r ≫ m = 𝟙_Y`. But mono
cancellation requires `m` on the RIGHT (i.e., we need `X ≫ m = Y ≫ m ⇒
X = Y`, not `m ≫ X = m ≫ Y ⇒ X = Y`). The latter would require `m` to be
**epi**, which it isn't necessarily.

So the actually-correct vacuous hypothesis collapses *all* of `Mono`, not
just `Mono ∩ SplitMono`. This is exactly `IsDiscrete C` (or, equivalently
on the categorical-skeleton side, `IsGroupoid C` plus `Subsingleton (X ⟶ Y)`).
For the *bare* "Mono = Iso" collapse without the at-most-one-morphism
strengthening, `IsGroupoid C` suffices (every morphism is iso, but distinct
parallel morphisms are allowed). S7 path (C) is precisely this broadening.

## 5. S7 follow-up paths (recorded in state.md "Next Action")

| Path | Hypothesis | Vacuous? | Estimated LOC | Excludes TopCat? |
|---|---|---|---|---|
| (C) | `[IsGroupoid C]` | yes (Mono = Iso) | ~5 | yes (TopCat has non-iso monos like `[0,1] ↪ ℝ`) |
| (D) | "every mono is regular + split" via `RegularMono` | **no** | ~30-50 | manually verifiable via `[0,1] → (0,1)` non-regular |
| (E) | Banaschewski–Brümmer 1986 factorisation-system retraction condition | **no** | ~150-300 | per the 1986 paper |

Path (C) is the cheapest broadening (~5 LOC). Path (D) is the first
genuinely non-vacuous result. Path (E) is the long-horizon goal.

## 6. Scope guarantee

- 1 Lean file edit (`proofs/Proofs/SchroederBernsteinOQ01.lean`): +~40 LOC,
  +1 public theorem.
- 2 doc edits:
  - `research/problems/schroeder-bernstein-oq-01/state.md`: refresh
    Phase header (Since/Iteration/Last Updated), rewrite Current Focus,
    Active Approach, Next Action, Sessions, Drift / parent state.
  - `src/data/research/problems/schroeder-bernstein-oq-01.json`: refresh
    `lastUpdate`, `currentState.since`, `.iteration`, `.focus`,
    `.nextAction`, `attemptCounts.total`.
- 1 new session note (this file).
- **0 Docker job count change** (3069 → 3069).
- **0 sorries / axioms / theorem-count deltas** beyond `+1 public theorem`.
- **0 changes to existing theorems** (`hasSBP_Type`, `hasSBP_Discrete`,
  `not_hasSBP_TopCat`, `fHom`, `gHom`, `fHom_injective`, `gHom_injective`).
- **0 changes** to `meta.json`, `annotations.json`, `index.ts`, or any other
  gallery-side file.
- **0 changes** to `knowledge.md` or `problem.md`.

## 7. Race awareness

Verified at 2026-05-14 ~15:50 UTC:

```bash
$ gh pr list --search "schroeder-bernstein-oq-01 in:title" --state open --limit 5 -R rjwalters/lean-genius
# (empty)
```

Most recent merge on slug: PR #18980 (S6 BUILD UNBLOCKER) at 2026-05-14
03:01 UTC — ~13h prior. Past saturation window.

## 8. Memory traps consulted

- `feedback_researcher_docs_only_chain_silent_parent_regression.md` —
  pre-claim Docker baseline ran clean at 3069 jobs (S6 BUILD UNBLOCKER
  PR #18980 already merged on origin/main); no latent regression
  surfaced.
- `feedback_researcher_state_sync_misses_top_level_phase.md` — top.phase
  = currentState.phase = "ACT" before and after this PR; no gallery
  listings drift.
- `feedback_researcher_docker_build_cwd_must_be_worktree.md` —
  invoked `./proofs/scripts/docker-build.sh ...` from worktree CWD
  `/Users/.../researcher-9/.loom/worktrees/researcher-9` so the
  container mounted the local edits, not the main repo. Verified
  baseline + post-edit builds both succeed.
- `feedback_mechanic_edit_absolute_main_repo_path_silent_drift.md` —
  used Edit with worktree-relative paths only; verified `git status`
  shows the worktree branch ahead of origin/main, not the main repo.

## 9. Honest calibration

This S6 ACT:

- **Closes one S6 horizon item** (the vacuous-sufficient-condition
  half of the Banaschewski–Brümmer framework, with full Lean
  verification).
- **Adds a 4th theorem** to the slug's pos/neg corpus.
- **Corrects** the path (A) sketch in prior state.md (the
  `[HasSplitMonos] → HasSBP` claim was unfounded).
- **Documents** the S7 non-vacuous follow-up with three concrete
  paths and per-path LOC estimates.

This S6 ACT does **not**:

- Solve the non-vacuous sufficient condition (still open as S7).
- Provide a complete characterization of `HasSBP` (still open as S20+).
- Add new failure-witnesses beyond `not_hasSBP_TopCat` (out of scope
  per S5 ACT closure).
- Touch the parent file `Proofs/SchroederBernstein.lean` (still
  verified at 0 sorries / 0 axioms, Wiedijk #25).
- Update `src/data/proofs/schroeder-bernstein/meta.json` to list
  `SchroederBernsteinOQ01.lean` in `additionalFiles` (deferred to
  enricher / auditor).
- Add `import Mathlib.CategoryTheory.Groupoid` (would only be needed
  for S7 path (C); current S6 uses only the pre-existing
  `Mathlib.CategoryTheory.Discrete.Basic` transitive imports).

## 10. Cross-references

- **S1 OBSERVE** PR #18274 (merged 2026-05-12 20:32 UTC) — three-doc setup.
- **S2/S3 ACT** PR #18383 (merged 2026-05-12 23:48 UTC) — `hasSBP_Type` (positive in `Type u`).
- **S4 ACT** PR #18496 (merged 2026-05-13 02:53 UTC) — `hasSBP_Discrete` (positive in `Discrete α`).
- **S5 PREP / S5b / S5c / S5d / S5e PREP** PRs #18450 / #18508 / #18602 / #18655 / #18673 — chain of design + audit memos for S5 ACT.
- **S5 ACT** PR #18707 (merged 2026-05-13 08:54 UTC) — `not_hasSBP_TopCat` (negative in `TopCat.{0}`).
- **S6 BUILD UNBLOCKER** PR #18980 (merged 2026-05-14 03:01 UTC) — `noncomputable` fix on `fHom`/`gHom`.
- **STATE-SYNC** PR #18901 (merged 2026-05-13 17:24 UTC) — Current Focus + Active Approach refreshed to S5 three-instance corpus.
- **Mathlib citations** (all at pin `2df2f01` v4.26.0):
  - `IsDiscrete` typeclass + `Discrete.isDiscrete` instance + `isIso_of_isDiscrete` instance: `Mathlib/CategoryTheory/Discrete/Basic.lean:326-343`.
  - `asIso` constructor for `IsIso → Iso`: `Mathlib/CategoryTheory/Iso.lean`.
- **For S7 path (C)** (recommended next): `IsGroupoid.all_isIso` instance at `Mathlib/CategoryTheory/Groupoid.lean:119-121` (v4.26.0 pin).
