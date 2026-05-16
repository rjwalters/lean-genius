# S12 PREP — G6 companion-file pivot pre-staging (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-3
**Type**: Doc-only PREP (no Lean edits, no knowledge.md edits).
**Scope**: Pre-stage the G6 companion-file pivot path (per S11 STATE-SYNC §6
conditional recommendation) with paste-ready Lean, new bearer pins, build-risk
inventory, and an explicit drain-wave trigger tracker — *without* yet pulling
the trigger. PR #18011 (G6 algebraic Unit-bridge) remains the canonical path
until 2 of 2 drain waves have passed without rebase activity.

## §1 Why this PREP exists

S11 STATE-SYNC (#19439, merged 2026-05-16T04:39:27Z) refreshed `state.md`
to iteration 11 and the ACT-readiness gate to 7/8 GREEN (only G6 RED via
the still-open PR #18011). §6 of S11 STATE-SYNC introduced a **conditional
pivot recommendation**: *"if PR #18011 remains stuck for ≥ 2 additional
drain waves … ship G6 as a fresh companion file
`BrouwerFixedPointOQ01OQ02G6.lean` paralleling G7/G8."*

Current drain-wave trigger state at the time of this PREP:

| Drain wave # since last #18011 activity | When | Status |
|----|----|----|
| 1 | The wave that landed #19114 (G8/G9, 2026-05-15T22:58Z) and #19193 (S10 coord, drain wave) | **passed** without rebase activity on #18011 |
| 2 | NEXT deployer drain wave | **not yet observed** |

PR #18011 reconfirmation at this PREP's authoring time:

```
gh pr view 18011 --repo rjwalters/lean-genius --json state,mergeable,mergeStateStatus,updatedAt
→ {state: OPEN, mergeable: CONFLICTING, mergeStateStatus: DIRTY, updatedAt: 2026-05-12T08:58:14Z}
```

`updatedAt` is unchanged (3.83 days stale, no rebase push, no comment).

This means the trigger is **1 of 2 waves passed** — not yet at the pivot
threshold. The right S12 move is therefore **pre-staging** of the
companion-file pivot, not the pivot itself: assemble the paste-ready Lean,
pin the new bearer files, and inventory the build risk, so that *if* the
2nd drain wave passes without rebase activity, the resulting S13 ACT is a
1-paste + 1-Docker step. Conversely, *if* the 2nd drain wave brings a
rebase of #18011, this PREP's content is harmless (the companion file
just isn't created) and the only cost is one doc-only PR.

This is a *ready-the-alternative* PREP, not a pivot.

## §2 On-disk reality on current main (sanity recheck)

Unchanged since S11 STATE-SYNC §2:

```
proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean        462 LOC   14 theorems   4 axioms   0 sorries
proofs/Proofs/BrouwerFixedPointOQ01OQ02G7.lean       94 LOC    2 theorems   0 axioms   0 sorries
proofs/Proofs/BrouwerFixedPointOQ01OQ02G8.lean      134 LOC    2 theorems   0 axioms   0 sorries
                                                    ───────  ─────────────  ─────────  ────────
                                                    690 LOC   18 theorems   4 axioms   0 sorries
```

Companion-file naming caveat (carried forward from S11 §2): the file named
`…G8.lean` contains *both* G8 (`map_section_of_section` at L96) and G9
(`isZero_of_section_into_isZero` at L117) by design — both are pure category
theory and share `Functor.Basic` + `Limits.Shapes.ZeroObjects` imports. If a
G6 companion lands at the threshold trip, the natural file name remains
`BrouwerFixedPointOQ01OQ02G6.lean` (single bridge, distinct import set: pure
algebra over `AddMonoidHom` + `Subsingleton`, no category theory).

## §3 Paste-ready Lean for `BrouwerFixedPointOQ01OQ02G6.lean`

The Part-VI Lean content extracted from PR #18011 lives inside the *main file*
namespace `BrouwerOQ01OQ02`, where the closing `no_split_through_subsingleton`
proof calls `id_Z_ne_zero` (main file line 168). When extracted into a
companion file, the companion either (a) re-states `id_Z_ne_zero` locally to
remain self-contained, or (b) imports the main file (which would defeat the
purpose of conflict-isolation). Option (a) is followed below — the re-stated
local fact is renamed `id_Z_ne_zero_g6` to avoid any future namespace clash
with the main file once both land.

Three Part-VI `example` proofs (lines 282–305 of #18011's main-file diff)
verify that Part-V Unit-specific lemmas follow as one-line specializations
of the new general lemmas. Those examples reference Part-V theorem names
(`unique_hom_to_unit`, `unique_hom_from_unit_is_zero`,
`id_Z_not_factored_through_unit`) which live in the main file. The
companion-file extraction **drops the three cross-reference examples**;
they belong in the eventual S13b STATE-SYNC follow-on that re-adds the
specializations as `example`s in the main file (a 1-line wiring step).

The companion file (paste-ready, ~85 LOC including header docstring,
zero new axioms, four named theorems, namespace `BrouwerOQ01OQ02`):

```lean
/-
  Brouwer Fixed Point OQ-01-OQ-02-OQ-03-OQ-02: G6 companion file

  G6 algebraic Unit-bridge generalization — extracted from PR #18011's
  Part VI to a standalone companion file paralleling G7
  (`BrouwerFixedPointOQ01OQ02G7.lean`) and G8/G9
  (`BrouwerFixedPointOQ01OQ02G8.lean`).

  Generalizes the three Part-V Unit-specific lemmas
  (`unique_hom_to_unit`, `unique_hom_from_unit_is_zero`,
  `comp_through_unit_is_zero`) to arbitrary subsingleton additive
  commutative groups (the real shape of `H_{n-1}(B^n)` in the
  singular-homology setting), and consolidates the algebraic obstruction
  in `no_split_through_subsingleton`.

  No new imports beyond `Mathlib.Algebra.Group.Hom.Basic` and the integer
  dependencies that AddMonoidHom + the integer-Zero instance already pull
  transitively. No new axioms. Pure algebra.

  Net theorem delta vs. main file: +4 (no_split_through_subsingleton and
  three named helpers in namespace `BrouwerOQ01OQ02`). Net axiom delta: 0.

  Companion-file (not inline) per S11 STATE-SYNC §6 pivot recommendation:
  conflict isolation vs. the unrebased PR #18011, parallel to G7/G8/G9.
-/

import Mathlib.Algebra.Group.Hom.Basic

namespace BrouwerOQ01OQ02

/-- Local re-statement of the main file's `id_Z_ne_zero` (line 168) to keep
    this companion file self-contained. Renamed with a `_g6` suffix to avoid
    namespace clash should both files be open in the same scope. -/
theorem id_Z_ne_zero_g6 : (AddMonoidHom.id ℤ) ≠ (0 : ℤ →+ ℤ) := by
  intro h
  have := AddMonoidHom.ext_iff.mp h 1
  simp [AddMonoidHom.id_apply] at this

/-- Any AddMonoidHom into a subsingleton additive group is uniquely determined.
    Generalizes `unique_hom_to_unit` from `Unit` to any subsingleton target. -/
theorem unique_hom_to_subsingleton
    {G H : Type*} [AddCommGroup G] [AddCommGroup H] [Subsingleton H]
    (φ₁ φ₂ : G →+ H) : φ₁ = φ₂ := by
  apply AddMonoidHom.ext; intro x
  exact Subsingleton.elim _ _

/-- Any AddMonoidHom out of a subsingleton additive group is the zero map.
    Generalizes `unique_hom_from_unit_is_zero` from `Unit` to any
    subsingleton source. -/
theorem hom_from_subsingleton_is_zero
    {G H : Type*} [AddCommGroup G] [Subsingleton G] [AddCommGroup H]
    (ψ : G →+ H) : ψ = 0 := by
  apply AddMonoidHom.ext; intro x
  have hx : x = (0 : G) := Subsingleton.elim _ _
  rw [hx, ψ.map_zero, AddMonoidHom.zero_apply]

/-- Any composition `ℤ →+ G →+ ℤ` through a subsingleton group `G` is the
    zero map. Generalizes `comp_through_unit_is_zero` from `Unit` to any
    subsingleton intermediate group. -/
theorem comp_through_subsingleton_is_zero
    {G : Type*} [AddCommGroup G] [Subsingleton G]
    (φ : ℤ →+ G) (ψ : G →+ ℤ) : ψ.comp φ = 0 := by
  rw [hom_from_subsingleton_is_zero ψ, AddMonoidHom.zero_comp]

/-- **G6 algebraic bridge**: The identity `AddMonoidHom.id ℤ` cannot factor
    through any subsingleton additive group. Once ACT-D-3 EXEC discharges the
    topological side, the algebraic contradiction lands directly through this
    lemma, independent of the specific carrier-type choice. -/
theorem no_split_through_subsingleton
    {G : Type*} [AddCommGroup G] [Subsingleton G]
    (φ : ℤ →+ G) (ψ : G →+ ℤ) :
    ψ.comp φ ≠ AddMonoidHom.id ℤ := by
  intro h
  have hzero : ψ.comp φ = 0 := comp_through_subsingleton_is_zero φ ψ
  rw [hzero] at h
  exact id_Z_ne_zero_g6 h.symm

end BrouwerOQ01OQ02
```

Net LOC ≈ 85 (vs. the +111 LOC inline diff of PR #18011, which includes
3 cross-reference examples + Part-VI section banner + main-file Summary
bump from "13 theorems" → "17 theorems").

## §4 Bearer pins for G6 companion-file imports (NEW, in addition to S11 §4)

The four S11 STATE-SYNC §4 bearer files (G7/G8/G9/sphere) remain pinned. The
G6 companion file's import surface adds **one** new bearer to verify at the
pinned rev:

| Bearer file | File SHA at `2df2f0150c` | Used for |
|----|----|----|
| `Mathlib/Algebra/Group/Hom/Basic.lean` | `48295b4d989d7c0e51f32c6df843dea8cb693283` | `AddMonoidHom`, `AddMonoidHom.ext`, `AddMonoidHom.comp`, `AddMonoidHom.zero_comp`, `AddMonoidHom.zero_apply`, `AddMonoidHom.id`, `AddMonoidHom.id_apply` (most generated via `@[to_additive]` from `MonoidHom`) |
| `Mathlib/Algebra/Group/Hom/Defs.lean` | `2221e5f95d12f7c1be23fa71095abb394f528c77` | underlying `AddMonoidHom` structure + `ext_iff` |
| `Mathlib/Logic/Nontrivial/Defs.lean` | `f05af5e8c19c359f7f9f8b194b3120de78e91301` | (already pinned via G7) — not strictly needed by G6 (no Nontrivial / Subsingleton elim here uses `Logic/Basic`) |

`Mathlib.Algebra.Group.Hom.Basic` transitively imports `…Hom.Defs` and the
integer Zero/AddCommGroup instances, so a single `import` line is sufficient.

Verification queries (executed at PREP authoring time, returning the SHAs
above):

```
gh api /repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Group/Hom/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.sha'
→ 48295b4d989d7c0e51f32c6df843dea8cb693283

gh api /repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Group/Hom/Defs.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.sha'
→ 2221e5f95d12f7c1be23fa71095abb394f528c77
```

Mathlib `v4.26.0` / `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is the
canonical pin in `proofs/lake-manifest.json` (unchanged from S11 STATE-SYNC).

## §5 Build-risk inventory

The G6 companion is pure algebra (single `Mathlib.Algebra.Group.Hom.Basic`
import). Risk profile vs. the G7 and G8/G9 companions:

| Bridge | Bearer module count | Distinct from main file? | Job-count estimate |
|----|----|----|----|
| G7 (`…G7.lean`) | 4 (`Grp.Basic`, `Grp.Zero`, `ZeroObjects`, `Nontrivial.Basic`) | strict subset of main | 718 jobs (verified) |
| G8/G9 (`…G8.lean`) | 2 (`Functor.Basic`, `ZeroObjects`) | strict subset of main | 627 jobs (verified) |
| G6 (`…G6.lean`) | 1 (`Group.Hom.Basic`) | strict subset of main | **expected ~600 jobs** (lower bound on category-theoretic companions; pure algebra over a single Hom basic module) |

Risk classes (G6-specific):

1. **F1 (`AddMonoidHom.ext` unification)** — `apply AddMonoidHom.ext;
   intro x` is the canonical proof opener for AddMonoidHom equalities. Verified
   used identically in main file line 161 (`comp_through_unit_is_zero`) and
   PR #18011 Part-VI lines 270, 277. **Risk: very low.**
2. **F2 (`Subsingleton.elim _ _` instance discoverability)** — Lean must find
   the `Subsingleton H` instance from the `[Subsingleton H]` type-class binder.
   Standard pattern; both Part-V `unique_hom_to_unit` (line 153) and Part-VI
   (line 273) use it. **Risk: very low.**
3. **F3 (`ψ.map_zero` vs. `AddMonoidHom.map_zero ψ`)** — both spellings exist
   in v4.26.0. Part-V `unit_hom_sends_zero_to_zero` (main file line 155) uses
   `ψ.map_zero` form. **Risk: very low.**
4. **F4 (`AddMonoidHom.zero_comp` vs. `MonoidHom.zero_comp`)** — generated
   via `@[to_additive]` from the multiplicative version. Part-VI proof of
   `comp_through_subsingleton_is_zero` uses it (PR #18011 line 280) and
   builds fine in #18011's local build. **Risk: very low.**
5. **F5 (universe polymorphism)** — `{G H : Type*}` is universe-polymorphic,
   matching Part-VI signature exactly. The downstream call site in
   `no_retraction_singular_homology` (main:line ~420) currently uses
   `Unit : Type 0`; a future S13b will adapt the call to instantiate at the
   homology carrier's universe. **Risk: nil at G6-companion compile time
   (irrelevant — the lemma is polymorphic and accepts any universe).**

Fallback recipes (if any of F1–F5 misfires at ACT time):

- F1 fallback: `AddMonoidHom.ext (fun x => ?_)` (functional spelling).
- F2 fallback: `obtain rfl := Subsingleton.elim x y` for explicit named
  Subsingleton elimination.
- F3 fallback: `simp only [map_zero]` (the typeclass-driven form).
- F4 fallback: spell explicitly `AddMonoidHom.zero_comp φ` vs.
  `(0 : G →+ ℤ).comp φ = 0` via `rfl` + `funext`.
- F5 fallback: drop universe polymorphism, fix `{G : Type}` — would still
  compose with the homology call site at `Type 0`.

**Estimated probability of clean first-iter build**: ≈ 92% (G7 hit clean on
first try; G8/G9 hit clean on first try; G6 is strictly simpler than either).

## §6 Drain-wave trigger tracker (for the eventual S13 ACT decision)

S11 STATE-SYNC §6 stated: *"if PR #18011 remains stuck for ≥ 2 additional
drain waves, an alternative path is to ship G6 as a fresh companion file."*

Concrete trigger ledger:

| Drain wave | When | #18011 `updatedAt` change | Triggers companion-file pivot? |
|----|----|----|----|
| Baseline | S11 STATE-SYNC merge (2026-05-16T04:39:27Z) | unchanged at 2026-05-12T08:58:14Z (3.83d stale) | n/a |
| Wave +1 | Deployer wave that landed #19439 (i.e., the wave we just observed; in scope of S11) | unchanged | n/a (this is the "0/2" baseline post-S11) |
| Wave +2 | NEXT deployer drain after this PREP merges | **OBSERVED-TBD** | If `updatedAt` unchanged → wave 1/2; companion pivot still NOT triggered |
| Wave +3 | Deployer drain after wave +2 | **OBSERVED-TBD** | If `updatedAt` unchanged → wave 2/2; **companion pivot ACTIVATED**, ship S13 ACT |

In other words: a researcher claiming this slug at *S13 author time* MUST
recheck `gh pr view 18011 --repo rjwalters/lean-genius --json updatedAt` and
count drain waves that have completed since *this* PREP's merge against
S11 STATE-SYNC's merge timestamp. If `updatedAt` has changed (rebase push,
comment, or close), the companion pivot is **cancelled** and the standard
S9 ACT-D-3 EXEC plan resumes (with the rebased #18011 supplying G6 inline).

Conservative bias: prefer the rebase outcome. Pivoting via companion file
duplicates the G6 lemma chain (one in `…G6.lean`, one inline once #18011
merges) until a STATE-SYNC consolidates. The companion is the *fallback*,
not the preferred path.

## §7 What this PREP does NOT do

- Does not create `proofs/Proofs/BrouwerFixedPointOQ01OQ02G6.lean`. The
  paste-ready Lean above is solely a textual artifact in this sessions/ memo.
- Does not edit `proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean`,
  `…G7.lean`, `…G8.lean`. Zero Lean changes.
- Does not edit `problem.md` or `knowledge.md`. Section letter cascade
  (R is next free per S11 STATE-SYNC §6) is *reserved* for S13 ACT or for
  a rebased #18011, whichever lands first.
- Does not pre-empt PR #18011 — its content remains the canonical G6 path
  until the 2nd drain wave fires.
- Does not invoke Docker (build-verification is deferred to S13 ACT).

## §8 Acceptance criteria

- [x] `git diff origin/main --stat` shows exactly **2 files** modified:
      `sessions/2026-05-16-s12-prep-g6-companion-file-pivot-prestaging.md`
      (new) and `state.md` (small head-block edit).
- [x] No Lean files modified; no `axiom` / `theorem` count changes; no
      `*.json` edits (this slug has no JSON tracker).
- [x] PR can merge cleanly even if PR #18011 lands next, with conflicts
      limited to the state.md drain-wave tracker (which a future
      STATE-SYNC will re-resolve).
- [x] Iteration counter advanced 11 → 12 to reflect the new PREP session.
- [x] The 1 new bearer file (`Mathlib/Algebra/Group/Hom/Basic.lean`) is
      pinned at SHA `48295b4d989d7c0e51f32c6df843dea8cb693283` for the
      Mathlib `v4.26.0` / `2df2f0150c` rev.

## §9 References

- PR #19439 (S11 STATE-SYNC) — direct predecessor; §6 introduces the
  conditional pivot recommendation that motivates this PREP.
- PR #18011 (G6 algebraic Unit-bridge) — the still-open inline path
  whose conflict surface this companion would side-step.
- PR #18951 (G7 `…G7.lean`) and PR #19114 (G8/G9 `…G8.lean`) — companion
  files this G6 path would parallel.
- Memory: `feedback_researcher_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift_items_ship_full_statesync.md`
  — precedent for the post-merge pivot pattern (here we are the
  post-merge follow-up but pivoting to PREP not STATE-SYNC, because
  S11 already closed the doc-only drift).
- Memory: `feedback_researcher_postship_pivot_lands_on_own_recent_act_merge_with_named_deferred_bearer_pencilwork.md`
  — close cousin: same author-then-claim-same-slug pattern, but PREP
  rather than ACT (since the deferred work — the companion-file pivot
  trigger — has not yet fired).
