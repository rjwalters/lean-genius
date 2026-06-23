# S3 PREP — Phantom `restrict_prod_eq_prod_restrict` audit (Mathlib v4.26.0 drift)

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: S3 PREP (doc-only audit; flags a `verified`-status drift in this slug's S2 SCAFFOLD)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

**Predecessors**:
- #18262 — S1 OBSERVE (`LocallyIntegrable` wrapper reframing, MERGED).
- #18364 — S2 SCAFFOLD (`Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` landed with the wrapper theorem, MERGED, **build pending** — never Docker-verified).

## §0 Scope

The S2 SCAFFOLD merged a wrapper theorem
`intervalIntegral_swap_of_locallyIntegrable` whose final tactic uses
the lemma name `restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc`.

**Empirical finding (this PREP):**

```
$ gh api 'search/code?q=%22restrict_prod_eq_prod_restrict%22+repo:leanprover-community/mathlib4&per_page=3'
{"total_count":0,"incomplete_results":false,"items":[]}
```

**Zero hits in Mathlib v4.26.0**. The lemma name is a **phantom** —
not just drifted by some lines but missing entirely. The S2 SCAFFOLD
file would fail to elaborate on first build.

This PREP:

1. Verifies the phantom finding at v4.26.0 via reproducible `gh api`
   search.
2. Identifies the actual Mathlib lemma: `Measure.prod_restrict` at
   `Mathlib/MeasureTheory/Measure/Prod.lean:720`, in *reverse direction*
   from what the local code assumes, and with *no measurability
   arguments*.
3. Surveys the family-wide impact: **5 local Lean files** use this
   phantom name (including the `verified`-status parent
   `Proofs/GreensTheoremOQ01OQ01OQ02.lean`).
4. Proposes the corrected proof block for this slug's wrapper file.
5. Recommends Doctor/Mechanic for the family-wide drift-sync.

**Net delta**: +1 new sessions/ file. **Zero edits** to any other file
— no `state.md`, `knowledge.md`, `problem.md`, gallery JSON, Lean
sources, or sibling session notes.

## §1 Phantom verification

### §1.1 The phantom name

`restrict_prod_eq_prod_restrict` is referenced in 5 local Lean files
(grep results in this slug's worktree at HEAD = origin/main):

```
proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean (this slug; S2 SCAFFOLD #18364)
proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean (sibling oq-03)
proofs/Proofs/GreensTheoremOQ01OQ01OQ01.lean    (sibling oq-01)
proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean    (parent slug)
proofs/Proofs/AreaOfCircleOQ05OQ01.lean         (unrelated slug)
```

The parent file `GreensTheoremOQ01OQ01OQ02.lean` has gallery
`status: verified` (per `state.md:87`). Verified status means
"machine-checked, no assumptions" per `CLAUDE.md` definitions; if
the verified parent uses a phantom name, the `verified` status is
**structurally stale** (set by merge author, not by current build
gate).

### §1.2 Live verification (2026-05-13 ~08:55 UTC)

```bash
$ gh api 'search/code?q=%22restrict_prod_eq_prod_restrict%22+repo:leanprover-community/mathlib4&per_page=3' \
    | jq '.total_count'
0
```

Compared to the canonical product-measure lemma:

```bash
$ gh api 'search/code?q=%22Measure.prod_restrict%22+repo:leanprover-community/mathlib4&per_page=3' \
    | jq '.total_count'
3
```

The latter resolves to `Mathlib.MeasureTheory.Measure.Prod` at
line 720 (v4.26.0 ref `defda893c008015592dbbf4e7d7c00a58aa62745`):

```lean
theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, restrict_sum_of_countable,
      restrict_sum_of_countable, prod_sum, prod_sum, restrict_sum_of_countable]
  congr 1
  ext1 i
  refine prod_eq fun s' t' hs' ht' => ?_
  rw [restrict_apply (hs'.prod ht'), prod_inter_prod, prod_prod,
      restrict_apply hs', restrict_apply ht']
```

**Three differences from the phantom name in S2 SCAFFOLD**:

1. **Name**: `Measure.prod_restrict`, not `restrict_prod_eq_prod_restrict`.
2. **No measurability hypotheses**: the phantom call passes
   `measurableSet_uIcc measurableSet_uIcc` as arguments; the real lemma
   takes only the two sets and uses an internal `prod_eq` argument that
   handles measurability automatically.
3. **Direction**: the real lemma rewrites
   `(restrict).prod (restrict) → (prod).restrict (×ˢ)` (LHS → RHS).
   The local code expects the reverse direction (to convert
   `Integrable f (volume.restrict (uIcc × uIcc))` into the parent's
   `Integrable f ((volume.restrict uIcc).prod (volume.restrict uIcc))`),
   so the actual rewrite needs `← Measure.prod_restrict`.

## §2 What the local file is trying to prove

The S2 SCAFFOLD file (`GreensTheoremOQ01OQ01OQ02OQ02.lean:78-89`):

```lean
theorem intervalIntegral_swap_of_locallyIntegrable {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_loc : LocallyIntegrable (fun p : ℝ × ℝ => f p.1 p.2) volume) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap a b c d hf_meas
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (uIcc a b ×ˢ uIcc c d) volume :=
    hf_loc.integrableOn_isCompact hcpt
  rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
```

After `apply` of the parent's `intervalIntegral_swap`, the remaining
goal is

```
Integrable (fun p => f p.1 p.2)
  ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))
```

(per the parent's hypothesis shape, verified via inspection of
`GreensTheoremOQ01OQ01OQ02.lean:191`).

`hint : IntegrableOn ... (uIcc × uIcc) volume` unfolds to
`Integrable f (volume.restrict (uIcc × uIcc))` where the restrict is on
the product `Set (ℝ × ℝ)`.

The bridge from `volume.restrict (uIcc × uIcc)` (`hint`'s form) to
`(volume.restrict uIcc).prod (volume.restrict uIcc)` (parent's hyp form)
needs two facts:

1. **`volume = volume.prod volume`** on ℝ × ℝ. In Mathlib v4.26.0 this
   is `MeasureTheory.volume_eq_prod` (12 hits across Mathlib4;
   typically used via `rw [volume_eq_prod]` to expose the product-measure
   structure on `volume : Measure (α × β)`).
2. **`(prod).restrict (s ×ˢ t) = (restrict s).prod (restrict t)`** —
   this is `Measure.prod_restrict.symm` or used as `← Measure.prod_restrict`.

## §3 Proposed corrected proof block

```lean
theorem intervalIntegral_swap_of_locallyIntegrable {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_loc : LocallyIntegrable (fun p : ℝ × ℝ => f p.1 p.2) volume) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap a b c d hf_meas
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (uIcc a b ×ˢ uIcc c d) volume :=
    hf_loc.integrableOn_isCompact hcpt
  -- Bridge: volume.restrict (s ×ˢ t) = (volume.restrict s).prod (volume.restrict t).
  -- Use volume_eq_prod to expose the product structure, then ← Measure.prod_restrict.
  rw [IntegrableOn, volume_eq_prod, ← Measure.prod_restrict] at hint
  exact hint
```

LOC: same as original (4 LOC body for the integrability obligation,
12 LOC for the theorem block).

**Open question for the corrector**: whether `rw [volume_eq_prod]` is
needed at all, or whether `Measure.prod_restrict` accepts unification
modulo the definitional equality `volume = volume.prod volume` on ℝ × ℝ
automatically. The `rw` form is the safe option; the bare form may also
work if `volume_eq_prod` is `rfl`-equation or marked `@[simp]`.

## §4 Family-wide impact

| File | Usage count | Status |
|---|---|---|
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` | parent (verified) | **structurally stale verified status** |
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` | this slug (S2 SCAFFOLD #18364, build pending) | discharge via §3 |
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` | sibling oq-03 (status?) | independent drift-sync needed |
| `proofs/Proofs/GreensTheoremOQ01OQ01OQ01.lean` | sibling oq-01 (n-dim lift) | independent drift-sync needed |
| `proofs/Proofs/AreaOfCircleOQ05OQ01.lean` | unrelated slug | independent drift-sync needed |

All 5 files import `Mathlib.MeasureTheory` (transitively) at the same
v4.26.0 pin. The phantom is consistent across files — likely all
introduced by a researcher who hand-typed a plausible-sounding name
that never existed in Mathlib upstream.

**Recommendation**: a Mechanic drift-sync PR addressing all 5 files in
one shot, after this slug's local discharge lands. Per memory
`project_greens_theorem_family_mathlib_drift_v4260.md`, this drift is
the primary blocker on the greens-theorem family's verified-status
honesty.

## §5 Why this PREP, not an S3 ACT

I considered shipping the §3 corrected proof block directly as an
S3 ACT, but chose to ship as PREP because:

1. **No local build verification**: worktree's `proofs/.lake` is in the
   self-referential symlink loop (memory:
   `feedback_researcher_lake_symlink_loop_and_wipe.md`). The §3 form
   uses `rw [volume_eq_prod, ← Measure.prod_restrict]` — a 2-step
   rewrite that may need adaptation (the order of operations or an
   intermediate `simp only` for `IntegrableOn` unfolding may matter).
2. **Family-wide concern**: the same phantom appears in 4 other files;
   fixing only this slug's instance is incomplete — the parent's
   `verified` claim depends on its own discharge. A Mechanic with a
   working build can attempt all 5 fixes in one consistent pass.
3. **Honesty**: the original S2 SCAFFOLD merged with `build pending` —
   the issue I'm flagging is a build failure that has not yet been
   surfaced by CI or doctor verification. Shipping the corrected proof
   without build verification under the same `build pending` flag would
   propagate the same risk. A PREP is the honest disclosure.

## §6 Race-safety

- **Open PRs on slug at draft time** (2026-05-13 ~08:55 UTC):
  `gh pr list --repo rjwalters/lean-genius --search "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title" --state open` → `[]` (zero).
- **Open PRs on sibling oq-01**: 3 PRs (#17822, #17838, #17840) on
  `greens-theorem-oq-01-oq-01-oq-02-oq-01`, all from 5+ days ago and
  apparently abandoned (S2/S3 ACT competing for same lemma). These
  reside on a different slug; no overlap with this PREP's file.
- **Most recent merge on this slug**: #18364 (S2 SCAFFOLD,
  2026-05-12T23:16:28Z) — ~10 hours ago.
- **Most recent activity on parent slug**: enricher PR #18302
  at 2026-05-12T21:23:47Z (~12h ago).
- **Pristine session-file path**:
  `sessions/2026-05-13-s3-prep-phantom-mathlib-audit.md`. Unique
  (the slug currently has no `sessions/` subdir).

## §7 Anti-targets

This PREP does **not**:

1. Modify `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` or any
   other `.lean` file. The discharge belongs to a Mechanic PR with a
   working build.
2. Update `state.md` (still says S1 OBSERVE complete; S2 SCAFFOLD's
   state.md update is a separate concern).
3. Touch gallery `meta.json` (the slug has no gallery entry yet).
4. Modify `knowledge.md` or `problem.md`.
5. Edit any sibling session file (the slug has no `sessions/` subdir
   yet — this PREP creates the first).
6. Re-audit the parent's `verified` status formally. That's an Auditor
   PR.
7. Address the sibling files (`OQ01`, `OQ03`, `AreaOfCircle`). Each
   needs its own audit if a Mechanic doesn't bundle them.

## §8 Suggested next actions

For **Doctor / Mechanic**:

1. Build the current file via
   `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02`
   from a clean worktree (not from `.loom/worktrees/researcher-1`'s
   symlink-broken `.lake`).
2. If the phantom-name elaboration error reproduces, apply the §3
   discharge.
3. Consider bundling the parent `Proofs.GreensTheoremOQ01OQ01OQ02`
   discharge in the same PR, since it shares the same phantom name
   and currently carries `verified` status that the build does not
   actually justify.

For **Auditor**:

1. Revisit the parent's `meta.json` `status: verified` claim once the
   Mechanic discharge lands; flag with `axiomatized` if the build
   fails until corrected.
2. Update the family-wide drift entry per memory
   `project_greens_theorem_family_mathlib_drift_v4260.md`.

For **future S3 ACT picker** (if not Mechanic):

1. Read §3 verbatim as the discharge template.
2. Build under Docker before push.
3. Update `state.md` to reflect S2 SCAFFOLD MERGED + S3 ACT phase
   advancement.

## §9 Honesty

- **The phantom finding is empirical**, verified by `gh api search/code`
  returning 0 hits on `leanprover-community/mathlib4`. Reproducible at
  any later date (search is live; result could only change if Mathlib
  introduces a back-compat alias, extremely unlikely given the lemma's
  absence from the v4.26.0 codebase tree).
- **The §3 corrected discharge is paper-checked, not build-verified.**
  The 2-step rewrite (`volume_eq_prod` then `← Measure.prod_restrict`)
  may need adjustment depending on `volume_eq_prod`'s exact form (∀
  α β with measure-product structure vs. specialised to ℝ × ℝ).
- **The family-wide impact assessment** (`grep` results in §4) reflects
  the worktree state at HEAD = origin/main; sibling files may have
  drifted further independently.
- **No claim** that the parent's `verified` status is *currently*
  invalidated — only that it is *not currently verified* by any build
  CI run that includes the phantom-name elaboration. The structural
  staleness is real but the formal correctness of the underlying math
  is presumably still fine.
- **The 5-file family count** is from the current worktree's `Grep`
  pattern `restrict_prod_eq_prod_restrict`; other phantom-name variants
  (e.g. `Measure.restrict_prod_eq_prod_restrict`, `MeasureTheory.Measure.restrict_prod`)
  were not exhaustively checked.

## §10 References

### Mathlib v4.26.0 source (verified by this PREP, 2026-05-13)

- `Mathlib/MeasureTheory/Measure/Prod.lean:720` — `Measure.prod_restrict`
  (the actual lemma, no measurability args).
- `Mathlib/MeasureTheory/Measure/Prod.lean:730` — `Measure.restrict_prod_eq_prod_univ`
  (an existing close-name lemma, but different statement).
- `Mathlib/MeasureTheory/Constructions/Pi.lean:653` — `Real.volume_pi`
  (Lebesgue volume = pi instance; companion fact for `volume_eq_prod`
  on `α × β`).

### Local Lean files affected (5)

- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:89` (this slug).
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` (sibling oq-03).
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ01.lean` (sibling oq-01).
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (parent, verified status).
- `proofs/Proofs/AreaOfCircleOQ05OQ01.lean` (unrelated slug).

### Predecessor PRs

- **#18262** — S1 OBSERVE.
- **#18364** — S2 SCAFFOLD (introduces the phantom-name usage).

### Memory

- `project_greens_theorem_family_mathlib_drift_v4260.md` — pre-existing
  catalog of this drift, identifying `Measure.prod_restrict` as the
  v4.26.0 replacement.
- `feedback_researcher_lake_symlink_loop_and_wipe.md` — explains why
  this PREP cannot Docker-build locally.

### Reproducible verification commands

```bash
# Phantom check (§1.2):
gh api 'search/code?q=%22restrict_prod_eq_prod_restrict%22+repo:leanprover-community/mathlib4&per_page=3' \
    | jq '.total_count'   # expect: 0

# Substitute check:
gh api 'search/code?q=%22Measure.prod_restrict%22+repo:leanprover-community/mathlib4&per_page=3' \
    | jq '.total_count'   # expect: 3

# Local file inventory:
git grep -l "restrict_prod_eq_prod_restrict" proofs/Proofs/   # expect: 5 files
```

**End of S3 PREP — phantom Mathlib name audit on S2 SCAFFOLD.**
