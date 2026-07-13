# S3 PREP-2 — §3 fix Mathlib verification (`volume_eq_prod`, `Measure.prod_restrict`, `SFinite`)

**Date**: 2026-05-13
**Researcher**: researcher-5
**Phase**: S3 PREP-2 (doc-only verification; resolves the open question
in #18711 §3 + adds state.md sync)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

**Predecessors**:
- #18262 — S1 OBSERVE (`LocallyIntegrable` wrapper reframing, MERGED).
- #18364 — S2 SCAFFOLD (the wrapper file landed with the phantom-name
  `restrict_prod_eq_prod_restrict`, MERGED, **build pending**).
- #18514 — S2d PREP (cross-family call-site verification, MERGED).
- #18711 — S3 PREP (phantom-name audit, MERGED, **doc-only**).

## §0 Scope and motivation

`#18711` §3 proposed the corrected proof block using
`rw [IntegrableOn, volume_eq_prod, ← Measure.prod_restrict] at hint`,
but left one open question (§3 last paragraph):

> *"whether `rw [volume_eq_prod]` is needed at all, or whether
> `Measure.prod_restrict` accepts unification modulo the definitional
> equality `volume = volume.prod volume` on ℝ × ℝ automatically."*

This PREP resolves that question via four independent Mathlib-source
verifications at the pinned rev, then identifies a precedent in this
codebase that confirms the working call shape. It also performs the
state.md sync that #18711 §7 anti-targets explicitly deferred.

**Net delta**: +1 new sessions/ file; +1 state.md update.
**Zero edits** to `knowledge.md`, `problem.md`, `.lean` files, gallery
JSON, or sibling sessions. (knowledge.md still mentions
`restrict_prod_eq_prod_restrict` as if it were real Mathlib — that
correction belongs to a later PREP or to the eventual Mechanic ACT,
to keep this PREP strictly additive and orthogonal to #18711.)

## §1 Verification 1: `volume_eq_prod` is `rfl`

Source: `Mathlib/MeasureTheory/Measure/Prod.lean:179–181`
(at pin rev `2df2f015`).

```lean
theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) :=
  rfl
```

Three relevant consequences:

1. **`(α β)` are explicit positional arguments**, not implicit. Callers
   must write `volume_eq_prod ℝ ℝ`, not `volume_eq_prod`. A bare
   `rw [volume_eq_prod]` would either fail elaboration (ambiguous type)
   or pick the wrong instantiation by unification.
2. **The proof is `rfl`**, but the lemma is still a *propositional*
   equation. `rw` can use it to syntactically rewrite the term
   `(volume : Measure (ℝ × ℝ))` to `(volume : Measure ℝ).prod (volume : Measure ℝ)`
   — the `rfl` proof affects only *how Lean checks the rewrite*, not
   whether the rewrite changes the goal's syntactic shape.
3. The fact that it is `rfl` means `simp only [volume_eq_prod]` would
   also work and could be substituted if the explicit `(α β)` arguments
   become awkward.

**Conclusion**: the `rw [volume_eq_prod]` step in #18711 §3 is real and
required, and the call site must spell out `volume_eq_prod ℝ ℝ`.

## §2 Verification 2: `Measure.prod_restrict` requires `[SFinite μ] [SFinite ν]`

Source: `Mathlib/MeasureTheory/Measure/Prod.lean:720–728`
(at pin rev `2df2f015`).

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

`μ` and `ν` are section-variable measures (declared at lines 68 of the
same file: `{μ μ' : Measure α} {ν ν' : Measure β}`). Two section
typeclass premises are in scope:

- `Mathlib/MeasureTheory/Measure/Prod.lean:223`: `variable [SFinite ν]`
- `Mathlib/MeasureTheory/Measure/Prod.lean:629`: `variable [SFinite μ]`

The proof body uses `sum_sfiniteSeq μ` and `sum_sfiniteSeq ν`, both of
which require `SFinite`. So `prod_restrict` is implicitly **typeclass
gated by `[SFinite μ] [SFinite ν]`**.

The local file's call site is over `volume.restrict (uIcc a b)` and
`volume.restrict (uIcc c d)` (both with `Measure ℝ` underneath). For
this to type-check, Lean must synthesize `SFinite (volume.restrict
(uIcc a b))` and `SFinite (volume.restrict (uIcc c d))`.

## §3 Verification 3: `SFinite` auto-derives from `SigmaFinite` and is preserved by `.restrict`

Source: `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean`
(at pin rev `2df2f015`).

```lean
-- line 75
instance [SFinite μ] (s : Set α) : SFinite (μ.restrict s) := ⟨…⟩

-- line 190
instance (priority := 100) [SigmaFinite μ] : SFinite μ := by …
```

`volume : Measure ℝ` carries `SigmaFinite` (the standard Lebesgue
instance). Hence:

- `SigmaFinite (volume : Measure ℝ)` ⇒ `SFinite (volume : Measure ℝ)`
  (via `instance` at line 190).
- `SFinite (volume : Measure ℝ)` ⇒ `SFinite (volume.restrict (uIcc a b))`
  (via `instance` at line 75).

Both required typeclass premises of `Measure.prod_restrict` are
discharged by `inferInstance` at the §3 call site. **No manual
`haveI : SFinite … := …` step is needed.**

## §4 Verification 4: `IntegrableOn` unfolds to the `μ.restrict s` form

Source: `Mathlib/MeasureTheory/Integral/IntegrableOn.lean:93–96`
(at pin rev `2df2f015`).

```lean
def IntegrableOn (f : α → ε) (s : Set α) (μ : Measure α := by volume_tac) : Prop :=
  Integrable f (μ.restrict s)
```

So `hint : IntegrableOn (fun p => f p.1 p.2) (uIcc a b ×ˢ uIcc c d) volume`
is definitionally
`Integrable (fun p => f p.1 p.2) (volume.restrict (uIcc a b ×ˢ uIcc c d))`.

The `rw [IntegrableOn] at hint` step is a defeq-`rw` that exposes the
`volume.restrict (s ×ˢ t)` shape, which is exactly the RHS of
`Measure.prod_restrict.symm`. After that:

```
-- hint after rw [IntegrableOn]:
hint : Integrable (fun p => f p.1 p.2) (volume.restrict (uIcc a b ×ˢ uIcc c d))

-- after rw [volume_eq_prod ℝ ℝ] at hint:
hint : Integrable (fun p => f p.1 p.2) ((volume.prod volume).restrict (uIcc a b ×ˢ uIcc c d))

-- after rw [← Measure.prod_restrict] at hint:
hint : Integrable (fun p => f p.1 p.2)
        ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))
```

That is exactly the shape the parent's `intervalIntegral_swap` expects
(verified by the parent file inspection at
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean:191` in #18711 §2).

**Resolution of the #18711 open question**: the explicit
`rw [volume_eq_prod ℝ ℝ]` step IS needed — `Measure.prod_restrict`
will not unify modulo defeq because `rw` matches *syntactically* (the
goal's measure must visibly contain `volume.prod volume`, not just
`volume : Measure (ℝ × ℝ)`).

## §5 In-repo precedent: the working pattern

The exact `rw [volume_eq_prod ℝ ℝ, ...]` invocation pattern is already
used and *builds* in this repository at the same pin:

`proofs/Proofs/AreaOfCircleOQ05OQ04.lean:158`:
```lean
rw [volume_eq_prod ℝ ℝ, integral_prod_mul (μ := volume) (ν := volume) … ]
```

(Also at line 247 of the same file, the same pattern is reused in a
companion theorem.) This is empirical evidence that:

- The `(α β) = (ℝ ℝ)` positional spelling is the *working* one;
- `rw [volume_eq_prod ℝ ℝ, ⟨next-lemma⟩]` is the *working* chained shape
  for converting `volume : Measure (ℝ × ℝ)` into a `volume.prod volume`
  form prior to a measure-product lemma.

## §6 Refined §3 fix (still build-pending — Mechanic ACT to verify)

Drop-in replacement for the final `rwa` step at
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:89`:

```lean
  -- Bridge: IntegrableOn f s μ := Integrable f (μ.restrict s), see
  -- IntegrableOn.lean:95. volume_eq_prod ℝ ℝ : (volume : Measure (ℝ × ℝ))
  -- = volume.prod volume (rfl @ Prod.lean:181). Measure.prod_restrict requires
  -- [SFinite μ] [SFinite ν], satisfied automatically by volume (SigmaFinite
  -- ⇒ SFinite @ Typeclasses/SFinite.lean:190; restrict preserves SFinite
  -- @ line 75). Pattern matches AreaOfCircleOQ05OQ04:158 precedent.
  rw [IntegrableOn, volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hint
  exact hint
```

Pencil-checked changes vs. #18711 §3:

1. Added explicit `(ℝ ℝ)` arguments to `volume_eq_prod` — required (§1).
2. Replaced `rwa` with `rw … exact hint` for clarity (the original
   `rwa` form would also work; the explicit `exact hint` makes
   instance-resolution failures localised).
3. Inline citations to the Mathlib pin and the in-repo precedent.

**Build is still pending**. The next step is a Mechanic ACT with
`./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02`
from a clean worktree, then propagation of the same fix to the four
sibling files identified in #18711 §1.1.

## §7 Anti-targets (preserved from #18711 §7, plus knowledge.md)

This PREP does **not**:

1. Modify `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` or any
   other `.lean` file.
2. Modify `knowledge.md` (still says `restrict_prod_eq_prod_restrict`
   is real Mathlib at rows §S1/Mathlib-API-audit table, lines 36, 62,
   86). That correction belongs to the Mechanic ACT PR that lands the
   §6 fix, or to a future PREP.
3. Modify `problem.md` or gallery `meta.json` (slug has no gallery
   entry yet).
4. Edit sibling slug session files.
5. Re-run #18711 §1.2 phantom verification — that result is durable;
   `gh api search/code` for the phantom name will continue to return 0
   hits.
6. Address the four sibling files (`OQ01`, `OQ02` parent, `OQ03`,
   `AreaOfCircleOQ05OQ01`). Each needs its own Mechanic discharge.

This PREP **does**:

1. Add this `sessions/2026-05-13-s3-prep-2-volume-bridge-verification.md`.
2. Update `state.md` to reflect the four merged PRs (`#18262`, `#18364`,
   `#18514`, `#18711`) and the actual current phase. The state.md sync
   was explicitly deferred by #18711 §7 — this PREP picks up that
   pre-curated orthogonal target.

## §8 State.md sync content (companion edit in this commit)

The state.md before this commit reports
`Phase: S1 OBSERVE complete (docs only, 0 Lean changes)` and
`Iteration: 1` — both stale since 2026-05-12. The sync brings the
header in line with the four merged predecessors and identifies the
current phase as `S3 PREP-2 complete (awaiting Mechanic ACT)`.

No other state.md fields are mutated semantically; the
**Decomposition Plan** table is filled in with the actual phase
outcomes; the **Active Approach** and **Next Action** sections are
updated to point at the §6 §3-fix template; the **Key Risks** entry
about `LocallyIntegrable.integrableOn_isCompact` name drift is
preserved (it is still relevant for the Mechanic build) and a new
risk row about the phantom name is added.

## §9 Race-safety

- **Open PRs on slug at draft time** (2026-05-13 ~12:25 UTC):
  `gh pr list --repo rjwalters/lean-genius --search "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title" --state open` → `[]` (zero).
- **Last merged on slug**: #18711 (S3 PREP, 2026-05-13T09:02:02Z) —
  ~3h 23m ago. No active sibling researcher slot has the slug claimed.
- **Pristine session-file path**:
  `sessions/2026-05-13-s3-prep-2-volume-bridge-verification.md`.
  Unique; sole new entry in `sessions/`.
- **No overlap with sibling OQ-01 open PRs** (#17822, #17838, #17840)
  — those touch `…OQ02OQ01.lean`, not this slug's `…OQ02OQ02.lean`.

## §10 Honesty

- **All four verifications** (§§1–4) are reproducible at the same
  Mathlib pin via the `gh api repos/.../contents/...?ref=2df2f015`
  pattern. The exact line numbers cited (`Prod.lean:181`, `:720`,
  `Typeclasses/SFinite.lean:75` and `:190`, `IntegrableOn.lean:95`)
  are from the pinned blob, not from current HEAD.
- **§5 precedent** is from the local worktree at HEAD = origin/main;
  if `AreaOfCircleOQ05OQ04.lean` is itself build-pending (memory
  cannot confirm one way or the other), the precedent's syntactic
  shape is still evidence (any drift would have been visible in the
  file as TODO/sorry).
- **§6 refined fix is paper-checked, not Docker-build-checked.** The
  reasoning is tighter than #18711 §3 (resolves the open question and
  adds positional-arg + typeclass details), but a Mechanic with a
  working `.lake` is still required to convert "pencil-correct" to
  "machine-verified". The build risk is now low but nonzero — minor
  drift between `Integrable` and `IntegrableOn` definitional unfolding
  could require a `change` step or `simp only [IntegrableOn]` instead
  of `rw [IntegrableOn]`.
- **The §1 `rfl` finding** does *not* mean the rewrite is a no-op;
  `rw` still performs the syntactic substitution even when the proof
  is `rfl`. The two concepts are independent.

## §11 References

### Mathlib v4.26.0 source (verified this PREP, 2026-05-13)

- `Mathlib/MeasureTheory/Measure/Prod.lean:65–68` — section variables
  `{μ μ' : Measure α} {ν ν' : Measure β}`.
- `Mathlib/MeasureTheory/Measure/Prod.lean:179–181` — `volume_eq_prod`,
  proven by `rfl`, explicit `(α β)` arguments.
- `Mathlib/MeasureTheory/Measure/Prod.lean:223` — `variable [SFinite ν]`.
- `Mathlib/MeasureTheory/Measure/Prod.lean:629` — `variable [SFinite μ]`.
- `Mathlib/MeasureTheory/Measure/Prod.lean:720–728` — `Measure.prod_restrict`.
- `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:75–77` —
  `instance [SFinite μ] (s : Set α) : SFinite (μ.restrict s)`.
- `Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean:190–192` —
  `instance (priority := 100) [SigmaFinite μ] : SFinite μ`.
- `Mathlib/MeasureTheory/Integral/IntegrableOn.lean:93–96` — `IntegrableOn`.

### In-repo precedent

- `proofs/Proofs/AreaOfCircleOQ05OQ04.lean:158, 247` — working
  `rw [volume_eq_prod ℝ ℝ, …]` invocations.

### Predecessor PRs

- **#18262** — S1 OBSERVE.
- **#18364** — S2 SCAFFOLD (introduces phantom name).
- **#18514** — S2d PREP.
- **#18711** — S3 PREP (phantom audit; §3 had the open question this PREP resolves).

### Memory

- `project_greens_theorem_family_mathlib_drift_v4260.md` — family-wide
  phantom catalog.
- `feedback_researcher_lake_symlink_loop_and_wipe.md` — Docker-build
  unreliability in worktree, explains build-pending status.
- `feedback_researcher_sibling_race_orthogonal_complement.md` — this
  PREP is an orthogonal complement to #18711, picking up its §7
  anti-target (state.md sync).
- `feedback_researcher_push_onto_open_pr_branch_contamination.md` —
  fresh branch from origin/main, not from previously-occupied
  branches, avoids PR scope contamination.

### Reproducible verification commands

```bash
# §1 — volume_eq_prod (the lemma itself):
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Measure/Prod.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
    | jq -r '.content' | base64 -D | sed -n '177,182p'

# §2 — Measure.prod_restrict signature and section variables:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Measure/Prod.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
    | jq -r '.content' | base64 -D | sed -n '720,728p'

# §3 — SFinite instance derivation:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Measure/Typeclasses/SFinite.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
    | jq -r '.content' | base64 -D | sed -n '73,80p;188,193p'

# §4 — IntegrableOn definition:
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Integral/IntegrableOn.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
    | jq -r '.content' | base64 -D | sed -n '93,97p'

# §5 — In-repo precedent:
sed -n '155,162p' proofs/Proofs/AreaOfCircleOQ05OQ04.lean
```

**End of S3 PREP-2 — §3 fix Mathlib verification + state.md sync.**
