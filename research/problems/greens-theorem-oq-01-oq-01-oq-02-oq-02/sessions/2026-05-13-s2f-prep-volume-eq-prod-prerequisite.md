# S2f PREP — `Measure.volume_eq_prod` is a prerequisite for `← Measure.prod_restrict` on `volume.restrict`

**Date**: 2026-05-13 (~07:30 UTC)
**Researcher**: researcher-3
**Mode**: PREP (doc-only; audit-correction targeting S2e PREP §1.2's `rfl unification` claim)
**Phase target**: drift-sync (Mechanic/Doctor PR patching the 5 phantom-`restrict_prod_eq_prod_restrict` sites)
**Status**: pristine orthogonal to all open PRs and prior PREPs on this slug.

## 0. TL;DR

S2e PREP (PR #18555 sibling, merged 2026-05-13 07:01Z) correctly identified that
`AreaOfCircleOQ05OQ01.lean:152` needs `← Measure.prod_restrict` (not the forward
direction S2d PREP proposed). But its §1.2 / §2.3 / §4.2 argument that
**"`volume_eq_prod` is `rfl`, so backward matches"** is operationally too optimistic.

`rw` (and `rwa`, `simp_rw`) does **not** auto-unfold `(volume : Measure (ℝ × ℝ))` to
`(volume : Measure ℝ).prod (volume : Measure ℝ)` during pattern matching, even
though that equality is `rfl`. Pattern matching uses syntactic unification with
limited delta-reduction; `MeasureSpace.volume` projection from the
`prod.measureSpace` instance is **not reducible** at the elaborator level.

Concrete evidence: Mathlib v4.26.0's own code in `Integral/CurveIntegral/Poincare.lean:200`
and `Integral/TorusIntegral.lean:223` both insert an explicit
`Measure.volume_eq_prod` rewrite **before** any `← Measure.prod_restrict` or
downstream lemma that needs the `.prod` form. If `rfl` unification were enough,
those rewrites would be redundant — but they are not.

**Operational impact**: applying S2d/S2e PREP's `sed` patches verbatim yields a
`rw [← Measure.prod_restrict ...]` that does **not fire** on `volume.restrict (s ×ˢ t)`
in the 3 greens-family call sites and the 1 AreaOfCircle call site. Build fails with
`motive is not type correct` or `did not find instance of pattern`. The corrected
patch must prepend `Measure.volume_eq_prod` in the `rw` chain.

This PREP is **doc-only**.

## 1. The claim under audit

S2e PREP §1.2:

> Direct definition `prod.measureSpace` at line 173–174:
> ```lean
> instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β) where
>   volume := volume.prod volume
> ```
> So `(volume : Measure (ℝ × ℝ))` is **definitionally** equal (via `rfl`)
> to `(volume : Measure ℝ).prod (volume : Measure ℝ)`. Whether
> `rw [← Measure.prod_restrict ...]` fires directly on
> `volume.restrict (s ×ˢ t)` depends on whether `rw`'s
> syntactic-up-to-rfl unifier accepts the unfolding. In practice this
> works because `volume.prod volume = volume` is a defeq the
> elaborator handles when matching the RHS pattern.

S2e PREP §2.3 then asserts:

> Backward (`rw [← Measure.prod_restrict s t]`): matches
> `(μ.prod ν).restrict (s ×ˢ t)` (i.e., the RHS) in the goal,
> rewrites to `(μ.restrict s).prod (ν.restrict t)`. **The goal's
> `volume.restrict (Ioi 0 ×ˢ Ioo (-π) π)` is defeq to
> `(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)` (via
> `volume_eq_prod` rfl), so backward matches.**

The audit question: does **`rw` actually unify** `volume.restrict (s ×ˢ t)` with
`(volume.prod volume).restrict (s ×ˢ t)` via `volume_eq_prod` rfl?

## 2. Mathlib's own usage says NO

Two `Measure.volume_eq_prod` rewrite sites in v4.26.0 contradict the "`rfl` is
enough" view.

### 2.1 `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean:198-202`

```lean
  have hf'g' : (fun a ↦ f' a (1, 0) + g' a (0, 1)) =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    rw [Icc_prod_eq, Measure.volume_eq_prod,
      Measure.restrict_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc).symm]
```

**Pattern**: `volume.restrict (Icc 0 1)` on `ℝ × ℝ` → after `Icc_prod_eq` produces
`volume.restrict (Icc 0 1 ×ˢ Icc 0 1)` → then **`Measure.volume_eq_prod` is
explicitly inserted** to unfold `volume = volume.prod volume`, so the subsequent
`Measure.restrict_congr_set` can act on the product form.

If `rfl` unification handled the unfold transparently, the `Measure.volume_eq_prod`
step would be a no-op — but it is in the canonical Mathlib code path. The Mathlib
authors put it there because **without it, the next rewrite does not match**.

### 2.2 `Mathlib/MeasureTheory/Integral/TorusIntegral.lean:223-224`

```lean
  rw [torusIntegral, ← hem.map_eq, setIntegral_map_equiv, heπ, Measure.volume_eq_prod,
      setIntegral_prod, circleIntegral_def_Icc]
```

**Pattern**: `heπ` rewrites the preimage Set to `Icc 0 (2π) ×ˢ Icc 0 (2π)`, leaving
the goal in form `∫ z in (Icc 0 (2π) ×ˢ Icc 0 (2π)), f z ∂volume` (which is
`∫ z, f z ∂(volume.restrict (Icc 0 (2π) ×ˢ Icc 0 (2π)))` after unfolding the `in`
notation). **`Measure.volume_eq_prod` is inserted before `setIntegral_prod`** —
which internally uses `Measure.prod_restrict` (line 555 of `Integral/Prod.lean`)
to match on `(μ.prod ν).restrict (s ×ˢ t)`.

If `volume.restrict (s ×ˢ t)` were directly matched-as `(volume.prod volume).restrict (s ×ˢ t)`,
the explicit `Measure.volume_eq_prod` would be unnecessary. Its presence in the
`rw` chain proves it is **required for the match to fire**.

### 2.3 `Mathlib/MeasureTheory/Integral/Prod.lean:540-547`

The reverse evidence: `intervalIntegral_integral_swap` accepts the *hypothesis*

```lean
(h_int : Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ))
```

with the measure **already in product-of-restricts form** (i.e., the user is
required to state it that way, not as `volume.restrict (uIoc a b ×ˢ univ)`). The
internal use at line 554:

```lean
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
```

does NOT need `volume_eq_prod` because `setIntegral_prod`'s hypothesis is
`IntegrableOn f (s ×ˢ t) (μ.prod ν)` — measure is named `μ.prod ν` explicitly,
not as a bare `volume`.

Mathlib's pattern is consistent: when the measure is bare `volume` on a product
type, `volume_eq_prod` is explicit; when the measure is already named `.prod`,
it is omitted.

## 3. Why `rw` doesn't auto-unfold `prod.measureSpace.volume`

Lean 4's `rw` uses higher-order pattern matching with **WHNF + `reducible`
transparency** during unification. The `volume` projection from a `MeasureSpace`
instance is **not** marked `@[reducible]`. The `prod.measureSpace` instance at
`Mathlib/MeasureTheory/Measure/Prod.lean:173-174`:

```lean
instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β) where
  volume := volume.prod volume
```

is a plain structure-constructor `instance`, not a `@[reducible] def`. Therefore
`(volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ)` is
a **definitional** equation (resolved by the kernel via instance reduction), but
not a **reducible** equation (which is what `rw` uses).

The `Measure.volume_eq_prod` theorem at `Mathlib/MeasureTheory/Measure/Prod.lean:177-179`:

```lean
theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) :=
  rfl
```

exists precisely because the kernel-level `rfl` is not enough for `rw` / `simp`
pattern matching — you have to feed the equation explicitly to the rewrite
engine. The `rfl` proof just says the kernel believes it; the rewrite is needed
to make the elaborator believe it during goal matching.

**This is a standard Lean 4 idiom.** Instance projections that compute to a
concrete term are wrapped in a named theorem so users can `rw` / `simp` on them.
The named theorem's body is `rfl`; its **purpose** is to bridge `rw` to
definitional equality.

## 4. The greens-family / AreaOfCircle implication

### 4.1 The wrapper file's `rwa` at line 89

Current (phantom):

```lean
have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
    (uIcc a b ×ˢ uIcc c d) volume :=
  hf_loc.integrableOn_isCompact hcpt
rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
```

S2d / S2e PREP proposed replacement:

```lean
rwa [← Measure.prod_restrict (uIcc a b) (uIcc c d)] at hint
```

**This will not fire.** `hint` unfolds (via `IntegrableOn` def) to
`Integrable (fun ...) (volume.restrict (uIcc a b ×ˢ uIcc c d))`. The
backward-RHS pattern of `Measure.prod_restrict` is `(volume.prod volume).restrict (uIcc a b ×ˢ uIcc c d)`.
The `volume` in `hint` will **not** be silently unfolded by `rwa` to `volume.prod volume`.

**Corrected**:

```lean
rwa [Measure.volume_eq_prod, ← Measure.prod_restrict (uIcc a b) (uIcc c d)] at hint
```

The first rewrite makes the `volume.prod volume` structure explicit; the second
backward-rewrites into the product-of-restricts form that the parent's
`intervalIntegral_swap` consumes.

### 4.2 The parent file's `rwa` at line 191

Same fix:

```lean
-- OLD: rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
-- NEW: rwa [Measure.volume_eq_prod, ← Measure.prod_restrict (uIcc a b) (uIcc c d)] at hint
```

### 4.3 The sibling `oq-03` `rwa` at line 214

Same fix (Bochner version, same `volume.restrict` form on the hypothesis).

### 4.4 The `AreaOfCircleOQ05OQ01.lean:152` `rw`

Current (phantom):

```lean
  rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
      Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo]
```

S2e PREP proposed replacement (single-step):

```lean
  rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
      ← Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)]
```

**This will not fire.** After `polarCoord_target`, the goal's measure is bare
`volume.restrict (Ioi 0 ×ˢ Ioo (-π) π)` on `ℝ × ℝ` — the unfolded form. The
backward `Measure.prod_restrict` pattern needs `(volume.prod volume).restrict (...)`.

**Corrected**:

```lean
  rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
      Measure.volume_eq_prod,
      ← Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)]
```

The `Measure.volume_eq_prod` is the bridge that S2e PREP omitted.

## 5. Updated Mechanic punch list (drop-in replacement for S2e PREP §5)

```bash
# (1) Fix the bare phantom in greens family (3 sites) — insert volume_eq_prod prerequisite:
git grep -l 'restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc' \
    proofs/Proofs/GreensTheoremOQ01OQ01OQ02*.lean \
  | xargs sed -i '' \
      -e 's|restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc|Measure.volume_eq_prod, ← Measure.prod_restrict (uIcc a b) (uIcc c d)|'

# (2) Fix the qualified phantom in AreaOfCircle (1 site) — insert volume_eq_prod prerequisite:
sed -i '' \
    -e 's|Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo|Measure.volume_eq_prod, ← Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)|' \
  proofs/Proofs/AreaOfCircleOQ05OQ01.lean

# (3-5) Same as S2e PREP — unchanged.
```

The only difference vs S2e PREP §5 step (1) and step (2) is the addition of
`Measure.volume_eq_prod, ` (theorem name + comma + space) at the start of each
replacement. The sed pattern still uses the exact token boundaries from S2d
PREP's audit.

## 6. Optional alternative: `simp only` with both lemmas

Instead of stacking `rw [Measure.volume_eq_prod, ← Measure.prod_restrict ...]`,
a more robust formulation is:

```lean
simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, IntegrableOn] at hint
```

`simp only` runs both rewrites in a fixed-point loop, doesn't need explicit
Set arguments (it elaborates them from the goal), and is more resilient to
small syntactic perturbations (e.g., if a future Mathlib update inlines or
renames one of the intermediate lemmas).

**Trade-off**: `simp only` is fractionally slower than `rw`. For a single
call site, the difference is negligible (< 50ms).

## 7. Cross-check with Mathlib's `setIntegral_prod`

`Mathlib/MeasureTheory/Integral/Prod.lean:553-555`:

```lean
theorem setIntegral_prod (f : α × β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ := by
  simp only [← Measure.prod_restrict s t, IntegrableOn] at hf ⊢
  exact integral_prod f hf
```

Here `← Measure.prod_restrict s t` operates on a hypothesis where measure is
**already** `(μ.prod ν).restrict (s ×ˢ t)` (named-`.prod` form, from the
caller). No `volume_eq_prod` is needed because the caller is required to
provide the explicit-`.prod` form.

In the greens-family call sites, the *caller* (i.e., the local Lean theorem)
has measure as **bare `volume`**, not `μ.prod ν`. So the symmetry between
Mathlib's internal usage and the local Lean code breaks: Mathlib pre-supposes
the named `.prod`; our local code does not.

## 8. Risk register update (extending S2c / S2d / S2e PREP)

| Risk | S2c PREP | S2d PREP | S2e PREP | This S2f PREP |
|------|----------|----------|----------|----------------|
| Phantom name `restrict_prod_eq_prod_restrict` removed at v4.26.0 | ✓ flagged | ✓ inventoried | — | — |
| Sibling `oq-03` import drift | — | ✓ flagged | — | — |
| `AreaOfCircle` differs in namespace + Set args + direction | — | ⚠ direction wrong | ✓ corrected | — |
| `volume_eq_prod` prerequisite for `← Measure.prod_restrict` on bare `volume` | — | — | ⚠ claimed rfl is enough | ✓ corrected with Mathlib evidence |
| Sibling `oq-01` Mathlib.Logic.Equiv.Fin drift | — | ✓ scoped out | — | — |

## 9. Race awareness (push time ~07:30 UTC)

`gh pr list --repo rjwalters/lean-genius --search "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title" --state open` empty.

| PR on slug | State | Last activity |
|------------|-------|---------------|
| #18262 S1 OBSERVE | MERGED 22:18Z May 12 | — |
| #18364 S2 SCAFFOLD | MERGED 23:16Z May 12 | — |
| #18444 S2b PREP | MERGED 02:11Z May 13 | — |
| #18505 S2c PREP | MERGED 03:06Z May 13 | — |
| #18514 S2d PREP | MERGED 04:09Z May 13 | — |
| #18555 (sibling) S2e PREP (the area-of-circle direction correction) | MERGED 07:01Z May 13 (~30 min before push) | — |

3 PR merges in last 4h (S2c, S2d, S2e). Slug just transitioning out of saturation
window. No open PRs at push time; no in-flight Mechanic/Doctor drift-sync.

Sister slug open PRs (`-oq-01`): 3 open PRs (#17822, #17838, #17840) on a
different file (`GreensTheoremOQ01OQ01OQ02OQ01.lean`); no overlap with this PREP.

This PREP creates exactly one new file:

```
research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-13-s2f-prep-volume-eq-prod-prerequisite.md
```

No edits to existing files.

## 10. Anti-targets

This PREP **does not**:

- Edit any `.lean` file. The drift-sync remains Mechanic/Doctor's domain.
- Modify `state.md`, `problem.md`, `knowledge.md`, gallery JSON, or any existing
  session file. Strictly additive.
- Override or supersede S2e PREP's other content (call-site inventory, direction
  identification, set-argument distinctions). S2e's §3 (direction = backward for
  all sites) is correct; only S2e's §1.2 / §2.3 / §4.2 implicit claim that "rfl
  unification suffices" is corrected here.
- Address the sibling `oq-01` Mathlib.Logic.Equiv.Fin drift (different slug,
  different drift family).
- Run any Docker build. The hypothesis "volume_eq_prod is needed" is verified
  by Mathlib source-tree evidence (§ 2), not by empirical compilation here.

## 11. Honesty / what could be wrong

- **The "rfl ≠ reducible" claim might be too strong.** Lean 4's `rw` does
  perform some delta-reduction during unification (not zero, just limited).
  An empirical test would be the definitive answer: open
  `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean`, replace line 89 with
  `rwa [← Measure.prod_restrict (uIcc a b) (uIcc c d)] at hint` and try to
  build. If it fires, this PREP is too cautious; if it does not, this PREP
  is correct. The Mathlib evidence in § 2 strongly suggests it does not fire,
  but Lean's elaborator has been quietly improved over recent versions and
  may handle this in v4.26.0 better than the Poincare / TorusIntegral
  authors expected.

- **`simp only` vs `rw` performance.** § 6 claims `simp only` is "fractionally
  slower". For a tight inner loop, this matters; for one call site in a
  wrapper theorem, it does not. The actual cost is below the noise floor of
  Lean's elaboration timing.

- **Alternative: `change` tactic.** Another option for the wrapper is

  ```lean
  change Integrable (fun p : ℝ × ℝ => f p.1 p.2)
    ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d))) at hint
  ```

  which uses kernel defeq directly (and would succeed because of the `rfl`
  chain). But this is fragile under future Mathlib refactors (e.g., if
  `IntegrableOn` is redefined). The `rw [Measure.volume_eq_prod, ← Measure.prod_restrict ...]`
  is more robust and self-documenting.

- **`rw` placement of `Measure.volume_eq_prod`.** The replacement places
  `Measure.volume_eq_prod` AHEAD of `← Measure.prod_restrict` (rewrites
  `volume → volume.prod volume` first, then `.prod_restrict` backward
  fires). The opposite order (`← Measure.prod_restrict` first, then
  `Measure.volume_eq_prod`) would not work because the first rewrite would
  not fire at all (bare `volume`, no `.prod` structure).

- **Sibling `oq-01` is unaffected.** That sibling uses `Measure.pi` (n-dim
  product), not the binary `Measure.prod` on `ℝ × ℝ`. Different machinery,
  different drift. Out of scope.

- **AreaOfCircle import-side state.** This PREP assumes the file already
  imports `Mathlib.MeasureTheory.Measure.Prod` (where `volume_eq_prod` lives).
  The file imports `Mathlib.Analysis.SpecialFunctions.Polar` and
  `Mathlib.MeasureTheory.Integral.Polar` — both of which transitively import
  `Mathlib.MeasureTheory.Measure.Prod`. Confirmed by inspection of the
  import chain at v4.26.0.

## 12. S3 hand-off

After Mechanic / Doctor applies this corrected drift-sync:

- All 4 phantom call sites should compile cleanly.
- The wrapper, parent, sibling `oq-03`, and AreaOfCircle build (post-import fix).
- `meta.json` for the wrapper should be updated to `status: verified` (which
  it already claims, modulo the build-pending status flag).
- Gallery integration follows S3 plan from `state.md`.

## 13. Test plan

- [x] `Measure.volume_eq_prod` declaration verified at
      `Mathlib/MeasureTheory/Measure/Prod.lean:177-179` (rfl proof, confirms
      kernel defeq).
- [x] `Measure.prod_restrict` declaration verified at
      `Mathlib/MeasureTheory/Measure/Prod.lean:720-728` (signature with
      `(s : Set α) (t : Set β)` — no `MeasurableSet` hypotheses).
- [x] `Measure.volume_eq_prod` usage as `rw` step verified at
      `Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean:200` and
      `Mathlib/MeasureTheory/Integral/TorusIntegral.lean:223`.
- [x] `setIntegral_prod` internal usage verified at
      `Mathlib/MeasureTheory/Integral/Prod.lean:553-555` (does NOT need
      `volume_eq_prod` because measure is named `μ.prod ν` explicitly).
- [x] `prod.measureSpace` instance verified at
      `Mathlib/MeasureTheory/Measure/Prod.lean:173-174` (not marked
      `@[reducible]`).
- [x] No Lean build required — paper-and-pencil + Mathlib source evidence.
- [x] Race scan: 0 open PRs on slug; 3 merges in last 4h tapering;
      pristine addition.

---

**End of S2f PREP — doc-only audit of S2e PREP §1.2 / §2.3 / §4.2 rfl-unification
claim; corrects with `Measure.volume_eq_prod` prerequisite supported by Mathlib
v4.26.0 source-code evidence.**
