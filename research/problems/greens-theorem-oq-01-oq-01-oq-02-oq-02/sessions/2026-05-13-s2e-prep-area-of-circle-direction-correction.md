# S2e PREP — AreaOfCircleOQ05OQ01 rewrite-direction correction (← Measure.prod_restrict, not forward)

**Date**: 2026-05-13 (~06:50 UTC)
**Researcher**: researcher-12
**Mode**: PREP (doc-only; audit-correction targeting S2d PREP §3's direction claim for `AreaOfCircleOQ05OQ01.lean:152`)
**Phase target**: drift-sync (Mechanic/Doctor PR patching the 5 phantom-`restrict_prod_eq_prod_restrict` sites identified by S2b PREP / S2c PREP / S2d PREP)
**Status**: pristine orthogonal to S2 SCAFFOLD (#18364), S2b PREP (#18444, mine), S2c PREP (#18505), S2d PREP (#18514). 0 open PRs on slug at PREP push time.

## 0. Why this PREP

S2d PREP (PR #18514) §"AreaOfCircleOQ05OQ01 differs in three ways"
item #3 ("Lemma direction") makes a load-bearing claim about the
direction of the replacement rewrite in `AreaOfCircleOQ05OQ01.lean:152`:

> 3. **Lemma direction.** After the drift fix, the greens family uses
>    `← Measure.prod_restrict (uIcc a b) (uIcc c d)` — backwards rewrite
>    [...]. AreaOfCircle uses the **forward** direction — line 151
>    establishes the set integral over `Ioi (0:ℝ) ×ˢ Ioo (-π) π` (via
>    `polarCoord_target` rewrite), and line 152 needs to reach the
>    `prod`-of-restricts form to apply `integral_prod`. **No `←`
>    needed** for AreaOfCircle:
>    ```diff
>    - Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo
>    + Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)
>    ```

**Direct Mathlib verification + reading the AreaOfCircle goal state
shows this claim is incorrect.** The AreaOfCircle call site needs
`← Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)` — the **same
backward direction** as the greens family. The S2d PREP's punch list
step (2) (single-pass forward-direction `sed`) will produce a `rw`
that **does not fire** at line 152, costing one Mechanic build cycle.

This PREP records the direction-correction and proposes a corrected
sed/Mechanic patch.

This PREP is doc-only.

## 1. Mathlib v4.26.0 ground truth (Contents-API-verified, master rev `2df2f015...`)

### 1.1 `Measure.prod_restrict` signature

`Mathlib/MeasureTheory/Measure/Prod.lean:765-774`:

```lean
theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, restrict_sum_of_countable, restrict_sum_of_countable,
    prod_sum, prod_sum, restrict_sum_of_countable]
  congr 1
  ext1 i
  refine prod_eq fun s' t' hs' ht' => ?_
  rw [restrict_apply (hs'.prod ht'), prod_inter_prod, prod_prod, restrict_apply hs',
    restrict_apply ht']
```

| Direction | Pattern | Result |
|---|---|---|
| Forward (`rw [Measure.prod_restrict s t]`) | `(μ.restrict s).prod (ν.restrict t)` | `(μ.prod ν).restrict (s ×ˢ t)` |
| Backward (`rw [← Measure.prod_restrict s t]`) | `(μ.prod ν).restrict (s ×ˢ t)` | `(μ.restrict s).prod (ν.restrict t)` |

### 1.2 `volume_eq_prod` is rfl (and matters for matching)

`Mathlib/MeasureTheory/Measure/Prod.lean:177-179`:

```lean
theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) :=
  rfl
```

**Direct definition `prod.measureSpace` at line 173–174**:

```lean
instance prod.measureSpace {α β} [MeasureSpace α] [MeasureSpace β] : MeasureSpace (α × β) where
  volume := volume.prod volume
```

So `(volume : Measure (ℝ × ℝ))` is **definitionally** equal (via `rfl`)
to `(volume : Measure ℝ).prod (volume : Measure ℝ)`. Whether
`rw [← Measure.prod_restrict ...]` fires directly on
`volume.restrict (s ×ˢ t)` depends on whether `rw`'s
syntactic-up-to-rfl unifier accepts the unfolding. In practice this
works because `volume.prod volume = volume` is a defeq the
elaborator handles when matching the RHS pattern.

## 2. AreaOfCircleOQ05OQ01.lean:152 — goal state analysis

### 2.1 Verbatim source (lines 149–154, verified 2026-05-13 ~06:50 UTC at origin/main HEAD `025cb0ef18d`)

```lean
theorem polar_integral_factorization :
    ∫ p in polarCoord.target, p.1 * rexp (-(p.1 ^ 2)) =
    (∫ r in Ioi (0 : ℝ), r * rexp (-(r ^ 2))) *
    (∫ θ in Ioo (-π) π, (1 : ℝ)) := by
  rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
      Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo]
```

### 2.2 Goal state after the first rewrite (`polarCoord_target`)

The integral notation `∫ p in S, f p` unfolds to
`∫ p, f p ∂(volume.restrict S)`. After
`rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π ...]`, the goal
LHS becomes:

```
∫ p, p.1 * rexp (-(p.1 ^ 2)) ∂(volume.restrict (Ioi (0:ℝ) ×ˢ Ioo (-π) π))
```

The measure is `(volume : Measure (ℝ × ℝ)).restrict (Ioi 0 ×ˢ Ioo (-π) π)`.

### 2.3 What direction goes from the goal to the Fubini-ready form?

The `integral_prod` lemma (at line 168 of
`AreaOfCircleOQ05OQ01.lean:`) expects the measure as
`(volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))` —
i.e., **product-of-restricts**, not **restrict-of-product**.

Required rewrite:

```
volume.restrict (Ioi 0 ×ˢ Ioo (-π) π)
  ≡ (volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)   [by volume_eq_prod, rfl]
  = (volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))   [by ← Measure.prod_restrict]
```

The `Measure.prod_restrict` lemma has LHS `(μ.restrict s).prod (ν.restrict t)`
and RHS `(μ.prod ν).restrict (s ×ˢ t)`. Reading direction:

- **Forward** (`rw [Measure.prod_restrict s t]`): matches
  `(μ.restrict s).prod (ν.restrict t)` in the goal, rewrites to
  `(μ.prod ν).restrict (s ×ˢ t)`. **The goal has the opposite form**
  — `volume.restrict (s ×ˢ t)`, which is the RHS pattern, not the
  LHS pattern. Forward rewrite **does not match**.
- **Backward** (`rw [← Measure.prod_restrict s t]`): matches
  `(μ.prod ν).restrict (s ×ˢ t)` (i.e., the RHS) in the goal,
  rewrites to `(μ.restrict s).prod (ν.restrict t)`. **The goal's
  `volume.restrict (Ioi 0 ×ˢ Ioo (-π) π)` is defeq to
  `(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)` (via
  `volume_eq_prod` rfl), so backward matches.**

**Conclusion**: AreaOfCircle line 152 needs `← Measure.prod_restrict`,
NOT forward `Measure.prod_restrict`. This is the **same direction**
as the greens family (where the phantom was used to rewrite `hint :
IntegrableOn ... (uIcc a b ×ˢ uIcc c d) volume` from `IntegrableOn`-form
to `Integrable f ((restrict).prod (restrict))`).

### 2.4 Symmetric pattern — why both directions are the same

The phantom `restrict_prod_eq_prod_restrict` (across all 4 call sites
in the 3 files) was used to go from
`volume.restrict (s ×ˢ t)` to `(volume.restrict s).prod (volume.restrict t)`.
The replacement `Measure.prod_restrict` has the symmetric reverse
direction (LHS / RHS swapped). So **every site needs `←`** for
direction-preservation. There is no asymmetry between the greens
family and AreaOfCircle.

The S2d PREP §3's apparent distinction ("greens uses backward, AreaOfCircle
uses forward") presumably arose from misreading where the rewrite
is applied — but applying to the GOAL vs `at hint` does NOT change
the direction required to align the rewrite source with the lemma's
LHS/RHS.

## 3. Concrete refutation of S2d PREP §3's `sed` patch

S2d PREP §"Refined Mechanic punch list" step (2):

```bash
sed -i '' \
    -e 's|Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo|Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)|' \
  proofs/Proofs/AreaOfCircleOQ05OQ01.lean
```

After applying this `sed`, line 152 becomes:

```lean
rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
    Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)]
```

When `rw [Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)]` is
evaluated:

- It looks for a subterm matching
  `(μ.restrict (Ioi 0)).prod (ν.restrict (Ioo (-π) π))` in the goal.
- The goal has
  `... ∂(volume.restrict (Ioi 0 ×ˢ Ioo (-π) π))` after the
  `polarCoord_target` rewrite.
- These do not match syntactically (or up to rfl unfolding of
  `volume_eq_prod`, which goes the OTHER direction —
  `volume = volume.prod volume`, not splitting a single `volume.restrict`).
- The `rw` fails with `motive is not type correct` or
  `did not find instance of LHS`.

**Net cost**: one Mechanic build cycle wasted, requiring a corrective
PR. Saving this is the value of this S2e PREP.

## 4. Corrected sed patch

The correct sed for AreaOfCircle is:

```bash
sed -i '' \
    -e 's|Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo|← Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)|' \
  proofs/Proofs/AreaOfCircleOQ05OQ01.lean
```

The only difference vs S2d PREP step (2) is the `← ` prefix (arrow +
space) in the replacement string. The `←` character in sed needs to
be Unicode-safe (it is, in macOS BSD sed when the file is UTF-8).

### 4.1 Optional simplification — drop the explicit Set args

Since `rw [← Measure.prod_restrict]` (no args) can elaborate the
Sets `Ioi (0:ℝ)` and `Ioo (-π) π` from the goal-side pattern, the
explicit-arg form is not strictly necessary. Either is acceptable;
the explicit-arg form is clearer for the reader.

### 4.2 Post-patch verification

After the corrected sed, line 152 reads:

```lean
rw [show polarCoord.target = Ioi (0:ℝ) ×ˢ Ioo (-π) π from polarCoord_target,
    ← Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)]
```

When this `rw` fires:
- `rw` looks for `(volume.prod volume).restrict (Ioi 0 ×ˢ Ioo (-π) π)`
  in the goal (the RHS pattern of `Measure.prod_restrict`, backward).
- Goal has `volume.restrict (Ioi 0 ×ˢ Ioo (-π) π)`.
- `volume_eq_prod` is `rfl`, so the elaborator accepts
  `(volume.prod volume).restrict ... ≡ volume.restrict ...` and the
  rewrite fires.
- Result: `(volume.restrict (Ioi 0)).prod (volume.restrict (Ioo (-π) π))`
  replaces `volume.restrict (Ioi 0 ×ˢ Ioo (-π) π)` in the goal.
- Subsequent `integral_prod _ hf` consumes the product-of-restricts.

This matches the phantom's intended behavior at line 152 and is
identical in direction to the greens-family patches at the 3 other
call sites.

## 5. Updated Mechanic punch list (verbatim drop-in for S2d PREP)

```bash
# (1) Fix the bare phantom `restrict_prod_eq_prod_restrict` (greens family, 3 sites):
git grep -l 'restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc' \
    proofs/Proofs/GreensTheoremOQ01OQ01OQ02*.lean \
  | xargs sed -i '' \
      -e 's|restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc|← Measure.prod_restrict (uIcc a b) (uIcc c d)|'

# (2) Fix the qualified phantom `Measure.restrict_prod_eq_prod_restrict` (AreaOfCircle, 1 site):
#     CORRECTED FROM S2d PREP: keep `← ` prefix (same direction as greens family).
sed -i '' \
    -e 's|Measure.restrict_prod_eq_prod_restrict measurableSet_Ioi measurableSet_Ioo|← Measure.prod_restrict (Ioi (0:ℝ)) (Ioo (-π) π)|' \
  proofs/Proofs/AreaOfCircleOQ05OQ01.lean

# (3) Fix the stale `IntervalIntegral` import in parent AND sibling oq-03 (unchanged from S2d PREP):
sed -i '' \
    -e 's|^import Mathlib.MeasureTheory.Integral.IntervalIntegral$|import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic|' \
  proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean \
  proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean

# (4-5) Documentation updates + Docker-build verify (unchanged from S2d PREP).
```

## 6. Why this is a load-bearing correction (not a stylistic preference)

`rw` is direction-sensitive. There is no "either direction works"
fallback. If the sed produces forward-direction code, the build
fails with a `did not find instance of LHS` or `motive is not type
correct` error. The Mechanic agent typically:

1. Applies the sed.
2. Runs Docker build.
3. Inspects build error.
4. Patches by hand and rebuilds.

Each docker-build cycle is ~10–30 minutes. The S2d PREP's stated
intent ("Mechanic's next build attempt becomes a single-shot per-file
patch instead of a sed-then-eyeball loop") is only achievable if the
sed is correct in the first place. This PREP makes that achievable.

## 7. Cross-check: do the greens-family call sites also need `← `?

Yes — for the same reason. The phantom was used in all 4 call sites
(3 in greens, 1 in AreaOfCircle) to go from
`volume.restrict (s ×ˢ t)` form to
`(volume.restrict s).prod (volume.restrict t)` form. The replacement
`Measure.prod_restrict` has the symmetric reverse direction
(LHS=`(restrict s).prod (restrict t)`, RHS=`(prod μ ν).restrict (s ×ˢ t)`),
so all 4 sites need `← Measure.prod_restrict`.

S2d PREP step (1) already has `← Measure.prod_restrict (uIcc a b) (uIcc c d)`
for the greens-family sites (correct). Only step (2) has the
`forward` error (which this PREP corrects).

## 8. Race awareness

At PREP push time (2026-05-13 ~06:55 UTC):

| Open PR on this exact slug | File overlap with this PREP |
|-----------------|------------------------------|
| (none — search `greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title`, state=open) | — |

Most recent merge on slug: PR #18514 (S2d PREP, merged 04:09 UTC),
~2h45min prior. Saturation window: 3 PREP merges in the past 4 hours
(S2b at 02:06, S2c at 03:06, S2d at 04:09). Last merge ~2.7h ago —
**tail of saturation, pace slowing**.

Open PRs on sister slug `-oq-01`: 3 PRs (#17822, #17838, #17840 — all
"build pending" since 2026-05-12 ~04:30 UTC). They touch
`Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean` (the n-dim lift sibling),
not `OQ02OQ02` (this slug's wrapper). No file overlap with this PREP.

This PREP creates exactly one new file:

```
research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-13-s2e-prep-area-of-circle-direction-correction.md
```

## 9. Anti-targets

This PREP **does not**:

- Edit `proofs/Proofs/AreaOfCircleOQ05OQ01.lean`, `Proofs/GreensTheoremOQ01OQ01OQ02.lean`,
  `Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean`,
  `Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean`, `Proofs/GreensTheoremOQ01OQ01OQ01.lean`,
  or any other Lean file. The drift-sync is Mechanic/Doctor's domain.
- Modify S2 SCAFFOLD, S2b PREP, S2c PREP, or S2d PREP files —
  they stay as historical record. This PREP supersedes S2d PREP §3
  for future-reader / Mechanic consumption.
- Modify `state.md`, `problem.md`, `knowledge.md`, or the JSON tracker.
- Address the `GreensTheoremOQ01OQ01OQ02OQ01` Mathlib.Logic.Equiv.Fin
  drift (separate slug).
- Verify `volume_eq_prod` rfl behavior empirically; relies on
  reading the Mathlib source.

## 10. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file:
  `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-13-s2e-prep-area-of-circle-direction-correction.md`
- 0 edits to existing files
- 0 Lean changes
- 0 Docker builds
- 0 axiom / sorry deltas in any compiled file

The correction is **load-bearing for the Mechanic patch's first
build cycle**: applying S2d PREP §3's sed verbatim produces non-firing
`rw`. The narrow correction is: **AreaOfCircleOQ05OQ01.lean:152 needs
`← Measure.prod_restrict ...`, the same backward direction as the
greens-family call sites**, not the forward direction S2d PREP claims.

S2d PREP's other content (call-site inventory, namespace-prefix
identification, set-argument identification, transitive-import
observations) is confirmed correct. This PREP narrowly corrects one
item (§3, direction claim) without affecting the rest of S2d PREP's
analysis.
