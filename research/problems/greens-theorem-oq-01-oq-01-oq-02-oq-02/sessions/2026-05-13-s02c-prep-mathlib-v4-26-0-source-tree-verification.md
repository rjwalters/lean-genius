# S2c PREP — Mathlib v4.26.0 source-tree verification (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-13 ~02:25 UTC
**Phase:** S2c PREP (orthogonal to S2b PREP, post-S2 SCAFFOLD)
**Iteration:** 4
**Builds on:**
- S2 SCAFFOLD (researcher-11, PR #18364, merged 2026-05-12 ~21:25 UTC; build pending).
- S2b PREP (researcher-10, PR #18444, doc-only Mathlib v4.26.0 API
  drift audit identifying `restrict_prod_eq_prod_restrict` as a phantom name
  and `Mathlib.MeasureTheory.Integral.IntervalIntegral` as a stale import).

## Why S2c (orthogonal to S2b)

S2b PREP flagged three Mathlib v4.26.0 drift items and proposed
drift-fix patches, but explicitly left **two of them unverified** by
static inspection — see § "Honesty / what could be wrong" of
`2026-05-13-s02b-prep-mathlib-drift-audit.md`:

1. The `← Measure.prod_restrict (uIcc a b) (uIcc c d)` direction and
   `volume = volume.prod volume` defeq unification — flagged as
   "build-validation-gated".
2. The exact spelling of `LocallyIntegrable.integrableOn_isCompact`
   at the v4.26.0 pin — flagged in S1 OBSERVE and S2 SCAFFOLD as a
   "name drift" risk, never closed.
3. Whether `Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic`
   transitively covers all symbols the parent uses (`measurableSet_uIcc`,
   `isCompact_uIcc`, etc.).

This PREP closes those three loose ends by direct GitHub Contents-API
inspection of `leanprover-community/mathlib4` at tag `v4.26.0` (equivalent
to the pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per
`proofs/lake-manifest.json`).

Doc-only — no Lean changes. The drift fix is still Doctor/Mechanic's
domain; this PREP gives them an exact punch list with source-tree line
numbers so the next build attempt is a single shot.

## Audit method

For each name, I used:

```bash
gh api "repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0" \
  --jq '.content' | base64 -d > /tmp/<file>
```

then `grep -n` for the symbol, and `sed -n '<start>,<end>p'` for the
signature. The commit ID returned by the Contents API for each file
(`gh api ... --jq '.sha'`) matches the v4.26.0 tag's tree.

## Verification 1 — `MeasureTheory.Measure.prod_restrict`

### Result: confirmed at `Mathlib/MeasureTheory/Measure/Prod.lean:720`

```lean
-- v4.26.0 Mathlib/MeasureTheory/Measure/Prod.lean:720
theorem prod_restrict (s : Set α) (t : Set β) :
    (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) := by
  rw [← sum_sfiniteSeq μ, ← sum_sfiniteSeq ν, restrict_sum_of_countable,
      restrict_sum_of_countable, prod_sum, prod_sum, restrict_sum_of_countable]
  ...
```

**Namespace.** Defined under `namespace MeasureTheory` (line 167) and
`namespace Measure` (line 169) ⇒ fully-qualified name is
`MeasureTheory.Measure.prod_restrict`. Within a file that has
`open MeasureTheory.Measure` (as the wrapper does at line 58), the bare
`prod_restrict` resolves correctly.

**Signature deltas vs the phantom `restrict_prod_eq_prod_restrict`:**

| Property | `restrict_prod_eq_prod_restrict` (phantom) | `Measure.prod_restrict` (real, v4.26.0) |
|---|---|---|
| Explicit args | `(hs : MeasurableSet s) (ht : MeasurableSet t)` | `(s : Set α) (t : Set β)` |
| Implicit args | `(μ : Measure α) (ν : Measure β)` (inferred) | same (inferred from outer namespace) |
| Direction | (presumed same as Mathlib's `prod_restrict`) | `(μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)` |
| Type-class hypotheses | (presumed none) | none |

The phantom name's two `MeasurableSet` arguments are surplus. The S2 SCAFFOLD
wrapper's call site at
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:89`:

```lean
rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
```

drops to (after drift fix):

```lean
rwa [← Measure.prod_restrict (uIcc a b) (uIcc c d)] at hint
```

— **no `measurableSet_uIcc` arguments needed**.

## Verification 2 — `volume = volume.prod volume` is `rfl`

### Result: confirmed at `Mathlib/MeasureTheory/Measure/Prod.lean:179`

```lean
-- v4.26.0 Mathlib/MeasureTheory/Measure/Prod.lean:179
theorem volume_eq_prod (α β) [MeasureSpace α] [MeasureSpace β] :
    (volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β) :=
  rfl
```

**Key fact: the proof is `rfl`.** This means `(volume : Measure (ℝ × ℝ))`
and `(volume : Measure ℝ).prod (volume : Measure ℝ)` are **definitionally
equal**. `rw` and `simp` should accept either form without an explicit
unfolding step, because the `rfl` is at the definitional level (not just
propositional).

**Practical implication for the drift-fix.** After the patch

```diff
-  rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
+  rwa [← Measure.prod_restrict (uIcc a b) (uIcc c d)] at hint
```

the `←` rewrite needs to match the RHS of `Measure.prod_restrict`:

```
(μ.prod ν).restrict (s ×ˢ t)
```

against `hint`'s actual form:

```
hint : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
        (volume.restrict (uIcc a b ×ˢ uIcc c d))
        -- ≡rfl: (volume.prod volume).restrict (uIcc a b ×ˢ uIcc c d)
```

The `rfl` defeq above guarantees the patterns unify. **No `simp only
[Measure.volume_eq_prod]` preamble is needed** at the type-theoretic
level, but Lean's elaborator sometimes prefers explicit `show` /
`change` for clarity. If `rwa` fails (rare), the bulletproof variant
is:

```lean
have hint' : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
    ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d))) := by
  rw [Measure.prod_restrict]; exact hint
exact hint'
```

— this does the rewrite in the forward direction on the goal, which
is structurally cleaner.

## Verification 3 — `LocallyIntegrable.integrableOn_isCompact`

### Result: confirmed at `Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:242`

```lean
-- v4.26.0 Mathlib/MeasureTheory/Function/LocallyIntegrable.lean:242
/-- If a function is locally integrable, then it is integrable on any compact set. -/
theorem LocallyIntegrable.integrableOn_isCompact [PseudoMetrizableSpace ε]
    {k : Set X} (hf : LocallyIntegrable f μ) (hk : IsCompact k) : IntegrableOn f k μ :=
  (hf.locallyIntegrableOn k).integrableOn_isCompact hk
```

**Name is exactly as the S1 OBSERVE / S2 SCAFFOLD assumed:**
`LocallyIntegrable.integrableOn_isCompact` (with `is`, no underscore-of).
No drift on this lemma name.

**Type-class hypothesis check.** The implicit `[PseudoMetrizableSpace ε]`
requires the codomain `ε` (here `ε = ℝ` for `f : ℝ × ℝ → ℝ`) to be
pseudo-metrizable. `ℝ` is a `MetricSpace` ⇒ `PseudoMetricSpace` ⇒
`PseudoMetrizableSpace` (via existing instances). Lean elaboration
should resolve this automatically; no new import needed beyond
`Mathlib.MeasureTheory.Function.LocallyIntegrable`.

**Sibling `LocallyIntegrableOn.integrableOn_isCompact`** also exists at
line 85 of the same file (for the relative version). Not what we want
here — the wrapper passes `LocallyIntegrable` (global), not
`LocallyIntegrableOn` (relative to a set).

## Verification 4 — `IntervalIntegral.Basic` import is sufficient

### Result: `Basic.lean` exists but does **not** carry every symbol the parent uses

The parent file `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean:24`:

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral  -- STALE at v4.26.0
```

This single-file path is gone at v4.26.0. The Contents API on
`Mathlib/MeasureTheory/Integral/IntervalIntegral?ref=v4.26.0` lists 9
files:

```
Basic.lean        ContDiff.lean     DerivIntegrable.lean
FundThmCalculus.lean   IntegrationByParts.lean   LebesgueDifferentiationThm.lean
Periodic.lean     Slope.lean        TrapezoidalRule.lean
```

The single-line drift fix is **almost certainly** sufficient:

```diff
-import Mathlib.MeasureTheory.Integral.IntervalIntegral
+import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
```

because:

- `Basic.lean` defines `intervalIntegral` (line 617): `∫ x in a..b, f x ∂μ`.
- `Basic.lean` provides `intervalIntegral_eq_integral_uIoc` (line 650),
  used in the parent's `integral_of_le` rewrites.
- `Basic.lean` transitively imports `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`
  and `Mathlib.MeasureTheory.Topology`, which pull in `volume` on ℝ.

**Symbols NOT in `Basic.lean` that the parent uses.** The parent's
proof script at line 191 calls `measurableSet_uIcc` and `isCompact_uIcc`.
A grep in v4.26.0 confirms:

| Symbol | v4.26.0 location |
|---|---|
| `measurableSet_uIcc` | `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean:550` |
| `isCompact_uIcc` | `Mathlib/Topology/Order/Compact.lean` (search hit) |

Neither lives in `IntervalIntegral/Basic.lean`. **However**, the parent's
other imports (`Mathlib.MeasureTheory.Integral.Prod` at line 25 and
`Mathlib.MeasureTheory.Measure.Prod` at line 26) should transitively
pull `Mathlib.MeasureTheory.Constructions.BorelSpace.Order` and the
topology-side compactness lemmas — `BorelSpace/Order.lean` is a
foundational measure-theory file imported by anything that talks about
intervals.

**Risk.** If the `Basic.lean` swap is *not* sufficient, the parent
file will fail to build with an "unknown identifier `measurableSet_uIcc`"
(or `isCompact_uIcc`) error. The fix is an additional explicit import:

```lean
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
```

This is mentioned here so Mechanic's first build attempt can include
the explicit import as a safety net; if the build is green with only
the `Basic.lean` swap, the explicit `BorelSpace.Order` import can be
removed in a follow-up.

## Verification 5 — `Mathlib.MeasureTheory.Integral.Prod` path stable

### Result: confirmed; carries `integral_integral_swap` at line 534

```lean
-- v4.26.0 Mathlib/MeasureTheory/Integral/Prod.lean:534
/-- Change the order of Bochner integration. -/
theorem integral_integral_swap ⦃f : α → β → E⦄
    (hf : Integrable (uncurry f) (μ.prod ν)) :
    ∫ x, ∫ y, f x y ∂ν ∂μ = ∫ y, ∫ x, f x y ∂μ ∂ν :=
  (integral_integral hf).trans (integral_prod_symm _ hf)
```

The parent file's other Mathlib import,

```lean
import Mathlib.MeasureTheory.Integral.Prod
```

is still at the correct path — no drift fix needed for this line.
Confirms S2b PREP § "Drift item 2" comment that this import "appears
to be at the correct path already".

**Bonus observation.** Mathlib v4.26.0 also has a near-relative at
`Prod.lean:539`:

```lean
lemma intervalIntegral_integral_swap {a b : ℝ} {f : ℝ → α → E}
    (h_int : Integrable (uncurry f) ((volume.restrict (Set.uIoc a b)).prod μ)) :
    ∫ x in a..b, ∫ y, f x y ∂μ = ∫ y, (∫ x in a..b, f x y) ∂μ := by ...
```

This is a **one-sided** interval-integral swap (one interval-integral,
one ordinary integral), with `uIoc` (open-closed) rather than `uIcc`
(closed). It is **not a drop-in replacement** for the parent's
two-sided `intervalIntegral_swap`, but is informational for any future
slug that wants to derive the parent's theorem from upstream Mathlib
directly. Not in scope for this PREP.

## Cross-file impact (refined from S2b PREP § "Cross-file impact")

S2b PREP listed 5 files with `restrict_prod_eq_prod_restrict`. Refined
table with v4.26.0-confirmed drift-fix:

| File | Line | Owner slug | Drift-fix |
|---|---|---|---|
| `Proofs/GreensTheoremOQ01OQ01OQ02.lean` | 191 | `greens-theorem-oq-01-oq-01-oq-02` | `← Measure.prod_restrict (uIcc a b) (uIcc c d)` AND `import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic` |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` | 89 | **this slug** | `← Measure.prod_restrict (uIcc a b) (uIcc c d)` (inherits parent's import fix transitively) |
| `Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean` | 214 | sibling `oq-03` | `← Measure.prod_restrict (uIcc a b) (uIcc c d)` (check sibling-specific imports separately) |
| `Proofs/AreaOfCircleOQ05OQ01.lean` | 152 | `area-of-circle-oq-05-oq-01` | `← Measure.prod_restrict <Set1> <Set2>` with sets matching that file's usage |
| `Proofs/GreensTheoremOQ01OQ01OQ01.lean` | 59 | sibling `oq-01` | Comment-only line — no Lean change, but update the comment text |

**Minimal patch sequence for Mechanic** (single PR, four code files
+ one comment file):

```bash
# 1. Phantom-name replacement (one sed across 4 .lean files):
git grep -l 'restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc' proofs/Proofs/ \
  | xargs sed -i '' -e 's|restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc|← Measure.prod_restrict (uIcc a b) (uIcc c d)|'
# (Note: AreaOfCircleOQ05OQ01.lean:152 may have different Set arguments — eyeball before sed.)

# 2. IntervalIntegral import fix (single line in parent):
sed -i '' -e 's|import Mathlib.MeasureTheory.Integral.IntervalIntegral$|import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic|' \
  proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean
# (Also check sibling oq-01 has Mathlib.Logic.Equiv.Fin → presumably .Basic or similar; S2b § "Drift item 3".)

# 3. Comment update in oq-01:
# Edit Proofs/GreensTheoremOQ01OQ01OQ01.lean:59 manually to drop the phantom name from the comment.

# 4. Docker build to verify:
./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02
# Builds this slug's wrapper, which transitively builds the parent.
```

## Anti-targets (this S2c PREP explicitly does NOT do)

1. **Does not modify any Lean file.** All proposed drift-fix patches
   are documentation; Doctor/Mechanic owns the code change. This PR
   creates only one new file:
   `research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-13-s02c-prep-mathlib-v4-26-0-source-tree-verification.md`.
2. **Does not modify `state.md`, `knowledge.md`, `problem.md`, the
   gallery JSON, or `meta.json`.** Strictly additive `sessions/` file
   — pristine conflict-free against any in-flight Doctor/Mechanic
   PR.
3. **Does not run the docker build.** Project memory
   (`feedback_researcher_lake_symlink_loop_and_wipe.md`) warns that
   the `.lake` symlink loop can wipe the worktree mid-build; the
   drift-fix build is Doctor/Mechanic's domain.
4. **Does not bump the S2 SCAFFOLD's "build pending" status.**
5. **Does not propose any Mathlib upstream contribution name change.**
   The seeker question (Mathlib upstream candidacy of the wrapper) is
   still open; that's S3+'s domain after the build is green.
6. **Does not search for sibling `oq-01`'s `Mathlib.Logic.Equiv.Fin`
   drift fix.** Cited in S2b PREP § "Drift item 3"; out of scope for
   this slug (sibling `oq-01` is a different file and a different
   research problem).

## Honesty / what could be wrong

- The v4.26.0 line numbers (720 for `prod_restrict`, 179 for
  `volume_eq_prod`, 242 for `LocallyIntegrable.integrableOn_isCompact`)
  are from the GitHub Contents API at tag `v4.26.0` on 2026-05-13.
  If Mathlib retags `v4.26.0` (rare but possible for re-tags), the
  line numbers may drift; the lemma names and signatures should be
  stable.
- The `rfl` claim about `volume_eq_prod` is confirmed by reading the
  source line directly. Whether Lean's `rw [← Measure.prod_restrict]`
  unifies through that `rfl` is a build-time matter (in practice
  `rfl`-level defeq is the easiest case for `rw`, so this should
  succeed).
- The `[PseudoMetrizableSpace ε]` typeclass requirement on
  `LocallyIntegrable.integrableOn_isCompact` for `ε = ℝ` is satisfied
  via the standard `MetricSpace ℝ → PseudoMetricSpace ℝ →
  PseudoMetrizableSpace ℝ` instance chain. I did not directly verify
  the instance chain; if Lean fails to synthesize it, an explicit
  `inferInstance : PseudoMetrizableSpace ℝ` or
  `Real.instPseudoMetricSpace` may be needed.
- Coverage of `measurableSet_uIcc` / `isCompact_uIcc` through the
  parent's existing imports (`MeasureTheory.Integral.Prod`,
  `MeasureTheory.Measure.Prod`) is presumed-transitive but not
  syntactically traced through every transitive `import` line. If
  the build errors on "unknown identifier", an explicit
  `import Mathlib.MeasureTheory.Constructions.BorelSpace.Order` is
  the safety net.
- I assume `Mathlib.MeasureTheory.Integral.Prod` is unchanged at
  v4.26.0 because the GitHub search-code hit returns it directly and
  the `integral_integral_swap` signature is read verbatim from
  v4.26.0's source. If the file itself was renamed/restructured (not
  evidenced), Mechanic's build will surface that.
- The cross-file impact table presumes `AreaOfCircleOQ05OQ01.lean:152`
  uses the same phantom-name pattern; I have not opened that file. The
  S2b PREP cross-file table flags it but does not transcribe the
  call-site. Mechanic should eyeball it before applying the sed.

## Race awareness

Pre-push checks (2026-05-13 ~02:25 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title"` returns 0 PRs
  on the **exact** `oq-02-oq-02` slug.
- `git branch -r | grep "greens-theorem-oq-01-oq-01-oq-02-oq-02"`
  returns 0 branches on this exact slug.
- `gh pr list --repo rjwalters/lean-genius --state open --search
  "drift greens OR mechanic greens OR doctor greens OR sync greens"`
  returns 0 open Mechanic/Doctor drift-sync PRs on the greens family.
- Open audit branches `audit/greens-*` are stale (pre-v4.26.0 era,
  unrelated to phantom-name drift).
- No `audit/sync-greens-theorem-oq-01-oq-01-oq-02-oq-02*` branches
  exist.

This PR is orthogonal by construction to:
- S2 SCAFFOLD (PR #18364, merged) — that PR introduced the wrapper
  Lean file; this PR is a follow-up audit document, no Lean change.
- S2b PREP (PR #18444) — that PR identified the drift; this PR
  closes the verification loop on the proposed fix using source-tree
  line numbers.
- Sibling `oq-01`'s in-flight PRs (#17822, #17838, #17840) — different
  Lean file (`GreensTheoremOQ01OQ01OQ02OQ01.lean`), different slug,
  no path conflict with this slug's `sessions/`.

## Next iteration after this PREP

Two paths, in decreasing preference:

1. **Doctor/Mechanic drift-sync.** Apply the patch sequence above to
   the 5 affected files. Run docker build on
   `Proofs.GreensTheoremOQ01OQ01OQ02OQ02`. If green, update meta.json
   for the parent slug, all OQ children, and `area-of-circle-oq-05-oq-01`
   in lockstep. This is family-wide and cheap.
2. **A researcher iteration ships S2c ACT on this slug alone.**
   Modify *only* `GreensTheoremOQ01OQ01OQ02OQ02.lean` (the wrapper)
   and inline a stand-alone `prod_restrict`-based proof that does not
   depend on the parent. ~100 LOC duplication; decouples this slug's
   verification from the parent's drift risk. Worse than path 1 for
   the family, but viable if Mechanic is over-saturated.

After the build is green:

- S3 finalization for this slug: update
  `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02.json`
  with `status: completed`, `axiomCount: 0`, `sorryCount: 0`, link to
  the built wrapper file.
- Update `state.md` Phase: `S3 ACT (build-verified)`.
- `knowledge.md` § Mathlib upstream: this wrapper is exactly the kind
  of small ergonomic improvement Mathlib welcomes; suggested target
  file is `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean`
  (the new `Basic.lean` of the directory, near
  `intervalIntegral_eq_integral_uIoc` at line 650, where iterated
  interval-integral utilities naturally live).

## Future status

Unchanged from S2b PREP: once the drift is fixed and the build passes,
this wrapper will be **`verified`** (not `axiomatized`). The proof is
a 5-line reduction to the parent; the parent itself uses only standard
Mathlib API (now confirmed name-and-line-by-line at v4.26.0); the
wrapper introduces zero `axiom` declarations and zero `sorry` markers.
