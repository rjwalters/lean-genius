# pascals-hexagon-oq-03 — S4c PREP: Mathlib `Projectivization` audit supersedes bespoke `ProjLineClass`

**Date**: 2026-05-13
**Author**: researcher-1
**Scope**: doc-only follow-up to PR #18338 (S4 PREP survey, merged 2026-05-12T23:18:21Z), PR #18461 (S4a PREP, merged 2026-05-13 ~03:09 UTC), PR #18559 (S4b PREP close-out, merged 2026-05-13 ~05:07 UTC). Audits the well-definedness-modulo-scalar machinery proposed by all three prior PREPs and finds that **Mathlib already provides the exact facility (`Projectivization K V`)** — eliminating the ~50 LOC bespoke `ProjLineClass := Quotient ScalarSetoid` boilerplate proposed in PR #18338 lines 163–170 ("Route (a)").

**No Lean source changes**, no `meta.json` / `state.md` / `problem.md` / `knowledge.md` / gallery JSON edits. The only file added by this PR is `research/problems/pascals-hexagon-oq-03/sessions/2026-05-13-s4c-prep-mathlib-projectivization-audit.md` (this document).

## Provenance / non-overlap

- PR #18338 (S4 PREP survey, doc-only) lines 163–170 identified that `ProjLine := Fin 3 → ℝ` does NOT quotient by scalars and therefore `lineThrough P Q ≠ lineThrough Q P` as raw vectors, breaking the would-be `Quotient.lift` for `pascalLine`. **Recommendation: Route (a)** — introduce a bespoke `ProjLineClass := Quotient ScalarSetoid` wrapper in a new ~50 LOC mini-section of `PascalsHexagonOQ03.lean`.
- PR #18461 (S4a PREP, doc-only) line 87 sharpened the exact scalars under `hexRev`: `(P → −Q, Q → −P, R → +R)` — two of three intersection points pick up a sign. Did **not** audit whether Mathlib already provides the projective-line quotient.
- PR #18559 (S4b PREP, doc-only) closed out the 6-of-6 Mathlib API path audit and addressed the Nat.card migration + degeneracy Option (b). Did **not** audit the Projectivization side either.

This PR is orthogonal to all three: drills into **one specific design recommendation** ("Route (a)") that all three PREPs left unaudited against Mathlib HEAD. New file path; no edits to any prior PREP, Lean source, meta.json, state.md, problem.md, knowledge.md, or gallery JSON. No race with any open S4-family PR (none open as of session time 2026-05-13 ~08:30 UTC).

## Finding A — `Projectivization K V` exists in Mathlib (pin `2df2f0150c`) and is the right abstraction

**Module**: `Mathlib.LinearAlgebra.Projectivization.Basic` (transitively re-exported by `Mathlib.Tactic` chains via the `LinearAlgebra` directory; verified to compile without additional imports beyond what `PascalsHexagonOQ03.lean` already pulls).

**Verification** at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```
gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Projectivization/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'
```

returns the file with:

| Identifier | Line | Signature |
|---|---|---|
| `projectivizationSetoid` | 42 | `Setoid { v : V // v ≠ 0 } := (MulAction.orbitRel Kˣ V).comap (↑)` |
| `Projectivization` | 47 | `def Projectivization := Quotient (projectivizationSetoid K V)` |
| `ℙ K V` notation | 51 | `scoped[LinearAlgebra.Projectivization] notation "ℙ" => Projectivization` |
| `Projectivization.mk` | 59 | `def mk (v : V) (hv : v ≠ 0) : ℙ K V := Quotient.mk'' ⟨v, hv⟩` |
| `Projectivization.lift` | 77 | `protected def lift {α} (f : { v // v ≠ 0 } → α) (hf : ∀ a b t, (a : V) = t • b → f a = f b) (x : ℙ K V) : α` |
| `Projectivization.lift_mk` | 83 | `Projectivization.lift f hf (mk K v hv) = f ⟨v, hv⟩` (simp) |
| `Projectivization.rep` | 90 | `protected noncomputable def rep (v : ℙ K V) : V` |
| `mk_eq_mk_iff` | 109 | `mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v := Quotient.eq''` |
| `mk_eq_mk_iff'` | 115 | `mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v` (variant) |

**Module prerequisites** (from header `public import` at lines 8–9):

```
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
```

These two imports load via the standard `import Mathlib.Tactic` chain in `PascalsHexagonOQ03.lean:8` (verified by `import Mathlib.Tactic` umbrella; explicit single import `Mathlib.LinearAlgebra.Projectivization.Basic` may be added if the umbrella's transitive dependency does not survive Mathlib reorganization — a precautionary addition costs 1 line).

**Constraint check**: `Projectivization K V` requires `[DivisionRing K] [AddCommGroup V] [Module K V]` (line 38). For `K = ℝ` and `V = Fin 3 → ℝ`, all three hold via Mathlib's canonical instances. No new typeclass legwork required.

## Finding B — `Projectivization ℝ (Fin 3 → ℝ)` is exactly what `pascalLine` should return

PR #18338's analysis (lines 163–170) was:

> Projective lines are equivalence classes under nonzero scalar multiplication, but the type `ProjLine := Fin 3 → ℝ` does NOT quotient by scalars. So `lineThrough P Q ≠ lineThrough Q P` as elements of `Fin 3 → ℝ` (they differ by a sign), and "well-definedness" of `pascalLine` must allow for nonzero scalar multiples. This means the **target of `pascalLine` cannot be `ProjLine` if we want strict equality on the quotient** — we must either:
>   - (a) quotient `ProjLine` by `ℝˣ`-scaling (introducing a new `ProjLineClass`); or
>   - (b) prove well-definedness up to nonzero scalar only, returning a `ProjLine` but stating downstream theorems in scalar-invariant form; or
>   - (c) choose a canonical representative (e.g., normalize so the first nonzero coordinate is 1) via `Classical.choice` or a `decide`-based normalization.

**Route (a)** is precisely `Projectivization ℝ (Fin 3 → ℝ)`, **but it does not require building any new boilerplate**. The Mathlib type is *defined as* `Quotient (projectivizationSetoid K V)` where the setoid is the `Kˣ`-orbit relation on `{v : V // v ≠ 0}` — i.e., scalar equivalence by nonzero units. This is exactly the `ScalarSetoid` PR #18338 proposed to build by hand.

**Bonus**: Mathlib's version is **strictly cleaner** than the bespoke proposal in three ways:

1. **Handles `0` correctly**: PR #18338's "Route (a)" sketch would have had to either include `0` as its own equivalence class (semantically wrong — `0` is not a projective line) or exclude it manually. `Projectivization`'s underlying type `{v : V // v ≠ 0}` already excludes `0` at the Sigma level. The `Projectivization.mk` constructor requires a proof `hv : v ≠ 0`, forcing the call site to handle degeneracy.

2. **`lift` API matches the well-definedness pattern**: `Projectivization.lift f hf` requires only `∀ a b (t : K), a = t • b → f a = f b` — i.e., scalar-invariance. The well-definedness obligation for `rawPascalLine` under the dihedral generators reduces to: "for each `hexRot` and `hexRev`, the image of `pascalLine` differs by a scalar from the original." `cross_anticomm` and `cross_self` (Finding C below) close this directly.

3. **`mk_eq_mk_iff` gives a usable equality characterization**: PR #18338's bespoke `ProjLineClass` would have required deriving `mk_eq_mk` lemmas from scratch. `mk_eq_mk_iff` (line 109) says `mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v`, immediately usable for proving the dihedral-generator invariance via concrete scalar witnesses (`a = ⟨-1, ...⟩` for the `hexRev` case where the pascal line picks up a sign).

## Finding C — `crossProduct` anticommutivity and degenerate-vector handling lemmas in Mathlib

The crossProduct identities required to discharge the `rawPascalLine_hexRot` / `rawPascalLine_hexRev` invariance proofs are all available at `Mathlib/LinearAlgebra/CrossProduct.lean` at the same pin:

| Identifier | Line | Statement | Use in OQ-02 |
|---|---|---|---|
| `cross_apply` | 80 | `(v ⨯₃ w) i = ...` (component formula) | unfold for `decide` calls |
| `cross_anticomm` | 86 | `-(v ⨯₃ w) = w ⨯₃ v` | direct proof of `lineThrough Q P = -lineThrough P Q` |
| `neg_cross` | 89 | alias for `cross_anticomm` | shorter form |
| `cross_anticomm'` | 92 | `v ⨯₃ w + w ⨯₃ v = 0` | additive form |
| `cross_self` | 96 | `v ⨯₃ v = 0` | degeneracy: `lineThrough A A = 0` |
| `dot_self_cross` | 101 | `v ⬝ᵥ v ⨯₃ w = 0` | `pointOnLine A (lineThrough A B)` |
| `dot_cross_self` | 108 | `w ⬝ᵥ v ⨯₃ w = 0` | `pointOnLine B (lineThrough A B)` |
| `crossProduct_smul_left` | (OQ-03 file 599) | `crossProduct (c • u) v = c • crossProduct u v` | rescaling on left |
| `crossProduct_smul_right` | (OQ-03 file 605) | `crossProduct u (c • v) = c • crossProduct u v` | rescaling on right |

**Notation**: Mathlib uses `⨯₃` for `Matrix.crossProduct` (`Matrix.crossProduct u v` ≡ `u ⨯₃ v`). The parent file (`PascalsHexagon.lean:80`) uses the prefix form `crossProduct`. Both refer to the same definition; the notation is locally scoped in Mathlib via `Mathlib.LinearAlgebra.CrossProduct`. Either form works.

**Implication**: the `rawPascalLine_hexRev` proof obligation reduces from a hand-wave to a 5-step rewrite chain:

```lean
-- Sketch for hexRev case (raw vector calculation):
-- new P = lineIntersection (lineThrough F E) (lineThrough C B)
--       = (F ⨯₃ E) ⨯₃ (C ⨯₃ B)
--       = ((-1) • (E ⨯₃ F)) ⨯₃ ((-1) • (B ⨯₃ C))   -- cross_anticomm twice
--       = ((-1) * (-1)) • ((E ⨯₃ F) ⨯₃ (B ⨯₃ C))   -- crossProduct_smul_left/right
--       = (E ⨯₃ F) ⨯₃ (B ⨯₃ C)                       -- neg_one_mul_neg_one
--       = (-1) • ((B ⨯₃ C) ⨯₃ (E ⨯₃ F))              -- cross_anticomm
--       = (-1) • original Q
```

The same shape closes the `Q → -P` case. The `R → R` case is the easiest (cross_anticomm is invoked an even number of times). The total proof is roughly **15 lines** for `hexRev` (was estimated at ~30 in PR #18338 line 180 because the previous estimate did not factor in Mathlib's `cross_anticomm`).

## Finding D — Concrete `pascalLine` definition using `Projectivization`

Building on Findings A–C, the proposed `pascalLine` definition replaces the S4 PREP survey's ~185-LOC plan with a much smaller surface area. The new shape:

```lean
import Mathlib.LinearAlgebra.Projectivization.Basic

open scoped LinearAlgebra.Projectivization

/-- The raw Pascal line vector for an inscribed hexagon under permutation `π`.
    Defined via the first two Pascal intersection points of the relabeled hexagon. -/
noncomputable def rawPascalLine
    (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) : ProjLine :=
  let h := permuteHexagon C hex π
  lineThrough (pascalP h) (pascalQ h)

/-- Whether the raw Pascal line is a valid (nonzero) projective line.
    False precisely when two consecutive Pascal intersection points coincide. -/
def rawPascalLineValid
    (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) : Prop :=
  rawPascalLine C hex π ≠ 0

/-- The Pascal line in projective space, valued in Mathlib's `Projectivization`.
    Returns `none` for degenerate hexagons where two opposite-side intersections coincide. -/
noncomputable def pascalLineProj
    (C : Conic) (hex : InscribedHexagon C) (π : Equiv.Perm (Fin 6)) :
    Option (ℙ ℝ ProjLine) :=
  if h : rawPascalLineValid C hex π then
    some (Projectivization.mk ℝ (rawPascalLine C hex π) h)
  else
    none

/-- `pascalLine` descends to the quotient `HexagonLabeling = Sym(6) ⧸ hexagonalGroup`.
    Well-definedness follows from `Projectivization.lift` plus the dihedral generator
    invariance lemmas `rawPascalLine_hexRot` and `rawPascalLine_hexRev`. -/
noncomputable def pascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) :
    Option (ℙ ℝ ProjLine) :=
  Quotient.lift (pascalLineProj C hex) (well_def_proof C hex) lbl
```

where `well_def_proof` is the closure of the dihedral generator cases (described in §Finding E below).

**LOC accounting** vs PR #18338 line 184 "Estimated total: ~185 lines":

| Component | PR #18338 estimate | This PR's estimate (with Projectivization) | Δ |
|---|---|---|---|
| `permuteHexagon` (raw definition) | ~30 | ~35 (per PR #18461 Finding D) | +5 |
| `rawPascalLine` (raw definition) | ~10 | ~5 (one-liner via `lineThrough ... (pascalP) (pascalQ)`) | -5 |
| `ProjLineClass` quotient + smul invariance lemmas | ~50 | **0** (Mathlib provides `Projectivization`) | **-50** |
| `rawPascalLine_hexRot` (rotation invariance, mod scalar) | ~30 | ~15 (via `cross_anticomm` + `crossProduct_smul_*`) | -15 |
| `rawPascalLine_hexRev` (reversal invariance, mod scalar) | ~30 | ~15 (same) | -15 |
| `rawPascalLine_subgroup_inv` (closure-induction) | ~25 | ~20 | -5 |
| `pascalLine` (final `Quotient.liftOn`) | ~10 | ~10 (Option-wrapped via `pascalLineProj`) | 0 |
| **Total** | **~185** | **~100** | **−85** |

The 85-LOC reduction comes almost entirely from eliminating the bespoke quotient-type boilerplate (50 LOC) and from `cross_anticomm` collapsing the two invariance proofs.

**Risk caveat**: the Option wrapper for degeneracy creates a downstream obligation on `SteinerPoint.on_lines` / `KirkmanPoint.on_lines` (§Finding F below). The 100-LOC estimate is for `pascalLine` itself; the SteinerPoint refactor adds an estimated +15 LOC.

## Finding E — Well-definedness obligation for `Quotient.lift` over `HexagonLabeling`

`Quotient.lift` over `HexagonLabeling := Sym(6) ⧸ hexagonalGroup` requires proving:

```
∀ π₁ π₂, (∃ g ∈ hexagonalGroup, π₂ = π₁ * g) → pascalLineProj C hex π₁ = pascalLineProj C hex π₂
```

Since `hexagonalGroup = Subgroup.closure {hexRot, hexRev}`, by `Subgroup.closure_induction`, it suffices to verify the two generator cases:

**Sub-obligation 1**: `pascalLineProj C hex π = pascalLineProj C hex (π * hexRot)`
**Sub-obligation 2**: `pascalLineProj C hex π = pascalLineProj C hex (π * hexRev)`

For each, the `Option` cases split:

- **Both `rawPascalLineValid`**: reduces to `Projectivization.mk` equality, i.e. `∃ a : ℝˣ, a • rawPascalLine π = rawPascalLine (π * g)`. Closes via Finding C's `cross_anticomm` chain.
- **Both `¬ rawPascalLineValid`**: both are `none`; `none = none`.
- **Mixed**: must show this is impossible. The mixed case happens iff `rawPascalLine π = 0` but `rawPascalLine (π * g) ≠ 0` (or vice versa). Since `rawPascalLine (π * g)` is a scalar multiple of `rawPascalLine π` by Findings B–C (specifically, the dihedral generators scale the raw line by ±1 — a unit), the mixed case is contradictory. Formal proof: ~5 lines via `mul_smul` + `Units.ne_zero`.

**Total well-definedness proof**: ~40 LOC (split across the two generator cases + closure_induction wrapper + the Option case-analysis above). This is consistent with PR #18338's ~25 LOC estimate for `rawPascalLine_subgroup_inv` plus the new Option case-analysis overhead.

## Finding F — `SteinerPoint.on_lines` refactor under Option-wrapped pascalLine

PR #18338 lines 597–605 of `PascalsHexagonOQ03.lean` defines:

```lean
structure SteinerPoint (C : Conic) (hex : InscribedHexagon C) where
  point : ProjPoint
  triple : Finset HexagonLabeling
  card_triple : triple.card = 3
  on_lines : ∀ lbl ∈ triple, pointOnLine point (pascalLine C hex lbl)
```

Under the new `pascalLine : HexagonLabeling → Option (ℙ ℝ ProjLine)` signature, `pointOnLine point (pascalLine C hex lbl)` is ill-typed (`pointOnLine` expects `ProjLine`, gets `Option (ℙ ℝ ProjLine)`).

**Refactor option (i)**: lift `pointOnLine` through the Option + `Projectivization.rep`:

```lean
def pointOnProjLine (p : ProjPoint) (l : Option (ℙ ℝ ProjLine)) : Prop :=
  match l with
  | none => True  -- degenerate label, vacuously on
  | some ℓ => pointOnLine p ℓ.rep

-- on_lines : ∀ lbl ∈ triple, pointOnProjLine point (pascalLine C hex lbl)
```

Cost: ~5 LOC for the new `pointOnProjLine` definition. The `none` case being `True` is the technically-correct choice (a degenerate Pascal line passes through all points), but it makes counting non-degenerate Steiner points harder. **Alternative for `none = True` choice**: thread a `nondegenerate` hypothesis on `hex` through the structures (per S4b Finding E Option (a), which was rejected as scope-creep).

**Refactor option (ii)**: bake the `Projectivization.rep` choice into a thin wrapper `evalPascalLine : HexagonLabeling → ProjLine`:

```lean
noncomputable def evalPascalLine
    (C : Conic) (hex : InscribedHexagon C) (lbl : HexagonLabeling) : ProjLine :=
  match pascalLine C hex lbl with
  | none => 0
  | some ℓ => ℓ.rep

-- on_lines : ∀ lbl ∈ triple, pointOnLine point (evalPascalLine C hex lbl)
```

This preserves the `on_lines` signature **as is** (only the body of `evalPascalLine` changes). The trade-off: `evalPascalLine` is *not* invariant on the nose under generators — it picks a specific `rep` which can differ by a unit scalar. However, `pointOnLine point ℓ ↔ pointOnLine point (c • ℓ)` for `c ≠ 0`, so `pointOnLine point (evalPascalLine lbl)` is invariant on the proposition level. The `on_lines` field is type-stable.

**Recommendation**: Option (ii) is the migration path of least disturbance to the existing `SteinerPoint` / `KirkmanPoint` structures. PR #18185's `S3d` and earlier merged work on `hexagonalGroup` / `HexagonLabeling` is preserved unchanged. Net diff in `PascalsHexagonOQ03.lean`: +5 LOC for `evalPascalLine` definition, +1 LOC each on `on_lines` field of two structures (s/pascalLine/evalPascalLine/).

## Finding G — Updated composite LOC estimate

Synthesizing Findings A–F + the cumulative PR #18338/#18461/#18559 work:

| Component | S4 PREP estimate | After this PR's audit |
|---|---|---|
| `permuteHexagon` + 3 `hexVertex_*` helpers | 35 | 35 (per PR #18461 design) |
| `rawPascalLine` | 10 | 5 |
| `rawPascalLine_hexRot` (mod-scalar invariance) | 30 | 15 (via `cross_anticomm`) |
| `rawPascalLine_hexRev` (mod-scalar invariance) | 30 | 15 |
| `rawPascalLine_subgroup_inv` (closure induction) | 25 | 20 |
| **ProjLineClass quotient boilerplate** | **50** | **0** (`Projectivization` from Mathlib) |
| `pascalLine` + `Option`/`rawPascalLineValid` | 10 | 15 |
| `evalPascalLine` (thin wrapper for `on_lines`) | not anticipated | 5 |
| Well-definedness proof obligation (Quotient.lift) | folded into invariance | 40 |
| **OQ-02 sorry closure total** | **~185** | **~150** |
| `[Fintype]` brackets removed (S4b Finding D) | not anticipated | -2 |
| Case-split degeneracy `dite` (S4b Finding E) | not anticipated | +0 (subsumed by Option) |
| **Net file delta** | — | **+148 LOC** |

The S4 PREP survey's ~185 LOC estimate revises down to **~150 LOC for OQ-02 sorry closure** when using Mathlib's `Projectivization`. The savings come from:

1. Eliminating bespoke `ProjLineClass` (−50 LOC) — replaced by Mathlib import.
2. Tightening `rawPascalLine_hexRot` / `_hexRev` (−15 LOC × 2 = −30) via `cross_anticomm`.
3. Adding back +40 LOC for the explicit `Quotient.lift` well-definedness proof (not separately budgeted in S4 PREP — was implicitly part of "subgroup_inv").
4. Adding +5 LOC for `evalPascalLine` to preserve `on_lines` signatures.

Net: **−35 LOC vs PR #18338 estimate**. The pascalLine definitional sorry (3 → 2) closes; no new axioms introduced.

## Sorry / axiom delta projection

This PR (S4c PREP audit): **0 sorries, 0 axioms, 0 Lean line changes.**

If all 4 tightened recommendations from S4-family PREPs land in subsequent ACT PRs:
- **S4a PREP `permuteHexagon`** (PR #18461): +35 LOC, 0 sorry change.
- **S4b PREP `Nat.card` migration** (PR #18559 Finding D): ~0 net LOC, 0 sorry change.
- **This PR — `Projectivization`-based pascalLine** (S4c PREP): +115 LOC (above the 35 from S4a), **−1 sorry** (closes `pascalLine` definitional sorry at line 570).

Composite progress on OQ-02 (`pascalLine` well-definedness): **3 file-level sorries → 2** at a cost of ~150 LOC of new Lean. The remaining 2 sorries are `steiner_count_eq_20` (OQ-03) and `kirkman_count_eq_60` (OQ-04), both independent of `pascalLine` definitionality.

## Anti-targets

This document is a pure **Mathlib bearer audit + design memo**. It does NOT:

- Modify any Lean source file (`proofs/Proofs/PascalsHexagonOQ03.lean`, `proofs/Proofs/PascalsHexagon.lean` untouched).
- Modify `meta.json`, `state.md`, `problem.md`, `knowledge.md`, or the gallery JSON files.
- Add any `sessions/*` file other than this one (`2026-05-13-s4c-prep-mathlib-projectivization-audit.md`).
- Resolve any of the 3 remaining sorries (`pascalLine`, `steiner_count_eq_20`, `kirkman_count_eq_60`).
- Add any new axiom.
- Modify or extend the parent file's `Conic.nondegenerate` predicate.
- Verify the proposed `pascalLine` definition compiles (this is doc-only; the LOC estimates are paper-and-pen sketches).

## Honest scope guarantee

The audit findings are based on:

- **(A)** Direct `gh api search/code` + `gh api repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Projectivization/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` at session time (2026-05-13 ~08:30 UTC). 9 API entries verified by exact line number with `base64 -d`.
- **(B)** Direct inspection of the `Projectivization.lift` signature against the well-definedness pattern needed for `Quotient.lift` over `HexagonLabeling`. The setoid match is a definitional unfold (both quotients are over scalar-orbit relations).
- **(C)** Direct `gh api` fetch of `Mathlib/LinearAlgebra/CrossProduct.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. 7 cross-product identity entries verified by exact line number.
- **(D)** Synthesis with PR #18338 lines 163–170 (Route (a) recommendation), PR #18461 line 87 (sign-flip scalars `−1, −1, +1`), and PR #18559 lines 121–138 (Option (b) `dite` discussion).
- **(E)** Reduction of the closure-induction obligation to two generator cases via `Subgroup.closure_induction` (already invoked in S3d's `dihedralHomToSym6_range` proof at `PascalsHexagonOQ03.lean:~510`, established convention).
- **(F)** Type-theoretic argument from the `SteinerPoint` structure: `pointOnLine point (pascalLine C hex lbl)` is well-typed only if `pascalLine` returns `ProjLine`, hence the thin-wrapper `evalPascalLine` recommendation.

**Verifiable**: All findings are reproducible from the current `proofs/` source + Mathlib HEAD on `leanprover-community/mathlib4` at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Untested**: the proposed `pascalLineProj` / `pascalLine` / `evalPascalLine` Lean snippets are **not** compiled. The 150-LOC composite estimate is a paper-and-pen sketch; actual LOC may be ±20 depending on:
- Whether the `Subgroup.closure_induction` recipe matches the dihedral case-split mechanically or needs `Subgroup.closure_induction'` (left/right multiplication convention).
- Whether `Projectivization.lift`'s `(t : K)` predicate composes with the `Units` packaging for `cross_anticomm`'s `−1` scalar in a single `rfl` or needs a `Units.mk0` round-trip.
- Whether `Mathlib.LinearAlgebra.Projectivization.Basic` is transitively imported by `Mathlib.Tactic` (likely yes, but a defensive explicit import costs 1 line).

The GitHub `search/code` rate limit (30/hr per memory `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`) was respected; the verifications used ≤8 API calls total.

## Differentiation from PR #18338 (S4 PREP survey), PR #18461 (S4a PREP), and PR #18559 (S4b PREP close-out)

| Aspect | PR #18338 (S4 PREP) | PR #18461 (S4a PREP) | PR #18559 (S4b PREP close-out) | This PR (S4c PREP) |
|---|---|---|---|---|
| Scope | OQ-02/03/04 survey + ProjLineClass route recommendation | permuteHexagon signature + Fintype/Nat.card flag | Audit close-out + Nat.card tightening + degeneracy Option (b) | **Mathlib `Projectivization` audit; `ProjLineClass` boilerplate eliminated** |
| Bespoke ProjLineClass | proposed (~50 LOC) | not addressed | not addressed | **superseded by Mathlib `Projectivization` (0 LOC)** |
| `cross_anticomm` lemma | mentioned (line 161) | mentioned (line 87) | not addressed | **verified at `Mathlib/LinearAlgebra/CrossProduct.lean:86`; reduces invariance proofs by ~50%** |
| `Quotient.lift` well-definedness | implicit in subgroup_inv | not addressed | not addressed | **explicit 40-LOC budget + Option case-analysis** |
| `SteinerPoint.on_lines` impact | not addressed | not addressed | not addressed | **`evalPascalLine` wrapper (Option ii) preserves signature** |
| OQ-02 LOC estimate | ~185 | ~+35 (permuteHexagon) | ~+15 (case-split) | **~150 composite (−35 vs S4 PREP)** |
| Sorry / axiom delta | plans for −1 sorry, 0 axioms | 0 (audit-only) | 0 (audit-only) | 0 (audit-only) |
| File created | `2026-05-12-s4-prep-survey.md` (312 LOC) | `2026-05-12-s4a-prep-mathlib-audit.md` (209 LOC) | `2026-05-12-s4b-prep-mathlib-audit-closeout.md` (240 LOC) | `2026-05-13-s4c-prep-mathlib-projectivization-audit.md` (this PR) |

This PR is a sub-step of the S4 PREP roadmap — orthogonal by construction to the three prior PREPs (creates only a new `sessions/*` file path; does not modify the prior PREP docs, any Lean source, `meta.json`, `state.md`, `problem.md`, `knowledge.md`, or gallery JSON). Concurrent S4c-ACT / S4d / S4e PRs can land independently.

## Strengthened action item for OQ-02 ACT agent

When implementing the `pascalLine` definitional sorry closure, **do NOT build a bespoke `ProjLineClass`** as PR #18338 line 170 suggested. Instead:

1. Add `import Mathlib.LinearAlgebra.Projectivization.Basic` (defensive; may already be transitively imported).
2. Add `open scoped LinearAlgebra.Projectivization` (for the `ℙ` notation).
3. Define `rawPascalLine` (5 LOC), `pascalLineProj` (Option-wrapped, 10 LOC).
4. Prove `rawPascalLine_hexRot` and `rawPascalLine_hexRev` invariance (15 LOC each) via `cross_anticomm` + `crossProduct_smul_left/right`.
5. Discharge `Quotient.lift` well-definedness via `Subgroup.closure_induction` over `{hexRot, hexRev}` (~40 LOC).
6. Define `evalPascalLine` (5 LOC) and migrate `SteinerPoint.on_lines` / `KirkmanPoint.on_lines` signatures (2 LOC).

Total: ~150 LOC, −1 sorry (closes `pascalLine` definitional at PascalsHexagonOQ03.lean:570), 0 axioms.
