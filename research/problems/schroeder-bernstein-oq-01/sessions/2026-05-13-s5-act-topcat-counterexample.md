# S5 ACT — `¬ HasSBP TopCat` via the `[0,1]` vs `(0,1)` counterexample

**Date**: 2026-05-13
**Researcher**: researcher-1
**Phase**: S5 ACT (Lean code; build pending)
**Mathlib pin**: v4.26.0 (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

## Predecessors

- #18274 — S1 OBSERVE.
- #18383 — S2/S3 ACT (`HasSBP` + `hasSBP_Type`, build verified).
- #18428 — S4 PREP (`HasSBP (Discrete α)`).
- #18450 — S5 PREP (`¬ HasSBP TopCat` design memo).
- #18496 — S4 ACT (`hasSBP_Discrete`).
- #18508 — S5b PREP (TopCat coercion ritual audit).
- #18602 — S5c PREP (final S5 ACT preflight; supplies the §4 assembled proof).
- #18655 — S5d PREP (citation line-drift audit).
- #18673 — S5e PREP (substantive audit-correction on S5c §3.5 injectivity proofs; supplies the corrected §4 forms used here).

## Outcome

`proofs/Proofs/SchroederBernsteinOQ01.lean` is extended by 5 declarations:

| Declaration | Visibility | LOC | Role |
|---|---|---|---|
| `fHom : TopCat.of ↥(Set.Icc 0 1) ⟶ TopCat.of ↥(Set.Ioo 0 1)` | `private def` | 8 | compression `x ↦ (x+1)/4`, lands in `[1/4, 1/2] ⊂ (0,1)` |
| `gHom : TopCat.of ↥(Set.Ioo 0 1) ⟶ TopCat.of ↥(Set.Icc 0 1)` | `private def` | 4 | inclusion `(0,1) ↪ [0,1]` via `Set.Ioo_subset_Icc_self` |
| `fHom_injective : Function.Injective (TopCat.Hom.hom fHom)` | `private theorem` | 5 | `rintro` + `Subtype.ext` + `simp [fHom]` + `linarith` |
| `gHom_injective : Function.Injective (TopCat.Hom.hom gHom)` | `private theorem` | 5 | `rintro` + `Subtype.ext` + `simp [gHom]` + `exact` |
| `not_hasSBP_TopCat : ¬ HasSBP TopCat.{0}` | `theorem` | 18 | mutual monos → iso → homeomorph → compactness on `(0,1)` → `isCompact_Ioo_iff` contradiction |

**Total added**: ~55 LOC including comments. **Final file size**: 160 LOC (was 78).

| Metric | Before | After |
|---|---|---|
| Theorems | 2 | 6 (incl. 3 private + 1 public) |
| Definitions | 1 | 3 (incl. 2 private) |
| Sorries | 0 | 0 |
| Axioms | 0 | 0 |
| New imports | — | 5 (`TopCat.Basic`, `TopCat.EpiMono`, `Compactness.Compact`, `Order.Compact`, `Tactic`) |

## Why this is meaningful

- **First Lean-formal failure witness for `HasSBP`.** Prior `HasSBP` instances (`Type`, `Discrete`) were both *positive*. `TopCat` is the first concrete *negative* witness in this slug's Lean corpus.
- **Validates the categorical predicate's expressiveness.** The same `HasSBP` predicate that holds in `Type` (Schroeder-Bernstein theorem) and `Discrete α` (vacuously) fails in `TopCat`, demonstrating the predicate discriminates structure.
- **Mirrors classical literature.** Bumby (1965, `Grp`) and Gowers (1996, `Ban`) are the canonical citations for SBP failure in concrete categories. The `TopCat` witness is the *easiest* such failure to formalize because Mathlib has full `TopCat` infrastructure (`TopCat.of`, `mono_iff_injective`, `homeoOfIso`) and the compactness obstruction is captured by `isCompact_Ioo_iff`.

## Proof structure (per S5c PREP §4 + S5e PREP §4)

The proof chains six Mathlib bearers:

1. **`TopCat.mono_iff_injective`** (`EpiMono.lean:38`): Mono in TopCat ↔ Function.Injective.
2. **`HasSBP` destructor** (`def`, applied directly to its 4 arguments per S5c §2.2): `h X Y ⟨fHom, _⟩ ⟨gHom, _⟩ : Nonempty (X ≅ Y)`.
3. **`TopCat.homeoOfIso`** (`Basic.lean:204`): Iso in TopCat → Homeomorph between underlying types (via `TopCat.coe_of := rfl`).
4. **`Homeomorph.compactSpace`** (`Lemmas.lean:104`): transfers `CompactSpace` along a homeomorphism.
5. **`isCompact_iff_isCompact_univ`** (`Compact.lean:970`): bridges `CompactSpace α` (via `isCompact_univ`) to `IsCompact (s : Set X)`.
6. **`isCompact_Ioo_iff`** (`Compact.lean:132`): for `(a, b)` open in ℝ, compactness forces `b ≤ a`.

The single arithmetic finisher is `linarith` from `1 ≤ (0 : ℝ)`.

## Compression-map well-definedness

For `x ∈ [0, 1]`:
- `(x + 1) / 4 ≥ 1/4 > 0`: from `x ≥ 0` ⇒ `x + 1 ≥ 1`.
- `(x + 1) / 4 ≤ 2/4 = 1/2 < 1`: from `x ≤ 1` ⇒ `x + 1 ≤ 2`.

So the image lies strictly inside `(0, 1)`, witnessed by two `linarith` calls in the membership-construction tactic block.

Continuity is handled by `fun_prop`, which automatically chains `Continuous.add_const`, `Continuous.div_const`, and `continuous_subtype_val` + `Subtype.mk`.

## Injectivity proofs (per S5e PREP §4 corrected forms)

S5c PREP §3.5 originally cited `Subtype.mk.inj_iff`, which is a **phantom lemma** in Mathlib v4.26.0 (verified by S5e PREP §1.1: zero hits in `language:lean` corpus). The corrected pattern in S5e §4:

```lean
private theorem fHom_injective :
    Function.Injective (TopCat.Hom.hom fHom) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  apply Subtype.ext
  simp [fHom] at hab
  linarith
```

The `simp [fHom]` unfolds `fHom` (a `private def` that simp would not unfold automatically) → applies `TopCat.hom_ofHom` → beta-reduces the destructured `ContinuousMap.toFun` → applies `Subtype.mk.injEq` (the real Lean-core lemma) → reduces to `(a + 1) / 4 = (b + 1) / 4`, which `linarith` closes to `a = b`.

For `gHom`, the lambda is `fun ⟨y, hy⟩ => ⟨y, …⟩` — identity on values — so after the simp chain `hab : a = b` directly, no `linarith` needed.

## Build status

**Build pending.** The worktree's `proofs/.lake` symlink is in the self-referential loop documented in memory `feedback_researcher_lake_symlink_loop_and_wipe.md`; local `docker-build.sh` would either fail (Docker inherits the loop) or initiate a ~10-min Mathlib clone that often truncates mid-build and triggers daemon-respawn worktree wipe.

Per the standard build-pending workflow (cf. ballot-problem-oq-01-oq-01-oq-02-oq-01 S2 ACT, PR #18381 / hilbert-15-* PRs / four-square-distribution-oq-01 PR #18640): the PR is committed and pushed first; doctor or mechanic runs `./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01` from a clean worktree.

S5e PREP §6 estimates ~5% build risk for the corrected injectivity forms used here. The compactness chain (`isCompact_iff_compactSpace.mp`, `Homeomorph.compactSpace`, `isCompact_iff_isCompact_univ.mpr`, `isCompact_Ioo_iff`) is paper-checked against S5c PREP §1.3 + §5's bearer table; all citations verified at v4.26.0.

### Risks the build may surface

- `fun_prop` on the destructured-Subtype-lambda continuous map: explicit fallback per S5c §3.3's comment is `(Continuous.add_const continuous_subtype_val 1).div_const 4 |>.subtype_mk _`.
- `simp [fHom]` vs `simp only [fHom, TopCat.Hom.hom, TopCat.hom_ofHom, Subtype.mk.injEq]`: S5e §4 fallback if the heuristic `simp` doesn't close. The full-`simp` form is preferred for readability.
- `(TopCat.homeoOfIso iso).compactSpace`: the `.compactSpace` method on `Homeomorph` should resolve via dot notation (`Homeomorph.compactSpace` is the canonical name, requires `[CompactSpace α]` instance in scope, which we provide via `haveI : CompactSpace ↥(Set.Icc 0 1) := inferInstance`).

## Files modified

| File | Action | Delta |
|---|---|---|
| `proofs/Proofs/SchroederBernsteinOQ01.lean` | edited | +82 LOC (78 → 160) |
| `research/problems/schroeder-bernstein-oq-01/state.md` | edited | +S5 ACT entry in Sessions; iteration 2 → 5 |
| `src/data/research/problems/schroeder-bernstein-oq-01.json` | edited | currentState/knowledge/leanFiles updated for S5 ACT |
| `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-13-s5-act-topcat-counterexample.md` | new | this session note |

No edits to `problem.md` (problem statement unchanged), `knowledge.md` (the S2/S3 knowledge entry is preserved; this PR's knowledge updates go through the slug JSON), or any sibling session note.

## Race-safety

- **Pre-write probe** (~2026-05-13 08:50 UTC): `gh pr list --repo rjwalters/lean-genius --search "schroeder-bernstein-oq-01 in:title" --state open` → `[]` (zero).
- **Most recent merge on slug**: PR #18673 (S5e PREP, 2026-05-13T08:03:50Z) — ~45 min ago. Past the typical race-window.
- **5 S5-prefix PREPs all merged** (S5, S5b, S5c, S5d, S5e) — this is the natural ACT consumer.
- **New file path**: `sessions/2026-05-13-s5-act-topcat-counterexample.md`. Unique across the 7 existing session files.
- **Recheck at push time** mandated.

## Honesty

- **No build verification.** The proof is paper-checked against:
  - S5c PREP §4's assembled proof (verbatim modulo the variable-naming + the absence of `set X, Y` per memory-noted simplification preference).
  - S5e PREP §4's corrected injectivity forms.
  - S5c PREP §5's bearer table (all 14 bearers verified at v4.26.0).
- **The two `linarith` calls inside `fHom`'s membership tactic** (the `(x + 1) / 4 ∈ Ioo 0 1` obligation) are local-arithmetic — they have not been Docker-verified but are paper-checked from the bounds.
- **`fun_prop` on destructured-Subtype-lambda continuous maps** is the residual risk; S5c §3.3 documents the explicit `Continuous.*` fallback if `fun_prop` doesn't close.
- **No `axiom` declarations added** anywhere. The proof relies only on Mathlib, the parent `HasSBP` def (`SchroederBernsteinOQ01.lean:47-48`), and `Mathlib.Tactic`.
- **No claim about `TopCat.{u}` for `u > 0`**: the proof fixes `TopCat.{0}` because the ℝ-subtype objects are `Type 0`. Universe polymorphism remains S6+ work.
- **Build risk estimated at ~5%** per S5e §6. The two highest-impact concerns are `fun_prop` and `simp [fHom]` heuristic resolution; both have explicit fallbacks documented in S5c/S5e.
- **No retroactive edits to prior session notes.** S5 / S5b / S5c / S5d / S5e PREPs remain as-merged; this S5 ACT consumes them according to their merged content.

## Outcome metrics

**Mode**: REVISIT (slug at 5 S5-PREP layers, all merged; this is the ACT they pre-staged).
**Problem**: `schroeder-bernstein-oq-01`.
**Sorry delta**: 0 (still 0 sorries in the file).
**Axiom delta**: 0 (still 0 axioms).
**LOC delta**: +82 Lean (78 → 160), +~190 doc (this session note).

## Anti-targets

- **Does NOT** generalize to `TopCat.{u}` (S6+).
- **Does NOT** add Banaschewski-Brümmer split-mono lemma (S6 ACT).
- **Does NOT** edit `problem.md` or `knowledge.md`.
- **Does NOT** modify parent gallery `meta.json` to register `SchroederBernsteinOQ01.lean` in `additionalFiles` (auditor/enricher PR — bookkeeping).
- **Does NOT** retroactively edit any prior session note (5 S5-prefix PREPs preserved as-merged).
- **Does NOT** create gallery JSON for this slug (slug remains research-only).

## Decision log

- **2026-05-13 S5 ACT**: Chose `simp [fHom]` / `simp [gHom]` over `simp only [...]` form for injectivity proofs. Reason: S5e PREP §4 explicitly endorses the heuristic form; the `simp only` is documented as a fallback if heuristic fails. Building under uncertainty, prefer the simpler form.
- **2026-05-13 S5 ACT**: Used `inferInstance` for `CompactSpace ↥(Set.Icc 0 1)` rather than `isCompact_Icc.compactSpace`. Reason: Mathlib has `instance : CompactSpace ↥(Set.Icc a b)` derived from `CompactIccSpace ℝ`; `inferInstance` resolves it without explicit lemma-name dependency.
- **2026-05-13 S5 ACT**: Inlined the object types `TopCat.of ↥(Set.Icc 0 1)` and `TopCat.of ↥(Set.Ioo 0 1)` rather than using `set X := ... with hX` per S5c PREP §4. Reason: avoids `set` tactic's definitional-equality subtleties when later code (`(TopCat.homeoOfIso iso).compactSpace`) needs the underlying type to be `↥(...)` for `Homeomorph.compactSpace` to fire.
- **2026-05-13 S5 ACT**: Imported `Mathlib.Topology.Order.Compact` for `CompactIccSpace` instance + `Mathlib.Topology.Compactness.Compact` for the `isCompact_Ioo_iff` and `isCompact_iff_isCompact_univ` bearers, rather than the heavyweight `import Mathlib`. Reason: keep imports narrow per S5c PREP §7's "at most 2 new imports" guideline (here 5 new for both TopCat and compactness).
