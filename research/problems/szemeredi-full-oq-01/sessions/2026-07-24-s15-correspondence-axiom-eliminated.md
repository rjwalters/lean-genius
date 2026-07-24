# S15 ACT — Furstenberg Correspondence Principle PROVED; parent axiom eliminated

**Author:** researcher-1
**Date:** 2026-07-24 ~11:45 UTC
**Phase:** ACT (the assembly step queued by S14)
**Predecessors:** S13 (limit_invariant_on_cylinder proved), S14 (Prokhorov
axiom eliminated; OQ01 file 0 ax / 0 sorry).

## Headline

`Furstenberg.furstenberg_correspondence` — **Axiom 1 of
`Proofs/FurstenbergCorrespondence.lean` — is now a THEOREM** with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`. Consequently:

- `szemeredi_k2_ergodic` (positive-Banach-density sets contain 2-APs, via
  the ergodic route) is now **fully machine-verified, zero custom axioms**.
- `szemeredi_ergodic` (all k) now depends on exactly ONE axiom
  (`multiple_recurrence_ge3`), down from two.
- Parent file axioms: **2 → 1**.

## What shipped

### `FurstenbergCorrespondenceOQ01.lean` (967 → 1203 LOC, +236; Part XV)

1. `limit_invariant_on_clopen_moving` — Part XII's fixed-base-point limit
   invariance generalized to **moving base points** `xs : ℕ → CantorSpace`
   (required because upper *Banach* density windows `[aₖ, aₖ+Nₖ)` move, so
   the Cesàro measures sit at varying orbit points `shift^[aₖ](1_A)`). The
   telescoping bounds are uniform in the base point; proof is verbatim
   Part XII.
2. `isClopen_of_mem_measurableCylinders` — every measurable cylinder over
   `ℕ → Bool` is clopen: preimage of an (automatically clopen) subset of
   the finite discrete space `(i : I) → Bool` under the continuous
   restriction. (`Pi.discreteTopology` + `isClopen_discrete`.)
3. `limit_measurePreserving` — **the key upgrade**: clopen invariance →
   full `MeasurePreserving shift μ μ` via
   `ext_of_generate_finite (measurableCylinders _)
   generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders`
   (the exact invocation pattern of Mathlib's
   `IsProjectiveLimit.unique`). Univ clause via `Measure.map_apply` + both
   sides probability.
4. `limit_positive_implies_ap` — k-fold return at the limit: the k-fold
   set is clopen, Portmanteau (`tendsto_measure_of_null_frontier_of_tendsto'`)
   + `Filter.Tendsto.eventually_ne` transfer positive limit measure to some
   Cesàro measure, then Part XIII's `positive_measure_gives_ap` extracts
   the AP.
5. `kfold_two_eq_pair` — `⋂ (i : Fin 2), shift^[i·n]⁻¹(B₀) = B₀ ∩ shift^[n]⁻¹(B₀)`.
6. `exists_invariant_measure_correspondence` — the full package: for
   `d*(A) ≥ δ > 0` there is a shift-invariant probability measure on
   Cantor space with `μ(B₀) ≥ δ` and the k-fold return property. Assembly:
   `choose` on `density_lower_bound` + Prokhorov subsequence
   (`seqCompact_probabilityMeasure_cantor`) + items 3, 4.

### `FurstenbergCorrespondence.lean` (253 → 284 LOC; axiom 2 → 1)

- `axiom furstenberg_correspondence` → `theorem`, proved from the OQ01
  package: System := ⟨CantorSpace, inferInstance, μ, shift, B₀, μ.2, hMP,
  cylinderZero_measurableSet⟩; pair-return derived from the k-fold clause
  at k = 2 via `kfold_two_eq_pair`; k-fold clause verbatim.
- Added `import Proofs.FurstenbergCorrespondenceOQ01` (no cycle: OQ01
  imports only Mathlib).
- Header/docstrings/summary table updated 2-axiom → 1-axiom prose.

## Verification

- Host `lake env lean`: both files exit 0 (only pre-existing deprecation
  warnings in OQ01's old parts).
- `#print axioms`:
  - `furstenberg_correspondence` → foundational only.
  - `szemeredi_k2_ergodic` → foundational only.
  - `szemeredi_ergodic` → foundational + `multiple_recurrence_ge3`.
  - `exists_invariant_measure_correspondence`, `limit_measurePreserving`
    → foundational only.
- Docker: `Built Proofs.FurstenbergCorrespondenceOQ01` +
  `Built Proofs.FurstenbergCorrespondence` (8577 jobs), exit 0.

## Gallery updates

- `furstenberg-correspondence/meta.json`: meta.axiomCount 2 → 1,
  leanFile.axiomCount 2 → 1, theoremCount 4 → 5, lineCount 253 → 284,
  assumptions rewritten (single multiple-recurrence axiom), overview /
  sections 3–6 / conclusion prose de-axiomatized for the correspondence.
  Status stays `axiomatized` (1 axiom remains) — honest.
- `furstenberg-correspondence-oq-01/meta.json`: lineCount 945 → 1203,
  theoremCount 32 → 37. Still verified/original/0.

## Lean gotchas (v4.31)

- `omega` cannot see through tactic-`let` bindings (`let Ns := fun m => N m - 1`
  makes `Ns m` an opaque atom): `show m ≤ N m - 1` (defeq unfold) first.
- `simp [(cylinder_isClopen 0 true).frontier_eq]` fails against a goal
  stated at `cylinderZero` (regular def ≠ reducible): restate the IsClopen
  fact AT `cylinderZero` via defeq (`have h : IsClopen cylinderZero :=
  cylinder_isClopen 0 true`) and simp with that.
- Structure-literal goals (`(System.mk ...).B ∩ ...`): convert hypotheses
  through defeq with an explicit `have hpos' : <reduced form> := hpos`
  before `rw` (rw needs syntactic match).

## Next steps

- **S16+ (the remaining axiom)**: `multiple_recurrence_ge3` — genuine deep
  ergodic theory (ergodic decomposition + characteristic factors /
  Furstenberg–Katznelson structure theory, ~2000+ lines, missing from
  Mathlib). This is research-grade; do NOT expect session-sized progress.
  Check Mathlib growth for ergodic decomposition before each attempt
  (the S14 meta-lesson: upstream growth retires local axioms wholesale).
- OQ01 file itself is COMPLETE for its stated purpose — the correspondence
  is proved end-to-end. Enricher may want to refresh
  furstenberg-correspondence annotations (prose still describes the
  axiomatized architecture in places).
