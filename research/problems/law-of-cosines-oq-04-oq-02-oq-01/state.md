# State: `law-of-cosines-oq-04-oq-02-oq-01`

**Tier**: B (Significance 6 / Tractability 5)
**Phase**: OBSERVE (S1) → PREP (S2-prep)
**Last update**: 2026-05-13 (researcher-4) — S2-PREP Mathlib bearer audit at pinned SHA

## Session N=2 — S2-PREP (2026-05-13, researcher-4)

**Mode**: PREP (doc-only; companion to S1 OBSERVE's `knowledge.md`).

**Outcome**: produced `s2-prep-bearer-audit.md` — re-grounds the S1 OBSERVE
`knowledge.md §4` Mathlib API survey against the lake-pinned Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`). Findings:

(a) **Wrong file path detected.** `InnerProductGeometry.angle` (def) and
    `InnerProductGeometry.cos_angle` cited in `knowledge.md §4.2` as living in
    `Mathlib/Analysis/InnerProductSpace/Basic.lean` actually live in
    **`Mathlib/Geometry/Euclidean/Angle/Unoriented/Basic.lean`** (at L40 and L65).
    A naive `gh api .../contents/<wrong-path>` lookup would have failed silently.

(b) **Substantial line drift** in `Convex/Between.lean`. The cluster
    `Sbtw.mem_image_Ioo`, `Sbtw.ne_left/left_ne/ne_right/right_ne` cited at L203-215
    actually sits at L341-353 (+138-line drift). Names + signatures stable; only
    line numbers moved. The S2 implementer would have been mis-guided by
    `knowledge.md`'s line citations alone.

(c) **Smaller drift** in `Geometry/Euclidean/Angle/Unoriented/Affine.lean`:
    `angle_eq_pi_iff_sbtw` L278→L281, `angle_add_angle_eq_pi_of_angle_eq_pi` L172→L175,
    `collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi` L376→L378. Names/sigs
    stable.

(d) **Path A Step 1 sketch added** (§4 of new doc): 15-25 LOC of cosine-equality
    conversion using `unfold EuclideanGeometry.angle` → `rw [InnerProductGeometry.cos_angle]`
    → `Real.arccos_inj` (Inverse.lean L336, preferred over `arccos_injOn` at L333 since
    the two-sided iff form is cleaner given explicit `[-1, 1]` bounds).

(e) **Refined risk register** (§3 of new doc): six rows of `knowledge.md §5`
    re-graded against audit evidence. Of those, two are **confirmed** (the
    `Sbtw.mem_image_Ioo` signature surprise + the `arccos`-injectivity bound
    derivability), one is **promoted in priority** (the `inner_smul_left` returning
    `r† * ⟪x, y⟫` for general `𝕜` may surface `starRingEnd ℝ` artefacts; check during S2),
    and one is **mostly nullified** (Mathlib version drift — names stable, only line
    numbers move, audit fixes that).

**Why PREP-only this session**: S2-implement is ~250-350 LOC of new Lean (per
`knowledge.md §8`) in a file (`LawOfCosinesOQ04OQ02OQ01.lean`) that doesn't yet exist.
Per `CLAUDE.md`'s "never run `lake build` directly" policy, transcribing 250+ LOC
without local verification carries non-trivial build risk. Bearer audit + cosine-equality
sketch (15-25 LOC) de-risks the largest Mathlib-interface uncertainty BEFORE S2-implement
starts. The remaining inner-product factorization (Steps 2-4 of `knowledge.md §3.A`)
will benefit from the corrected file paths and line numbers.

**Net diff this session**: +1 markdown file (`s2-prep-bearer-audit.md`, ~210 lines),
state.md update, JSON cursor update. Zero Lean changes. Parent file
`LawOfCosinesOQ04OQ02.lean` unchanged (still 174 LOC, 9 theorems, 0 axioms, 0 sorries).

---

## Summary (S1 OBSERVE, 2026-05-11, researcher-8)

S1 OBSERVE for `law-of-cosines-oq-04-oq-02-oq-01` is complete. The OQ — deriving the
algebraic angle-bisector identity `m · b = n · c` from a geometric premise — has been
reformulated as a clean inner-product factorization in Mathlib's `EuclideanGeometry`
framework, no missing primitives identified, and the S2 implementation has been
scoped at ~250-350 lines.

Doc-only iteration. Three files created in this worktree:

* `research/problems/law-of-cosines-oq-04-oq-02-oq-01/problem.md` — formal statement,
  classification, approach menu, related-proofs table.
* `research/problems/law-of-cosines-oq-04-oq-02-oq-01/knowledge.md` — full survey:
  §1 target, §2 vector reformulation, §3 three approach paths with hand
  derivation for the recommended Path A, §4 Mathlib API survey (5 sub-sections),
  §5 risk register, §6 sibling-proof lessons, §7 S1 outcome, §8 next-action menu.
* `src/data/research/problems/law-of-cosines-oq-04-oq-02-oq-01.json` — phase
  updated from `NEW` to `OBSERVE`, problem-statement / knownResults / knowledge
  fields populated, next-action set to S2 Path A.

No Lean changes in S1. Parent file `LawOfCosinesOQ04OQ02.lean` build status
unchanged (0 axioms, 0 sorries, 7 theorems).

## Path Decision

**S2 will implement Path A** (inner-product factorization). See
`knowledge.md §3.A` for the hand derivation and `knowledge.md §8` for the
seven-lemma S2 outline.

The key insight is that `Sbtw ℝ B D C` extracts a barycentric parameter
`s ∈ Ioo 0 1` with `D -ᵥ A = (1 - s) • u + s • v` (where `u := B -ᵥ A`,
`v := C -ᵥ A`), and the bisector hypothesis `∠ B A D = ∠ D A C` collapses (after
arccos injectivity + cancellation of the common `1 / ‖D -ᵥ A‖`) to the
algebraic equation

```
((1 - s) · c - s · b) · (b · c - ⟪u, v⟫) = 0
```

The second factor is excluded by `¬ Collinear ℝ ({A, B, C} : Set P)` (strict
Cauchy-Schwarz), forcing `s = c / (b + c)`. From `m = s · a` and `n = (1 - s) · a`
the identity `m · b = n · c` follows immediately.

## Session N=1 — S1 (2026-05-11, researcher-8)

* **Goal**: locate the `hbis : m * b = n * c` hypothesis in the parent file, survey
  Mathlib's metric-geometry API, decide on a derivation path for S2.
* **Result**: above. Path A selected. Risk register surfaced one medium-likelihood
  obstruction (Mathlib `ring`-failure in the factorization step) with a
  `linear_combination` mitigation already identified.
* **Files touched**: 3 markdown + 1 JSON (this iteration); no Lean file modifications.
* **Build status**: unchanged.

## Next action (Session N=2)

Implement S2 Path A in a new file `proofs/Proofs/LawOfCosinesOQ04OQ02OQ01.lean`.
Order of lemmas as listed in `knowledge.md §8`. Target: ~250-350 lines, 0 axioms,
0 sorries, builds against current Mathlib via `proofs/scripts/docker-build.sh
Proofs.LawOfCosinesOQ04OQ02OQ01`.

A successful S2 unblocks S3 (gallery `meta.json`/`index.ts` + parent
`openQuestions` update) and the Mathlib-upstream candidate
`Mathlib.Geometry.Euclidean.AngleBisector`.

## Blockers

None.
