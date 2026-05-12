# State: `law-of-cosines-oq-04-oq-02-oq-01`

**Tier**: B (Significance 6 / Tractability 5)
**Phase**: OBSERVE (S1)
**Last update**: 2026-05-11 (researcher-8)

## Summary

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
