# Research State: roth-theorem-k3-oq-02-incomplete-01

## Current State
**Phase**: OBSERVE → done (transitioning to ORIENT/ACT)
**Path**: full
**Since**: 2026-04-03T02:25:34-07:00
**Iteration**: 2-OBSERVE (S2, researcher-1, 2026-05-30, doc-only)
**Last Updated**: 2026-05-30

## Current Focus (S2, researcher-1, 2026-05-30)

S2 OBSERVE iteration: full inventory of the 2 sorries in
`proofs/Proofs/RothTriangleRemoval.lean` (lines 292 and 309) with concrete
attack plans for both, plus a leaf-file cross-traffic verification (0
importers). Both sorries reduce, via the canonical `(a, x) ∈ A × ZMod N`
parametrization of triangles, to a 6-fold counting argument and an
edge-disjointness injection. The full plan is captured in:

- `sessions/2026-05-30-s2-observe-sorry-attack-plan.md` (this session)

This is the first substantive content for `knowledge.md` (which was empty
template) — the session memo carries the technical content directly until
knowledge.md is updated in a later session.

## Sorry inventory

| # | Line | Lemma | Statement | Difficulty |
|---|---|---|---|---|
| 1 | 292 | `rs_tc_ap_free_le` | `triangleCount G univ univ univ ≤ 6 * A.card * N` | MEDIUM (Fin 6 permutation) |
| 2 | 309 | `rs_removal_lb` | `R` covers all canonical triangles → `A.card * N ≤ R.card` | MEDIUM (edge-disjoint injection) |

## Recommended ACT plan (split into 3 sub-ACTs)

| ACT | Target | Est. LOC | Risk | Status |
|---|---|---|---|---|
| S3 | `yz_edge_unique_triangle` + `xz_edge_unique_triangle` (missing helpers) | ~50 | LOW | not started |
| S4 | Discharge sorry #1 (`rs_tc_ap_free_le`) via Fin 6 × A × ZMod N embedding | ~60 | MEDIUM | not started |
| S5 | Discharge sorry #2 (`rs_removal_lb`) via canonical-triangle → R injection | ~70 | MEDIUM | not started |

## Available infrastructure (file already proves, 0 sorry)

- `triangle_yields_ap_triple` (line 143) — triangle → APTriple
- `ap_free_forces_equal` (line 196) — under AP-free, APTriple gives a=b=c
- `ap_triple_yields_triangle` (line 162) — APTriple → triangle
- `ap_free_triangle_exists` (line 253) — canonical triangle for each (a, x)
- `xy_edge_unique_triangle` (line 228) — XY-edge uniqueness; **YZ and XZ
  analogues NOT YET PROVED → S3 work**
- `ap_free_min_removal` (line 317) — R contains ≥1 directed pair from each
  canonical triangle

## Cross-traffic risk: NONE

```bash
$ grep -rln 'import Proofs.RothTriangleRemoval' proofs/Proofs/ | wc -l
0
```

`RothTriangleRemoval.lean` is a **leaf file** — sub-ACTs cannot cascade
into other gallery files. This removes the non-leaf-parent risk of
problems like `lagrange-four-squares-oq-01-oq-02`.

## Active Approach

Discharge the 2 sorries via the canonical `(a, x)` parametrization:

- **Sorry #1**: build an embedding `T ↪ Fin 6 × A × ZMod N` where `T` is
  the filtered triangle Finset, sending each ordered triangle to
  `(σ, a, x)` where `(a, x)` is its canonical parametrization (from
  `ap_free_forces_equal`) and `σ ∈ Fin 6` is the ordering permutation.
  `card_le_of_injective` + `card_product` gives the 6·|A|·N bound.

- **Sorry #2**: from `ap_free_min_removal`, for each `(a, x) ∈ A × ZMod N`
  use Classical choice on the 6-way disjunction to pick a directed pair
  `p(a, x) ∈ R` from the canonical triangle. Injectivity of `p` follows
  from edge-disjointness of canonical triangles (needs S3 helpers).
  `Finset.card_image_of_injective` gives `|A|·N ≤ |R|`.

## Mathlib bearer audit

No Mathlib v4.26.0 bearer at risk. Plan uses only:
- `Finset.card_le_of_injective`, `Finset.card_product`,
  `Finset.card_image_of_injective`
- `Fin 3`, `Fin 6` decidable equality
- `ZMod N` arithmetic
All stable since Mathlib v4.0. Pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(verified at S2 commit time).

## Attempt Counts

- Total attempts: 2 (S1 = problem.md only 2026-04-03; S2 = OBSERVE attack
  plan 2026-05-30, this session)
- Current approach attempts: 1 (S2 doc-only OBSERVE)
- Approaches tried: 1 (canonical-(a,x) parametrization, viable)

## Blockers

None. The plan is fully grounded in already-proven file lemmas (file is
build-clean at 0 axioms / 2 sorries; sorries are isolated to lines 292 and
309). 3 helper lemmas (YZ / XZ edge uniqueness + edge-disjointness) need
to be added in S3, but copy-paste from the existing XY case is expected.

## Next Action

S3 ACT: add `yz_edge_unique_triangle` and `xz_edge_unique_triangle` as
helper lemmas (estimated ~50 LOC, LOW risk — direct copy/adaptation of
`xy_edge_unique_triangle` at line 228).

## References

- `proofs/Proofs/RothTriangleRemoval.lean:287-292` — sorry #1 site
- `proofs/Proofs/RothTriangleRemoval.lean:301-309` — sorry #2 site
- `proofs/Proofs/RothTriangleRemoval.lean:228-249` — `xy_edge_unique_triangle`
  (template for S3 YZ/XZ helpers)
- `proofs/Proofs/RothTriangleRemoval.lean:317-344` — `ap_free_min_removal`
  (the 6-way disjunction used in sorry #2 attack)
- `proofs/Proofs/SzemerediCounting.lean:165-169` — `triangleCount` definition
- `sessions/2026-05-30-s2-observe-sorry-attack-plan.md` — full S2 attack plan
- `src/data/proofs/roth-theorem-k3-oq-02/meta.json` — gallery metadata
  (status: formalized, badge: wip, sorries: 2, axiomCount: 0)
