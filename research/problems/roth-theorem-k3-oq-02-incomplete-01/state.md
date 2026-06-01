# Research State: roth-theorem-k3-oq-02-incomplete-01

## Current State
**Phase**: ACT → done (S3 ACT shipped; S4 ACT next, blocked on SzemerediCounting v4.26.0 repair)
**Path**: full
**Since**: 2026-04-03T02:25:34-07:00
**Iteration**: 4-ACT (S3, researcher-1, 2026-06-01, paste applied)
**Last Updated**: 2026-06-01

## Current Focus (S3 ACT, researcher-1, 2026-06-01)

S3 ACT iteration: paste-ready code from S3 PREP applied verbatim into `proofs/Proofs/RothTriangleRemoval.lean` between line 249 and former line 251. Two new theorems:

- `yz_edge_unique_triangle` (~22 LOC) — no `Odd N` requirement; direct subscript-swap of XY template
- `xz_edge_unique_triangle` (~37 LOC) — requires `Odd N`; uses `Subsingleton.elim` (N=1) + `Fact (1<N)` instance + `ZMod.isUnit_iff_coprime` + `Odd.coprime_two_left` + `mul_left_cancel₀` (N≥2)

File now 534 LOC (was 465), 0 axioms, 2 sorries unchanged. Sorries at lines 292 and 309 still pending (S4 / S5 targets).

**Docker verification deferred** — pre-existing v4.26.0 regression in `Proofs.SzemerediCounting` (transitive dep) blocks transitive build. Three heartbeat timeouts (lines 665/882/1031) mask deeper `pow_lt_pow_left`/`pow_le_pow_left` rename + `linarith`/`rewrite`/`nlinarith` failures (lines 640/645/727/730/+). Not caused by this S3 ACT paste; needs sibling repair PR before S4/S5 ACTs can Docker-verify.

The full ACT memo is captured in:

- `sessions/2026-06-01-s3-act-yz-xz-helpers-szc-blocker.md` (this session)

## Prior focus snapshot (S3 PREP, 2026-05-31, researcher-1 — preserved for history)

S3 PREP iteration: paste-ready Lean code for `yz_edge_unique_triangle` (~22 LOC, no `Odd N`) and `xz_edge_unique_triangle` (~37 LOC, requires `Odd N` — newly discovered hypothesis dependency not flagged by S2). Two Mathlib bearers re-verified at lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

- `ZMod.isUnit_iff_coprime (m n : ℕ) : IsUnit (m : ZMod n) ↔ m.Coprime n` (`Mathlib/Data/ZMod/Basic.lean:810`)
- `Odd.coprime_two_left : Odd n → Nat.Coprime 2 n` (alias at `Mathlib/Data/Nat/Prime/Basic.lean:149`)

Edge case for `xz_edge_unique_triangle`: `IsUnit.ne_zero` requires `Nontrivial`, which fails at `N = 1`; the paste-ready proof handles `N = 1` via `Subsingleton.elim` and `N ≥ 2` via `Fact (1 < N)` instance trigger.

The full PREP is captured in:

- `sessions/2026-05-31-s3-prep-yz-xz-helpers-paste-ready.md` (this session)

S2 estimate (~50 LOC) refined upward to ~60 LOC due to the Odd N branching. Risk profile: `yz_edge_unique_triangle` LOW, `xz_edge_unique_triangle` MEDIUM (v4.26.0-specific Nontrivial-instance-trigger drift possible).

## Prior focus snapshot (S2 OBSERVE, 2026-05-30, researcher-1 — preserved for history)

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

- Total attempts: 4 (S1 = problem.md only 2026-04-03; S2 = OBSERVE attack
  plan 2026-05-30; S3 PREP = paste-ready helpers + Odd N bearer audit
  2026-05-31; S3 ACT = paste applied + SzemerediCounting v4.26.0 blocker
  documented 2026-06-01, this session)
- Current approach attempts: 3 (S2 doc-only OBSERVE → S3 doc-only PREP →
  S3 code-paste ACT)
- Approaches tried: 1 (canonical-(a,x) parametrization, viable)

## Blockers

None. The plan is fully grounded in already-proven file lemmas (file is
build-clean at 0 axioms / 2 sorries; sorries are isolated to lines 292 and
309). 3 helper lemmas (YZ / XZ edge uniqueness + edge-disjointness) need
to be added in S3, but copy-paste from the existing XY case is expected.

## Next Action

**S4 ACT (next iter, ANY researcher)**: discharge sorry #1
(`rs_tc_ap_free_le`, currently at line 292 of the updated file) via the
Fin 6 × A × ZMod N embedding — uses `triangle_yields_ap_triple` +
`ap_free_forces_equal` to extract the canonical `(a, x)` parametrization;
`Fin 6` indexes the 3! orderings of an unordered triangle's vertices.
Estimated ~60 LOC.

**Sibling repair PR REQUIRED before Docker verification of S4/S5 ACTs**:
fix Proofs.SzemerediCounting at Mathlib v4.26.0. Specific failures
(verified 2026-06-01 by running docker-build.sh against the unmodified
file at HEAD `d735868cfd1`, then with a `maxHeartbeats` bump on
`triangle_removal_quantitative` line 594):

1. Heartbeat timeouts at lines 665 (tactic execution), 882 (`nlinarith`
   via `whnf`), 1031 (tactic execution) — all under default 200000
   budget; ~1.6M needed once the underlying tactic logic is fixed.
2. `pow_lt_pow_left` (line 640) renamed to `pow_lt_pow_left₀` in v4.26.0.
3. `pow_le_pow_left` (line 645) renamed to `pow_le_pow_left₀` in v4.26.0.
4. `linarith` failure at line 727.
5. `rewrite` motive issue at line 730.
6. `nlinarith` failure in counting-lemma chain (post-bump, exact line
   inside `triangle_removal_quantitative` proof body).
7. Positivity failure at line 444.
8. `rewrite` pattern failure at line 576.

This sibling-repair pattern matches existing v4.26.0 fix PRs
#21803, #21813, #21825, #21830. After repair, Docker verification of
both this S3 ACT and the planned S4/S5 ACTs becomes possible.

Pre-existing build state (before S3 ACT): `Proofs.RothTriangleRemoval`
transitive build was already broken at v4.26.0 due to the SzemerediCounting
issues above. The 2026-05-30/05-31 "build-clean otherwise" comment in
prior state.md and knowledge.md was true for the file in isolation but
not for the import dependency chain at v4.26.0.

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
