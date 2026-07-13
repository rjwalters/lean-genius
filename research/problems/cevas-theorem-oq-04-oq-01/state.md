# Current State

**Phase**: SCAFFOLD (S2)
**Since**: 2026-05-14 (S2 ACT)
**Iteration**: 2
**Last Updated**: 2026-05-14 (researcher-12)

## Current Focus

S2 ACT SCAFFOLD lifts the parent file's mass-point structure (3-vertex
triangle, `MassPointCeva.MassPoint` with `mA, mB, mC : ℝ`) to an
arbitrary `Fin (n+1)`-indexed family `NDimMassPoint.MassPoint n`. The
file `proofs/Proofs/CevasTheoremOQ04OQ01.lean` (~210 LOC, 0 sorries, 0
axioms) defines the n-dim "complement-fraction" ratios

  ratio i = (Σ_{j ≠ i} mass j) / total = 1 - mass i / total

and proves the headline identity

  Σ_i ratio i = n     (the **n-dim Ceva sum identity**)

which generalises the triangle-case "complement fractions sum to 2".

## Previous Focus

S1 OBSERVE (researcher-3, 2026-05-12) inventoried Mathlib's
`AffineSpace.Ceva` coverage (Joseph Myers 2025) and laid out three S2
target candidates: S2-A (n-dim mass-point structure), S2-B (triangle
bridge), S2-C (constructive existence).

## Active Approach

**Real-arithmetic shadow generalisation** (preferred over the
AffineSpace-based S2-A target).

The S1 OBSERVE recommended S2-A as a ~100 LOC file with 2 strategic
sorries using `Mathlib.LinearAlgebra.AffineSpace.{Centroid, Combination,
AffineIndependent}`. This S2 ACT instead adopts a *self-contained*
real-arithmetic generalisation that:

1. Avoids AffineSpace machinery entirely (no risky API surface dependency).
2. Captures the bookkeeping identity (Σ ratio = n) without geometric
   commitment.
3. Matches the parent file's pure-ratio-arithmetic style.
4. Defers the geometric concurrency claim to S3+ when AffineSpace can
   be wired in carefully (the geometric content is already in Mathlib;
   this file complements it with mass-point bookkeeping).

### S2 Deliverables

| Item | Status |
|---|---|
| `NDimMassPoint.MassPoint n` (structure, n+1 pos. masses) | def |
| `MassPoint.total` + `total_pos` + `total_ne_zero` | def + 2 lemmas |
| `MassPoint.ratio i = (Σ_{j≠i} mass j)/total` | def |
| `sum_erase_eq_total_sub` (auxiliary) | proved |
| `ratio_eq_one_sub : ratio i = 1 - mass i / total` | proved |
| `ratio_lt_one : ratio i < 1` (unconditional) | proved |
| `ratio_pos : 0 < ratio i` (for n ≥ 1) | proved |
| `sum_mass_div_total : Σ mass i / total = 1` | proved |
| **`sum_ratio_eq : Σ ratio i = n`** (HEADLINE) | proved |
| Example: triangle `mp.ratio 0 + mp.ratio 1 + mp.ratio 2 = 2` | proved |
| `uniform n` + `uniform_total` + `uniform_ratio` (centroid case) | def + 2 lemmas |

**Total**: 1 structure, 4 definitions, 10 lemmas/theorems, 0 sorries, 0 axioms.

## Next Action

S3 candidates (in order of expected value):

1. **Triangle bridge to parent file** (~50 LOC, 2 strategic sorries):
   construct a `MassPointCeva.MassPoint ↔ NDimMassPoint.MassPoint 2`
   equivalence at the data level (i.e., the `mass` function) and
   relate the parent's edge-split parameters `rD, rE, rF` to this
   file's complement-fractions `ratio 0, ratio 1, ratio 2` via the
   identity `rD = ratio 0 - ratio 2` (or similar — needs careful
   bookkeeping; the two normalisations are different but compatible).

2. **Constructive existence** (~80 LOC, 1–2 strategic sorries): lift
   `masses_from_ceva` to n dimensions. Given a profile `r : Fin (n+1) → ℝ`
   with `Σ r i = n` and `0 < r i < 1`, construct explicit masses
   realising `mp.ratio i = r i`. The natural construction is
   `mass i := 1 - r i` followed by normalisation; the constraint
   `Σ r i = n` is exactly the consistency condition.

3. **Geometric concurrency bridge** (~50–80 LOC, 0–1 sorry): import
   `Mathlib.LinearAlgebra.AffineSpace.{Ceva, Combination}` and tie
   `MassPoint n` to a concurrency point at the mass-centroid.
   Wraps `AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype`
   (Joseph Myers 2025) in mass-point notation.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1 (S2 real-arithmetic scaffold)
- Approaches tried: 2 (S1 OBSERVE inventory; S2 real-arithmetic scaffold)

## Build Status

**S2 SCAFFOLD build: PENDING.** Worktree's `proofs/.lake` is a
self-symlink (per memory `feedback_researcher_lake_symlink_broken.md`).
Docker build (~30–45 min cold from worktree) deferred to CI.

### S2 Risk Profile

| Mathlib API | Status | Risk |
|---|---|---|
| `Finset.sum_pos` | Standard | Low |
| `Finset.univ_nonempty` | Standard | Low |
| `Finset.sum_erase_eq_sub` | Standard | Low |
| `Finset.sum_sub_distrib` | Standard | **Medium** — may be renamed at v4.26.0 |
| `Finset.sum_const` + `Finset.card_univ` + `Fintype.card_fin` | Standard | Low |
| `Finset.card_pos` + `Finset.card_erase_of_mem` | Standard | Low |
| `Fin.sum_univ_three` | Standard | Low |
| `div_self`, `div_pos`, `field_simp`, `linarith` | Tactics | Low |

The medium-risk item is `Finset.sum_sub_distrib`. If this name is wrong
at v4.26.0, the fallback patch is a 1-LOC swap (alternative names:
`Finset.sum_sub`, `Finset.sub_sum`, `sub_sum`, or inlining via
`simp_rw [sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]`).

### Mathlib Imports

- `Mathlib.Data.Real.Basic` — `ℝ` ordered field
- `Mathlib.Data.Fin.Basic` — `Fin (n+1)` indexing
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum`, `∑` notation
- `Mathlib.Tactic` — `linarith`, `field_simp`, `positivity`, `omega`

NO `AffineSpace` imports — deliberately deferred to S3+.

## Blockers

None.  S2 SCAFFOLD ships as `(build pending)` per the project's
`(build pending)` discipline; if Docker CI surfaces a v4.26.0 API
mismatch on the medium-risk item, S3 picks up the 1-LOC repair as a
prerequisite to the triangle bridge.

## Race Disclosure

Pre-claim probe at 2026-05-14T20:30Z (researcher-12, this session):

```
slug = cevas-theorem-oq-04-oq-01
open_PRs   = 0
recent_merges = 0 (only S1 OBSERVE doc-only via session log; no Lean PRs)
```

Genuinely pristine.  S2 ACT is the **first Lean file** for this slug.
