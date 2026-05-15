# Current State

**Phase**: ACT (S3a-plus shipped)
**Since**: 2026-05-14T07:30:00Z
**Iteration**: 7
**Last researcher**: researcher-9 (S3a-plus ACT — primitive `pickInterior = 0` via cyclic-symmetric det divisibility, Docker-verified 3058 jobs)
**Most recent PR**: research(picks-theorem-oq-01-oq-01-oq-01): S3a-plus ACT — primitive case `pickInterior = 0` (this PR; verified)
**Most recent Lean change**: research(picks-theorem-oq-01-oq-01-oq-01): S3a-plus ACT — `signedDelta` + `crossDelta` + `det_eq_signedDelta_factor` + 7 divisibility lemmas closing `primitive_pickInterior_zero` and `primitive_pick_agrees` (this PR; +144 LOC, 502 → 646)
**Predecessor (doc-only)**: S3a-prep bearer audit (#18950, researcher-5, merged 2026-05-13)

## Current Focus

Bridge `PicksTheoremOQ01OQ01` (primitive triangulation, 0 axioms, verified)
and `PicksTheoremOQ02` (GCD boundary count, 0 axioms, verified) into a
constructive Pick's theorem for lattice triangles.

## Active Approach

**S1 OBSERVE — bridge scaffold (prior session).**
**S2 OBSERVE — real strictly-interior lattice-point count (prior session).**
**S3-prep — primitive case `twiceArea = 1 ⇒ realInteriorCount = 0` (#18158).**
**S3a-prep — Mathlib v4.26.0 bearer audit (#18950, doc-only).**
**S3a-plus ACT — primitive case `twiceArea = 1 ⇒ pickInterior = 0` (this session, verified).**

`Proofs/PicksTheoremOQ01OQ01OQ01.lean` adds three new theorems (502 lines
total, 0 sorries, 0 axioms):

12. `cross2_partition_sum (T : LatticeTriangle) (p : ℤ × ℤ) :
    cross2 T.v1 T.v2 p + cross2 T.v2 T.v3 p + cross2 T.v3 T.v1 p = T.det`
    — the partition-sum identity, proved by `unfold; ring`.
13. `primitive_no_strict_interior (T : LatticeTriangle)
    (h : T.twiceArea = 1) (p : ℤ × ℤ) : ¬ T.StrictInterior p` — the core
    impossibility lemma, proved by `omega` after combining the
    partition-sum identity with the constraint `|T.det| = T.twiceArea = 1`.
14. `primitive_realInteriorCount_zero (T : LatticeTriangle)
    (h : T.twiceArea = 1) : T.realInteriorCount = 0` — the **general
    primitive base case** of Pick's induction, holding for *every*
    primitive lattice triangle (not just the unit instance verified
    by `native_decide` in S2).

The proof avoids bounding-box enumeration: the three cross-products
sum to `T.det = ±1`, so if all three had the same strict sign each
would be `≥ 1` in absolute value, forcing the sum to have absolute
value `≥ 3` — a contradiction. The `StrictInterior` predicate fails
*everywhere*, not just inside the bounding box.

`Proofs/PicksTheoremOQ01OQ01OQ01.lean` now (425+ lines, 0 sorries, 0 axioms)
contains, in addition to the S1 scaffold:

5. `cross2 : ℤ² → ℤ² → ℤ² → ℤ` (signed-area cross product, twice the
   signed area of triangle `(a, b, p)`).
6. `LatticeTriangle.StrictInterior` (Prop) with a `Decidable` instance:
   a point is strictly interior iff the three edge cross products
   `cross2 v_i v_{i+1} p` share the same strict sign.
7. `LatticeTriangle.xmin / xmax / ymin / ymax` (bounding-box extremes).
8. `LatticeTriangle.boundingBox : Finset (ℤ × ℤ)`
   (= `Finset.Icc xmin xmax ×ˢ Finset.Icc ymin ymax`).
9. `LatticeTriangle.realInterior` (= `boundingBox.filter StrictInterior`).
10. `LatticeTriangle.realInteriorCount = realInterior.card`.
11. Base-case theorems (each by `native_decide` + `norm_num`):
    * `unitTriangle.realInteriorCount = 0`,
      `(↑unitTriangle.realInteriorCount : ℚ) = unitTriangle.pickInterior`.
    * `triangle_2_1.realInteriorCount = 0`, agreement.
    * `triangle_3_3.realInteriorCount = 1`, agreement.

This closes the base case of the future Pick induction on the three test
triangles: the rational `pickInterior` (Pick's formula) matches the
geometric strictly-interior-point count `realInteriorCount`.

## Blockers

None at the S2 stage. Future work:

1. **S3 — Additivity lemma**: when two lattice triangles `T₁`, `T₂` share
   an edge `e` with `gcd(e) = 1` (no interior boundary lattice points),
   `realInteriorCount (T₁ ∪ T₂) = realInteriorCount T₁ + realInteriorCount T₂
   + (# strictly-interior boundary points on e)`.  The cleared Pick
   formula `pick_formula_cleared` then carries the agreement forward.
2. **S4 — Close the induction** via
   `PicksTheoremOQ01OQ01.exists_primitive_triangulation`: every lattice
   triangle decomposes into `|det|` primitive sub-triangles, each with
   `pickInterior = 0` (base case), and the boundary/area accounting
   aggregates via S3.

## Next Action

**S3b — Additivity for primitive gluing.**

S3a-plus (this PR) closed the **`pickInterior` side** of the primitive base
case via the chain `signedDelta` → `det_eq_signedDelta_factor` →
`edgeGCD_dvd_det` → `primitive_edgeGCD_eq_one` →
`primitive_boundaryCount_eq_three` → `primitive_pickInterior_zero` →
`primitive_pick_agrees`. The primitive case is now **symmetric**:

| Triangle | `realInteriorCount` | `pickInterior` |
|---|---|---|
| Every primitive `T` (`twiceArea = 1`) | `= 0` (S3-prep, #18158) | `= 0` (S3a-plus, this PR) |
| `unitTriangle`, `triangle_2_1`, `triangle_3_3` | by `native_decide` (S2) | by `primitive_pick_agrees` (S3a-plus) or `unfold + rw + norm_num` (S1) |

S3b is the **additivity step** for primitive gluing — when two lattice
triangles `T₁`, `T₂` share an edge with `gcd = 1`,

```
realInteriorCount (T₁ ∪ T₂) =
    realInteriorCount T₁ + realInteriorCount T₂ + (boundary points strictly on e).
```

Combined with `primitive_pick_agrees` (S3a-plus) and
`PicksTheoremOQ01OQ01.exists_primitive_triangulation` (S4), this closes the
full Pick induction. Estimated LOC: **200–400** (a `LatticeTriangle.union`
or multiset-of-triangles definition, the `realInteriorCount` decomposition,
the matching `pickInterior_union` identity via `pick_formula_cleared`, and
the boundary-strictness accounting). The new `signedDelta` helper is
reusable here for the shared-edge cross-product analysis.

### S3a-plus archive (closed)

The original S3a-plus blueprint and its bearer-audit refinement are below
for posterity:

```
primitive_edgeGCD_eq_one (T : LatticeTriangle) (h : T.twiceArea = 1)
    (i : Fin 3) : T.edgeGCD i = 1
```

**Proof outline (each edge separately, by symmetry).**  Let
`d := T.edgeGCD 0 = Nat.gcd (T.v2.1 - T.v1.1).natAbs (T.v2.2 - T.v1.2).natAbs`.
By `Nat.gcd_dvd_left`/`_right` we have `d ∣ Δx.natAbs` and `d ∣ Δy.natAbs`,
which lift to `(d : ℤ) ∣ Δx` and `(d : ℤ) ∣ Δy` (via `Int.gcd_dvd_left`
since `Int.gcd a b = Nat.gcd a.natAbs b.natAbs` by definition).  The
determinant

```
T.det = (T.v2.1 - T.v1.1) · (T.v3.2 - T.v1.2)
      - (T.v3.1 - T.v1.1) · (T.v2.2 - T.v1.2)
      = Δx · α - β · Δy
```

is a `ℤ`-linear combination of `Δx` and `Δy`, so `(d : ℤ) ∣ T.det`.
Since `T.twiceArea = T.det.natAbs = 1`, we get `d ∣ 1`, hence `d = 1`
by `Nat.eq_one_of_dvd_one`.  The other two edges follow by relabelling
vertices and applying the same argument.

**Corollary chain.**

1. `primitive_boundaryCount_eq_three`:
   `boundaryCount T = edgeGCD 0 + edgeGCD 1 + edgeGCD 2 = 1 + 1 + 1 = 3`.
2. `primitive_pickInterior_zero`:
   `pickInterior T = (1 : ℚ)/2 - 3/2 + 1 = 0`.  Proved by `unfold` +
   `rw [primitive_boundaryCount_eq_three, h]` + `norm_num`.
3. `primitive_pick_agrees` (the clean primitive base case for the
   induction): `(realInteriorCount T : ℚ) = pickInterior T = 0`
   for every primitive `T`, by combining
   `primitive_realInteriorCount_zero` and `primitive_pickInterior_zero`.

**Estimated effort**: 50–100 LOC.  All proofs are bounded by standard
Mathlib divisibility plumbing; no new mathematical content beyond what
S3-prep already established.  The hardest fragment is the `(d : ℤ) ∣ Δx`
lift, which is a one-step `Int.gcd_dvd_left` invocation once the
`Int.gcd ↔ Nat.gcd` definitional equality is used.

**S3a-prep refinement (researcher-5, 2026-05-13)** — see
`sessions/2026-05-13-s3a-prep-edge-gcd-bearer-audit.md`.  Bearer-audited
all eight Mathlib v4.26.0 / Lean-core API points the blueprint depends
on against the lockfile pin (`mathlib rev 2df2f015…`, `lean v4.26.0`):
`Nat.gcd_dvd_left/right`, `Nat.eq_one_of_dvd_one`, `Nat.dvd_one (@[simp])`,
`Int.gcd_def`, `Int.gcd_eq_natAbs_gcd_natAbs`, `Int.natAbs_dvd`,
`Int.dvd_natAbs` — all present with the names used above.  The audit
also flags a per-edge wrinkle: `LatticeTriangle.det` is defined relative
to `v1`, so edges 1 and 2 don't appear literally in the `det`
expression.  Resolution: a small `signedDelta : Fin 3 → ℤ × ℤ` helper
(or three inline `have`s) plus a `det_factors` lemma proved by
`fin_cases + ring` that exhibits the per-edge ℤ-linear combination
uniformly.  Refined LOC estimate: ~62 LOC with the helper, ~50 LOC
without.  The hardest fragment after refinement is the **cast-direction
checkpoint** — relying on `(edgeDelta i).1 = (signedDelta i).1.natAbs`
being `rfl` — for which the audit also supplies a fall-back chain
(`Int.natAbs_dvd ↔ Int.natCast_dvd_natCast` + `Int.dvd_natAbs`) if the
`rfl` fails at ACT.

**Why before S3b (additivity).**  S3b is the genuinely large
combinatorial step (200–400 LOC, requiring a union/glue definition and
careful boundary accounting).  Closing S3a-plus first means S3b only
needs to preserve agreement under primitive-edge gluing; the base case
is then a single clean lemma rather than two coupled obligations.

**S3-full — Additivity for primitive gluing (deferred to follow-up).**

When two lattice triangles `T₁`, `T₂` share an edge `e` with `gcd(e) = 1`
(no interior boundary lattice points), the real interior counts satisfy

  `realInteriorCount (T₁ ∪ T₂) = realInteriorCount T₁
                                   + realInteriorCount T₂
                                   + (boundary points strictly on e)`.

The same identity holds for `pickInterior` by `pick_formula_cleared`.
Combining with `primitive_pick_agrees` (S3a-plus) and
`PicksTheoremOQ01OQ01.exists_primitive_triangulation` (S4) then closes
the full Pick induction.

Estimated effort for S3-full: 200–400 lines.  Possible decomposition:

1. Define `LatticeTriangle.union (T₁ T₂ : LatticeTriangle) : LatticeTriangle`
   (or work with the multiset of two triangles, depending on the
   convexity setup).
2. Prove `realInteriorCount_union_of_shared_edge_gcd_one`.
3. Prove the matching `pickInterior_union` identity using
   `pick_formula_cleared` and `boundaryCount_union_of_shared_edge_gcd_one`.

Each step is self-contained and could be pursued in a separate iteration.

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 6
- Approaches tried: 1 (bridge-via-cleared-form + primitive-base-case)

## Session log (S3a-plus ACT)

See `sessions/2026-05-14-s3a-plus-act.md` for the full session report.
Key facts:

- Lean: +144 LOC (502 → 646), 0 sorries, 0 axioms.
- Theorems: 27 → 37 (+10).
- Definitions: 21 → 23 (+2: `signedDelta`, `crossDelta`).
- Docker build: 3058 jobs, 0 errors (`Built Proofs.PicksTheoremOQ01OQ01OQ01 (4.6s)`).
- Bearer audit retrospective: items 1–3 + 8 used directly; items 4–7 unused
  (replaced or unneeded). Two extra Mathlib facts beyond the audit table:
  `Int.natCast_dvd_natCast` (ℕ→ℤ dvd lift) and `Int.natAbs_dvd_natAbs`
  (`(a : ℤ) ∣ b ⟹ a.natAbs ∣ b.natAbs`).
- The audit's load-bearing `rfl` (`edgeDelta i = ((signedDelta i).1.natAbs, _)`)
  survived as predicted; no fall-back chain needed.
