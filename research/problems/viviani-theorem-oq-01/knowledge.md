# Viviani's Theorem (viviani-theorem-oq-01)

**Statement.** For any point inside an equilateral triangle, the sum of the
perpendicular distances from the point to the three sides equals the triangle's
altitude — independent of the point.

**Gallery status.** No prior gallery entry. Mathlib has no Viviani theorem.
This is genuine new content, not a wrapper.

## Summary

Formalized via an explicit coordinate model rather than the synthetic
`EuclideanGeometry` area API (which is fiddly for triangle areas). The
coordinate route reduces the whole statement to a `ring` identity once the
absolute values in the point-to-line distance formula are resolved on the
triangle interior.

### Model

Unit-side equilateral triangle `A=(0,0)`, `B=(1,0)`, `C=(1/2, √3/2)`. Sides:

| Side | Line `aX+bY+c=0` | `(a,b,c)` | `√(a²+b²)` |
|------|------------------|-----------|------------|
| AB   | `Y=0`            | `(0,1,0)` | `1` |
| AC   | `√3·X − Y = 0`   | `(√3,−1,0)` | `2` |
| BC   | `√3·X + Y − √3=0`| `(√3,1,−√3)` | `2` |

Perpendicular distance `distToLine a b c x y = |a x + b y + c| / √(a²+b²)`.

Interior half-planes: `y ≥ 0`, `√3 x − y ≥ 0`, `√3 x + y − √3 ≤ 0`. On the
interior:
- `d_AB = y`
- `d_AC = (√3 x − y)/2`
- `d_BC = (√3 − √3 x − y)/2`
- **sum = √3/2 = altitude**, independent of `(x,y)`. (`ring`.)

The only irrational fact used is `(√3)² = 3` (`Real.sq_sqrt`).

## Built items (proofs/Proofs/VivianiTheorem.lean, build-pending)

- `distToLine` — point-to-line perpendicular distance.
- `dist_AB / dist_AC / dist_BC` — per-side distance evaluation on the interior
  (resolve `|·|` via `abs_of_nonneg` / `abs_of_nonpos`, denominators via
  `Real.sqrt_sq`).
- `viviani` — main theorem: sum of the three distances `= √3/2`.
- `altitude_eq` — apex-to-base distance is `√3/2` (justifies the RHS as the
  altitude).
- `interior_nonempty` — centroid `(1/2, √3/6)` satisfies all three constraints,
  so the hypotheses are non-vacuous.

**Axiom/sorry count:** 0 axioms, 0 sorries (claimed; awaits a green build).

## Mathlib gaps

None blocking. Mathlib lacks a Viviani statement but supplies everything used
(`Real.sqrt`, `Real.sq_sqrt`, `Real.sqrt_sq`, `abs_of_nonneg/nonpos`).

## Verification status

**VERIFIED 2026-06-16 (Session 2).** `docker-build.sh Proofs.VivianiTheorem` →
`✔ [7743/7743] Built Proofs.VivianiTheorem (136s)`, 0 errors. The hand-derived
proof compiled exactly as written. Registered in `proofs/Proofs.lean` and
integrated into the gallery (`src/data/proofs/viviani-theorem-oq-01/`).
Final: verified, 0 axioms / 0 sorries.

(Session 1 was written under a dual backend blackout — Aristotle 404 + corrupt
`proofs/.lake` self-symlink — and committed as a build-pending orphan.)

## Next steps

1. On Docker recovery: `./proofs/scripts/docker-build.sh Proofs.VivianiTheorem`.
2. If green: register in `proofs/Proofs.lean`, add `src/data/proofs/viviani-theorem/`
   gallery integration (meta.json), mark COMPLETED.
3. If any rewrite fails to match: the math is correct; likely fixes are
   `simp only [distToLine]` instead of `unfold`, or adjusting the `show`
   numeral forms. The final identity is a pure `ring` step.
4. Optional generalization (follow-up OQ): arbitrary triangle → sum of
   *weighted* distances, or the 3D analogue (sum of distances to faces of a
   regular tetrahedron = its height).

## Sessions

### 2026-06-16 (Session 1, researcher-12) — FRESH
**Outcome:** progress (build-pending complete proof).
Claimed the fresh seeker stub (no prior artifacts). Chose the coordinate model
over synthetic geometry. Wrote `VivianiTheorem.lean` with a full hand-derived
proof (0 sorry / 0 axiom claimed). Could not verify: Aristotle 404 + corrupt
`.lake`. Committed as orphan + PR, documented here. Phase → ACT.

### 2026-06-16 (Session 2, researcher-12) — REVISIT / VERIFY
**Outcome:** COMPLETED (build-verified, registered, gallery-integrated).
Docker recovered (cache volume intact, host had only 2 lean containers). Ran
`docker-build.sh Proofs.VivianiTheorem` → `✔ [7743/7743] Built` in 136s, 0
errors. The hand-derived proof compiled exactly as written — no rewrite/`show`
adjustments needed. Registered the import in `proofs/Proofs.lean` (after
`VietasFormulasOQ03OQ05`); authored gallery `meta.json` + `annotations.json`
under `src/data/proofs/viviani-theorem-oq-01/`. Aristotle still 404 (not
needed). Phase → COMPLETED. Final status: verified, 0 axioms / 0 sorries.
