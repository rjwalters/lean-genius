# Knowledge Base: feuerbachs-theorem-oq-02-incomplete-01

3D Feuerbach's theorem for orthocentric tetrahedra. The twenty-four-point
sphere is internally tangent to the insphere and externally tangent to the
four exspheres. The orthocentric hypothesis (opposite edges perpendicular)
is essential — it does NOT hold for general tetrahedra.

---

## File Map

- `proofs/Proofs/FeuerbachsTheoremOQ02.lean`: main formalization (665 lines)
  - 5 sorry'd theorems: `feuerbach_3d_insphere`, `feuerbach_3d_exsphere_{A,B,C,D}`
  - 3 axioms: `feuerbach_3d_fails_general`, `edge_midpoints_on_sphere`,
    `face_centroids_on_sphere`
  - Proven: orthocentric_third_perp, monge_point_euler_line,
    centroid_on_euler_line, volume_eq_inradius_surfaceArea, circumcenter_equidist
- `proofs/Proofs/FeuerbachsTheoremOQ02Aristotle.lean`: companion (124 lines)
  - 14 → 5 sorry'd helper lemmas after this session

---

## Session 2026-04-27 — Aristotle Companion Cleanup

**Mode**: FRESH (knowledge_score=4 WEAK; problem.md was a stub).

### What Was Done

Filled 9 of 14 routine helper sorries in `FeuerbachsTheoremOQ02Aristotle.lean`:

| Lemma | Tactic |
|-------|--------|
| `dist3_sq_nonneg` | `positivity` |
| `dist3_sq_comm` | `ring` |
| `dot3_self_nonneg` | `positivity` |
| `dot3_comm` | `ring` |
| `dot3_add_left` | `ring` |
| `internally_tangent_sym` | `abs_sub_comm _ _` |
| `externally_tangent_sum_comm` | `add_comm _ _` |
| `twentyFourPoint_radius_third_of_circum` | `linarith` |
| `ortho_edge_sum_identity` | `linear_combination 2 * hab_cd - 2 * hac_bd` |

### The `ortho_edge_sum_identity` Computation

For `A B C D : ℝ × ℝ × ℝ` with hypotheses `hab_cd : (B-A)·(D-C) = 0` and
`hac_bd : (C-A)·(D-B) = 0`, the goal is
`|AB|² + |CD|² = |AC|² + |BD|²`.

Expanding componentwise (writing each `·` as the explicit coordinate dot):

```
LHS - RHS = 2 · [B·D + A·C - C·D - A·B]
hab_cd_expr = B·D - B·C - A·D + A·C
hac_bd_expr = C·D - C·B - A·D + A·B
hab_cd_expr - hac_bd_expr = B·D + A·C - C·D - A·B
```

So `LHS - RHS = 2·(hab_cd_expr - hac_bd_expr) = 2·hab_cd - 2·hac_bd`. The
`linear_combination` tactic with these coefficients closes via `ring`.

### Remaining Sorries in Companion File

Five lemmas left, each non-trivial for distinct reasons:

1. `dist3_sq_zero_iff (P Q : ℝ × ℝ × ℝ)`:
   `(Q-P)² sum = 0 ↔ P = Q`. Forward direction needs `sq_eq_zero_iff` +
   `Prod.ext` for `ℝ × (ℝ × ℝ)`. Doable but multi-line.
2. `dot3_self_zero_iff`: similar Prod.ext gymnastics.
3. `midpoint3_equidist`: `let M := ...` in goal type; `ring` may not
   automatically unfold the let. Needs `show` or `dsimp only` first.
4. `midpoint3_spec`: same `let` issue.
5. `externally_tangent_radii_nonneg`: **lemma is FALSE as stated**. The
   hypotheses (0 < d, d = r₁ + r₂, 0 ≤ r₁) do NOT force 0 ≤ r₂
   (counterexample: r₁ = 3, r₂ = -1, d = 2). Should be removed or restated.

### Key Insights

- The Aristotle companion's "routine" lemmas are a mix: most are pure ring
  identities that succumb to `ring`/`positivity`/`linear_combination`, but
  some encode incorrect or subtler claims (e.g. `externally_tangent_radii_nonneg`
  is unprovable as stated).
- The `linear_combination` tactic is well-suited to dot-product / coordinate
  identities once the right coefficient is computed by hand.
- The five main 3D Feuerbach sorries (`feuerbach_3d_insphere`,
  `feuerbach_3d_exsphere_{A,B,C,D}`) remain — these require deep coordinate
  computations equivalent to the 2D case and depend on the axiomatized
  edge-midpoint and face-centroid lemmas.

### Files Modified

- `proofs/Proofs/FeuerbachsTheoremOQ02Aristotle.lean` (-12 +13 lines, 14 → 5 sorries)

### Sorry/Axiom Delta

- Aristotle companion sorries: 14 → 5 (-9)
- Main file sorries: 5 → 5 (no change)
- Axioms: 3 → 3 (no change)

### Next Steps

1. **Companion completion**: prove the four remaining tractable sorries
   (`dist3_sq_zero_iff`, `dot3_self_zero_iff`, `midpoint3_equidist`,
   `midpoint3_spec`) using `Prod.ext` and `dsimp only` for let bindings.
2. **Statement correction**: remove or fix `externally_tangent_radii_nonneg`
   (currently unprovable).
3. **Main theorem progress**: the five `feuerbach_3d_*` sorries require
   showing |N₂₄ - I|² = |R/3 - r|² (insphere case) symbolically. This is
   deep; depends on the axioms `edge_midpoints_on_sphere` and
   `face_centroids_on_sphere` which are themselves substantial.
4. **Axiom decomposition**: the three axioms could be replaced by sorries
   and submitted to Aristotle as a separate effort.

---

## Dead Ends

- 5 tangency sorries likely unfillable (formulas appear mathematically incorrect)
- feuerbach_3d_fails_general hard to prove (sqrt in face areas)

---

## Session 2026-04-27 (Session 2) — Companion File Cleanup

**Mode**: REVISIT (after Session 1's mathematical-error discovery)
**Outcome**: Filled all 13 routine sorries in `FeuerbachsTheoremOQ02Aristotle.lean`; fixed 1 false statement.

### Changes to FeuerbachsTheoremOQ02Aristotle.lean

**Proved (12 lemmas, previously sorries):**
- `dist3_sq_nonneg` — `positivity`
- `dist3_sq_zero_iff` — destructure + `nlinarith` + `sq_eq_zero_iff`
- `dist3_sq_comm` — `ring`
- `dot3_self_nonneg` — `nlinarith [mul_self_nonneg ...]`
- `dot3_self_zero_iff` — destructure + nlinarith + `mul_self_eq_zero`
- `dot3_comm`, `dot3_add_left` — `ring`
- `midpoint3_equidist`, `midpoint3_spec` — `simp only; ring`
- `internally_tangent_sym` — `abs_sub_comm`
- `externally_tangent_sum_comm` — `ring`
- `twentyFourPoint_radius_third_of_circum` — `linarith`
- `ortho_edge_sum_identity` (the isodynamic property!) — `linear_combination 2 * hab_cd - 2 * hac_bd`

**Statement fix:**
- `externally_tangent_radii_nonneg` was FALSE as written (counterexample r₁=10, r₂=-5, d=5).
  Added missing precondition `hr₁_le_d : r₁ ≤ d` to make the statement correct.
  This matches the geometric intent for non-degenerate external tangency.

### Build Verification
- `./proofs/scripts/docker-build.sh Proofs.FeuerbachsTheoremOQ02Aristotle` succeeds with
  64GB memory budget. Only unused-variable warnings remain.
- Sorry count in companion file: 13 → 0. Axioms: 0 → 0.

### Honest Progress Assessment

This session did NOT advance the main 5-sorry tangency theorems (still flagged "likely
unfillable"). The companion file consists of routine geometric helper lemmas; their proofs
are valuable scaffolding for future work but do not substitute for the deep tangency
results that remain open. The isodynamic property `ortho_edge_sum_identity` is the most
substantial new lemma proved (a classical fact about orthocentric tetrahedra).

The 5 main sorries appear to require:
1. Literature search to identify the correct sphere/radius (likely NOT N₂₄ at radius R/3)
2. Restating the theorems with the correct geometric objects (e.g., midedge sphere)
3. Then a coordinate computation analogous to the 2D Feuerbach proof

---

## Problem Understanding

### What the file proves

- **Definitions** (full): tetrahedron, orthocentric variant, edge lengths,
  face areas, centroid, edge/face midpoints, circumcenter (via Cramer's
  rule), Monge point, twenty-four-point center/radius, incenter, inradius,
  excenters, exradii, and sphere tangency conditions.
- **Theorems** (proven, no sorry, 0 axioms): `orthocentric_third_perp`,
  `monge_point_euler_line`, `twentyFourPointCenter_midpoint`,
  `twentyFourPointRadius_eq`, `centroid_on_euler_line`,
  `volume_eq_inradius_surfaceArea`, `Tetrahedron.circumcenter_equidist`.

### What remains open

- 5 main 3D Feuerbach tangency theorems (deep)
- 3 axioms (counterexample existence + 24-point sphere completeness)
- 5 routine helper lemmas in the Aristotle companion file
