# Knowledge Base: feuerbachs-theorem-oq-02-incomplete-01

3D analogue of Feuerbach's theorem for tetrahedra. **STATUS (2026-05-02):**
the candidate (N₂₄, R/3)-sphere is FALSE as a Feuerbach sphere — refuted in
closed form at the orthocentric tetrahedron T₀ = ((2,0,0),(0,3,0),(0,0,6),(0,0,0)).
The five tangency theorems and the bundled `feuerbach_3d_theorem` have been
REMOVED from the Lean file (sorries 5 → 0). Identifying and formalizing the
correct Feuerbach sphere (Murakami 1952 / Court 1934, likely face-circumcircle
based) remains an open formalization target.

---

## Session 2026-04-27 (Session 1) -- Mathematical Error Discovery

**Mode**: FRESH (WEAK knowledge tier)
**Outcome**: CRITICAL FINDING -- 2 axioms provably FALSE, tangency theorems likely incorrect

## File Map

- `proofs/Proofs/FeuerbachsTheoremOQ02.lean`: main formalization (665 lines)
  - 5 sorry'd theorems: `feuerbach_3d_insphere`, `feuerbach_3d_exsphere_{A,B,C,D}`
  - 3 axioms: `feuerbach_3d_fails_general`, `edge_midpoints_on_sphere`,
    `face_centroids_on_sphere`
  - Proven: orthocentric_third_perp, monge_point_euler_line,
    centroid_on_euler_line, volume_eq_inradius_surfaceArea, circumcenter_equidist
- `proofs/Proofs/FeuerbachsTheoremOQ02Aristotle.lean`: companion (124 lines)
  - 14 → 5 sorry'd helper lemmas after this session

### False Axioms Identified

**1. `edge_midpoints_on_sphere` (REMOVED)**
- Claimed: edge midpoints at distance R/3 from midpoint(O, M)
- Disproved by: regular tetrahedron (edge midpoints at distance 1 vs R/3 ~ 0.577)
- **Correct**: edge midpoints on sphere centered at G with radius R/2

**2. `face_centroids_on_sphere` (REMOVED)**
- Face centroids NOT equidistant from N24 for non-regular orthocentric tetrahedra

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

### Monge Point Correction
- M != H. Euler line: O(0), G(1), H(2), M(4). H = midpoint(O, M).

### Tangency Theorems Likely False
- dist(N24, I) ~ 1.067 vs |R/3 - r| ~ 0.551 for (2,0,0),(0,3,0),(0,0,6),(0,0,0)

### Changes Made
1. Removed 2 false axioms (3 -> 1)
2. Added edge_midpoints_equidist_from_centroid theorem
3. Fixed docstrings, added warnings

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

---

## Session 2026-05-02 (Session 3) — Closed-Form Refutation

**Mode**: ACT on RICH-tier problem (knowledge_score=34).
**Outcome**: Symbolic counterexample → 5 false sorry theorems removed → 5
sorries → 0. ACT phase advanced (refutation, not yet replacement).

### What Was Done

For the orthocentric tetrahedron `T₀` with vertices

  A = (2, 0, 0), B = (0, 3, 0), C = (0, 0, 6), D = (0, 0, 0),

orthocentricity is verified directly:

  AB · CD = (-2, 3, 0) · (0, 0, -6) = 0
  AC · BD = (-2, 0, 6) · (0, -3, 0) = 0
  AD · BC = (-2, 0, 0) · (0, -3, 6) = 0

Symbolic computation:

  O   = (1, 3/2, 3),  R = 7/2,  R/3 = 7/6
  G   = (1/2, 3/4, 3/2)
  M   = 4G − 3O = (-1, -3/2, -3)
  N₂₄ = midpoint(O, M) = (0, 0, 0)
  S_A = 9, S_B = 6, S_C = 3, S_D = 3√14
  S   = 18 + 3√14 = 3(6 + √14)
  V   = 6
  r   = 3V/S = 6/(6 + √14) = 3(6 − √14)/11
  I   = (r, r, r)
  dist(N₂₄, I) = r√3
  |R/3 − r|    = 7/6 − r

Tangency would require 3r² = (7/6 − r)². With r = 3(6−√14)/11:

  3r²       = 27(6−√14)²/121 = (1350 − 324√14)/121
  (7/6 − r)² = ((-31 + 18√14)/66)² = (5497 − 1116√14)/4356

After multiplying both sides by 4356 = 36·121, equality reduces to

  48600 − 11664√14 = 5497 − 1116√14

which fails component-wise in the ℚ-basis {1, √14}: 48600 ≠ 5497 and
11664 ≠ 1116. Therefore the (N₂₄, R/3)-sphere is NOT internally tangent
to the insphere of T₀.

### Files Modified

- `proofs/Proofs/FeuerbachsTheoremOQ02.lean`:
  - Removed `feuerbach_3d_insphere`, `feuerbach_3d_exsphere_{A,B,C,D}`,
    `feuerbach_3d_theorem`, and the corresponding `#check`.
  - Replaced PART 10 with a refutation comment that records the closed-form
    counterexample and points to Murakami (1952) and Court (1934) as
    candidate correct constructions.
  - Updated the file header status block and the PART 15 summary.
  - Line count: 723 → 688.
  - Sorries: 5 → 0; axioms: 1 → 1.
- `src/data/proofs/feuerbachs-theorem-oq-02/meta.json`:
  - `meta.sorries`: 5 → 0; `leanFile.sorries`: 5 → 0.
  - `leanFile.lineCount`: 723 → 688; `theoremCount`: 21 → 15;
    `substantiveTheoremCount`: 7 → 6.
  - Rewrote `description`, `assumptions`, `originalContributions`,
    `historicalContext`, `text`, `proofStrategy`, `keyInsights`,
    `conclusion`, `openQuestions`, `mainTheorems`, and the `feuerbach-3d`
    section to reflect the refutation.
- `src/data/proofs/feuerbachs-theorem-oq-02/annotations.json`:
  - Replaced `ann-main-theorem` (the "5 sorries" annotation) with
    `ann-3d-feuerbach-refutation` (the closed-form disproof).
  - Rewrote `ann-proved-theorems` to reflect post-refutation status.
- `src/data/research/problems/feuerbachs-theorem-oq-02-incomplete-01.json`:
  - `phase`: ORIENT → ACT.
  - Knowledge insights / built items / progress summary updated.

### Sorry / Axiom Delta

- Main file sorries: 5 → 0 (-5)
- Companion file sorries: 0 → 0 (no change)
- Axioms: 1 → 1 (no change)

### Honest Assessment

This session DOES NOT prove a 3D Feuerbach theorem. It proves that the
candidate sphere previously formalized is the WRONG sphere, and it removes
the five sorry theorems that asserted otherwise. This is meaningful
progress because:

1. It eliminates 5 sorries that no future session could honestly close
   (the underlying claims are false in closed form).
2. It converts a numerical/floating-point intuition (sessions 1–2) into a
   reproducible symbolic argument visible in the source.
3. It leaves the surrounding infrastructure intact for any future attempt
   at the correct (Murakami / Court) Feuerbach sphere.

What this session does NOT do: identify or formalize the correct
3D Feuerbach sphere, prove the existential axiom
`feuerbach_3d_fails_general` (which remains an axiom), or attempt the
midedge-sphere variant (which is also disproved at T₀: dist(G, I)² ≈ 0.812
vs (R/2 − r)² ≈ 1.286).

### Next Steps

1. **Identify the correct Feuerbach sphere.** Murakami (1952) builds it
   from face circumcircles; Court (1934) uses isodynamic data. Either
   construction would require new infrastructure (face circumcircles in
   ℝ³, signed isodynamic ratios) — likely 200–500 lines.
2. **Prove the existential axiom** `feuerbach_3d_fails_general` by
   adapting the T₀ counterexample to a non-orthocentric specimen. The
   √14 arithmetic is the main obstacle; once a Lean tactic for
   "polynomial-in-√d" comparison is available, this becomes routine.
3. **Optionally promote the refutation to a formal theorem** of the
   form `∃ T : OrthocentricTetrahedron, ¬ spheresInternallyTangent
   T.toTetrahedron.twentyFourPointCenter T.toTetrahedron.incenter
   T.toTetrahedron.twentyFourPointRadius T.toTetrahedron.inradius`.
   Same √14 obstacle.

---

## Session 2026-05-03 (Session 4) — Formula Correction + Two New Theorems

**Mode**: REVISIT (ACT phase, RICH knowledge tier)
**Outcome**: Added 2 provable theorems, corrected 1 false docstring claim.

### Mathematical Finding: R/2 Claim Is False

The previous docstring for `edge_midpoints_equidist_from_centroid` claimed the
common distance from G to edge midpoints is R/2. This is FALSE for the regular
tetrahedron A=(1,1,1), B=(1,-1,-1), C=(-1,1,-1), D=(-1,-1,1):

- G = O = (0,0,0), R = √3, R/2 = √3/2 ≈ 0.866
- midpoint_AB = (1,0,0), dist(G, midpoint_AB) = 1 ≠ √3/2

The CORRECT formula: dist²(G, M_AB) = (|AC|²+|BD|²)/16.

Proof: G - M_AB = (C+D-A-B)/4 = ((C-A)+(D-B))/4. Squaring:
|(C-A)+(D-B)|² = |C-A|² + 2(C-A)·(D-B) + |D-B|²
= |AC|² + 0 + |BD|² (by AC⊥BD condition).

For T₀: (|AC|²+|BD|²)/16 = 49/16 = R²/4 ✓ (R = 7/2)
For regular: (8+8)/16 = 1 ≠ R²/4 = 3/4 ✗

The R/2 formula holds for T₀ but NOT in general. The docstring is now corrected.

### New Theorem: twentyFourPointCenter_is_2G_minus_O

N₂₄ = 2G - O (proved by ring from definitions).

Algebraically: N₂₄ = midpoint(O, 4G-3O) = (O+4G-3O)/2 = 2G-O.

Consequence: for an orthocentric tetrahedron, the orthocenter H = 2G-O coincides
with N₂₄. So `twentyFourPointCenter_is_2G_minus_O` confirms N₂₄ = H for
orthocentric tetrahedra.

### New Theorem: edge_midpoints_dist_sq_formula

dist²(G, M_AB) = (|AC|² + |BD|²)/16 (using AC⊥BD)
dist²(G, M_AC) = (|AB|² + |CD|²)/16 (using AB⊥CD)

Proved by nlinarith using the orthocentric perpendicularity hypotheses.

### Files Modified

- `proofs/Proofs/FeuerbachsTheoremOQ02.lean`:
  - Added `twentyFourPointCenter_is_2G_minus_O` theorem (lines ~548-558)
  - Added `edge_midpoints_dist_sq_formula` theorem (lines ~645-656)
  - Fixed PART 14 block comment (removed false R/2 claim)
  - Fixed `edge_midpoints_equidist_from_centroid` docstring (corrected R/2 reference)
  - Updated PART 15 summary (10 theorems listed, corrections noted)
  - Line count: 688 → 743

### Sorry / Axiom Delta

- Sorries: 0 → 0 (no change)
- Axioms: 1 → 1 (no change)
- Theorems: 8 → 10 (+2)

### Honest Assessment

The two new theorems are algebraic/coordinatewise facts, provable by ring and
nlinarith. They add genuine mathematical content:
1. `twentyFourPointCenter_is_2G_minus_O` crystallizes the geometric identity.
2. `edge_midpoints_dist_sq_formula` provides the exact value (not just equidistance),
   and corrects an error in the prior docstring.

The session does NOT close the remaining axiom `feuerbach_3d_fails_general`. That
axiom requires exhibiting a concrete non-orthocentric tetrahedron, computing face
areas (which involve sqrt), and showing the tangency condition fails. The sqrt in
face areas makes this very hard to formalize without specialized algebraic-number
arithmetic tactics.

### Next Steps

1. **feuerbach_3d_fails_general**: Still an axiom. Possible approach: find a
   non-orthocentric tetrahedron where all face areas are rational (Pythagorean
   condition: a²b²+b²c²+a²c² is a perfect square for the face BCD). This is
   a number-theoretic search problem.
2. **Murakami sphere**: Survey the face-circumcircle-based construction and
   add it to the file's infrastructure.
