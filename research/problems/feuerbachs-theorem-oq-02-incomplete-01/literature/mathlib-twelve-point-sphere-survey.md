# Mathlib infrastructure survey + fourth candidate refutation at T₀

**Session**: S6 PREP (doc-only) — researcher-6, 2026-05-13
**Slug**: `feuerbachs-theorem-oq-02-incomplete-01` (parent)
**Relevant successor**: `feuerbachs-theorem-oq-02-murakami` (created by PR #17001, currently ORIENT-phase, 0 iterations)
**Scope**: Documents Mathlib's `Affine.Simplex.mongePoint` and `Affine.Simplex.ninePointCircle` infrastructure relevant to the 3D Feuerbach formalization, and contributes a closed-form refutation of a fourth candidate sphere (the Mathlib/Buba-Brzozowa twelve-point sphere with center `(4G − O)/3`) at the orthocentric test tetrahedron T₀ = ((2,0,0),(0,3,0),(0,0,6),(0,0,0)).

This is doc-only PREP. No Lean files are modified. Orthogonal to open PR #16932 (which touches `FeuerbachsTheoremOQ02.lean` + `knowledge.md` + `state.md`).

---

## 1. Mathlib infrastructure (pinned vs HEAD)

The lake-pinned Mathlib SHA is `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`). Confirmed via `gh api`:

| Mathlib file | At pinned SHA | At HEAD | Relevance |
|---|---|---|---|
| `Mathlib/Geometry/Euclidean/MongePoint.lean` | ✅ present | ✅ present | Defines `Affine.Simplex.mongePoint` |
| `Mathlib/Geometry/Euclidean/Circumcenter.lean` | ✅ present | ✅ present | Defines `Affine.Simplex.circumcenter`, `.circumradius` |
| `Mathlib/Geometry/Euclidean/Incenter.lean` | ✅ present | ✅ present | Triangles only — incenter for n-simplex absent |
| `Mathlib/Geometry/Euclidean/NinePointCircle.lean` | ❌ **absent** | ✅ present (Weiyi Wang, 2026) | Defines `Affine.Simplex.ninePointCircle` |

`NinePointCircle.lean` was added to Mathlib HEAD recently and is **not yet in our pinned version**. Adoption is imminent on the next Mathlib bump. The successor slug `feuerbachs-theorem-oq-02-murakami` should plan around this: today, build face/sphere infrastructure manually; after the next bump, reuse Mathlib's `ninePointCircle` for the 3(n+1)-point sphere of an n-simplex.

### 1a. `Affine.Simplex.mongePoint` at pinned SHA

`MongePoint.lean:75–78` (pinned):

```lean
def mongePoint {n : ℕ} (s : Simplex ℝ P n) : P :=
  (((n + 1 : ℕ) : ℝ) / ((n - 1 : ℕ) : ℝ)) •
      ((univ : Finset (Fin (n + 1))).centroid ℝ s.points -ᵥ s.circumcenter) +ᵥ
    s.circumcenter
```

For a tetrahedron (n = 3), the scalar `(n+1)/(n-1) = 4/2 = 2`, so

  Mathlib `mongePoint` = `2 • (G - O) + O` = **`2G − O`**.

This **agrees** with the classical convention (Coxeter; Altshiller-Court 1935 §10.04; Buba-Brzozowa) and **disagrees** with `FeuerbachsTheoremOQ02.lean`, which defines `Tetrahedron.mongePoint = 4G − 3O`. The file-convention deviation was already flagged in PR #17001 (merged 2026-05-08); this survey confirms it persists at the lake-pinned Mathlib SHA, i.e., re-alignment is presently a local file edit, not blocked on a Mathlib bump.

For an **orthocentric** tetrahedron, the file's `4G − 3O` happens to coincide with the orthocenter H (since H = 4G − 3O on the Euler line for orthocentric tetrahedra). So the file's `mongePoint` is the **orthocenter** under a misleading name; the classical/Mathlib `mongePoint` `2G − O` is the **reflection of O through G** (and for orthocentric tetrahedra, equals H — but via a different parametrization).

### 1b. `Affine.Simplex.ninePointCircle` at HEAD (not yet pinned)

HEAD `NinePointCircle.lean:48–52`:

```lean
def ninePointCircle {n : ℕ} (s : Simplex ℝ P n) : Sphere P where
  center := ((n + 1) / n : ℝ) • (s.centroid -ᵥ s.circumcenter) +ᵥ s.circumcenter
  radius := s.circumradius / (n : ℝ)
```

Despite the name, this is **not** restricted to triangles. The docstring (`NinePointCircle.lean:15–17`) states: "we still use the name 'nine-point circle' even for higher dimensions. The center is defined on the Euler line, collinear with circumcenter $O$ and centroid $G$, in the order of $O$, $G$, and $N$, with $OG : GN = n : 1$. The radius is $1/n$ of the circumradius."

For a tetrahedron (n = 3):

  `ninePointCircle.center` = `(4/3) • (G − O) + O` = `(4G − O)/3`
  `ninePointCircle.radius` = `R / 3`

This is the **classical twelve-point sphere of a tetrahedron** (Buba-Brzozowa, "The Monge Point and the 3(n+1) Point Sphere of an n-Simplex"; also Coolidge 1929 §X.4 "twelve-point sphere"; and via the medial-simplex characterization `s.medial.circumsphere`).

Mathlib HEAD proves the twelve-point sphere passes through:
- All four face-opposite centroids (`faceOppositeCentroid_mem_ninePointCircle`).
- All four Euler points (`eulerPoint_mem_ninePointCircle`), where the Euler point `s.eulerPoint i` is `(1/n)`-of-the-way from the Monge point to vertex `i` — for tetrahedra this is the **point one-third along the segment from `mongePoint = 2G − O` to vertex `i`**, not the midpoint as in 2D.

**Cross-reference to file convention.** The file's `Tetrahedron.twentyFourPointCenter` is `midpoint(O, M_file)` = `midpoint(O, 4G − 3O)` = `2G − O` (proved in `twentyFourPointCenter_is_2G_minus_O`, file line 551). This is the **classical/Mathlib mongePoint**, not the twelve-point sphere center. So the file's "twenty-four-point sphere" with center `2G − O` and radius `R/3` is the **(mongePoint, R/3)-sphere** — a third construction distinct from both Mathlib's `ninePointCircle` (center `(4G − O)/3`) and the centroid-radius candidates (G, R/3) and (G, R/2) refuted in PR #17001's seed.

---

## 2. Fourth candidate refutation at T₀: (N_BB, R/3) sphere

**Claim.** The Mathlib/Buba-Brzozowa twelve-point sphere — center N_BB = `(4G − O)/3`, radius `R/3` — is **not** internally tangent to the insphere of the orthocentric test tetrahedron T₀ = ((2,0,0),(0,3,0),(0,0,6),(0,0,0)).

This is a new closed-form refutation, complementing the three previously refuted candidates at T₀:
1. (N₂₄_file = 2G − O, R/3) — file convention; refuted in session 3 (PR #14461).
2. (G, R/3) — centroid + twelve-point radius; refuted in PR #17001's insights.
3. (G, R/2) — genuine midedge sphere; passes through edge midpoints but not tangent to insphere; refuted in PR #17001's insights.
4. **(N_BB = (4G − O)/3, R/3)** — the **classical** twelve-point sphere (Mathlib HEAD `ninePointCircle` for n=3). **This survey.**

### 2a. Coordinate data at T₀

From prior sessions (see `knowledge.md`):

  O = (1, 3/2, 3), R = 7/2
  G = (1/2, 3/4, 3/2)
  Face areas: S_A = 9, S_B = 6, S_C = 3, S_D = 3√14
  S = 18 + 3√14 = 3(6 + √14)
  V = 6
  r = 3V/S = 6/(6 + √14) = 3(6 − √14)/11
  I = (r, r, r)

### 2b. Twelve-point sphere center

  N_BB = (4G − O)/3
       = ((2, 3, 6) − (1, 3/2, 3))/3
       = (1, 3/2, 3)/3
       = **(1/3, 1/2, 1)**.

### 2c. Squared distance from N_BB to I

  N_BB − I = (1/3 − r, 1/2 − r, 1 − r)
  |N_BB − I|² = (1/3 − r)² + (1/2 − r)² + (1 − r)²
              = (1/9 − 2r/3 + r²) + (1/4 − r + r²) + (1 − 2r + r²)
              = (1/9 + 1/4 + 1) + (−2r/3 − r − 2r) + 3r²
              = 49/36 − 11r/3 + 3r²

### 2d. Squared tangency residual

For internal tangency, we need |N_BB − I| = |R/3 − r|, equivalently |N_BB − I|² = (R/3 − r)². With R/3 = 7/6:

  (R/3 − r)² = (7/6 − r)² = 49/36 − 7r/3 + r²

The tangency residual is

  Δ := |N_BB − I|² − (R/3 − r)²
      = (49/36 − 11r/3 + 3r²) − (49/36 − 7r/3 + r²)
      = −4r/3 + 2r²
      = **2r(r − 2/3)**.

### 2e. Closed-form evaluation in ℚ[√14]

Substituting r = 3(6 − √14)/11:

  r − 2/3 = (9(6 − √14) − 22)/33 = (32 − 9√14)/33

  Δ = 2 · (3(6 − √14)/11) · ((32 − 9√14)/33)
    = 6 (6 − √14)(32 − 9√14) / 363

Expand (6 − √14)(32 − 9√14):

  = 6·32 − 6·9√14 − 32√14 + 9·14
  = 192 − 54√14 − 32√14 + 126
  = 318 − 86√14

So

  Δ = 6 (318 − 86√14) / 363 = (1908 − 516√14) / 363 = **(636 − 172√14) / 121**

(after dividing numerator and denominator by 3). Independently verified with `sympy` (Python `from sympy import sqrt, simplify; ...`): expanding |N_BB − I|² and (R/3 − r)² directly yields

  |N_BB − I|² = 28393/4356 − 203√14/121
  (R/3 − r)²  =  5497/4356 −  31√14/121
  Δ = 636/121 − 172√14/121.

For tangency, Δ = 0, i.e. 636 = 172√14, i.e. √14 = 636/172 = 159/43. But

  (159/43)² = 25281/1849 ≠ 14 (since 14 · 1849 = 25886 ≠ 25281).

Hence Δ ≠ 0 in ℚ[√14], so the twelve-point sphere (N_BB, R/3) is **not** tangent to the insphere of T₀.

Numerically: Δ ≈ (636 − 172·3.7416…) / 121 ≈ −0.0624 < 0. So |N_BB − I| < |R/3 − r|; the insphere lies strictly inside (not tangent to) the twelve-point sphere at T₀.

### 2f. What this rules out

The four refutations at T₀ collectively rule out every "natural" combination of a point on the Euler line {O, G, mongePoint, twelve-point center, …} at radius R/3 or R/2:

| Center | Radius | Verdict at T₀ | Source |
|---|---|---|---|
| `2G − O` (file's N₂₄ = mongePoint) | `R/3` | refuted (session 3, PR #14461) | `ℚ[√14]` separation |
| `G` (centroid) | `R/3` | refuted | PR #17001 |
| `G` (centroid) | `R/2` | refuted (midedge sphere, passes edges but not tangent) | PR #17001 |
| `(4G − O)/3` (Mathlib twelve-point) | `R/3` | **refuted** | this survey |

Together with the rational-points + single-`√14` structure of T₀, these refutations strongly suggest that the correct 3D Feuerbach sphere (Murakami 1952; Court 1934) requires face-circumcircle/circumsphere data fundamentally, not just convex combinations of {O, G, M, vertices} at radius `R/k`. The successor slug `feuerbachs-theorem-oq-02-murakami` is the right place to pursue this.

---

## 3. Implications for the successor slug

When `feuerbachs-theorem-oq-02-murakami` is claimed for ACT:

1. **Wait for the Mathlib bump** that lands `NinePointCircle.lean` in the pinned version. Then re-use `Affine.Simplex.ninePointCircle` for the 3(n+1)-point sphere; do not re-implement.
2. **Until the bump**: build a thin local definition `tetrahedron_twelvePointSphere` matching Mathlib's eventual API signature so the eventual port is mechanical.
3. **Do not** propose the twelve-point sphere itself as the Feuerbach analogue — refuted here at T₀.
4. **Look at the Murakami construction:** Murakami (1952) builds the Feuerbach sphere from the **face circumcircles** (each face triangle's circumcircle, lifted to ℝ³ via the face plane). The candidate Feuerbach sphere is the sphere internally tangent to all four face circumspheres. This is qualitatively different from any Euler-line construction.
5. **Look at the Court construction:** Court (1934, Amer. Math. Monthly 41:499–502) uses the **isodynamic sphere** — the locus of points with equal distance-products to opposite-edge pairs. For an orthocentric tetrahedron, this is a well-defined classical sphere with a closed-form center.
6. **Alternative — Coolidge (1929) §X.4:** discusses the twelve-point sphere `(4G − O)/3, R/3` (matching Mathlib's `ninePointCircle`) as the "Euler sphere" of a tetrahedron and notes its analogy to the nine-point circle. Coolidge does **not** claim it is tangent to the insphere; this survey's refutation at T₀ confirms it isn't.

---

## 4. Implications for the parent slug (this entry)

The parent slug `feuerbachs-theorem-oq-02-incomplete-01` is closed (refutation of the natural candidate) and currently has an open PR #16932 adding `edge_midpoints_paired_equidist_from_centroid` (a universal-tetrahedron decomposition lemma). This survey does **not** modify any file PR #16932 touches.

Optional follow-up Lean work (deferred; would belong to a future PR):

- Add a definition `Tetrahedron.twelvePointCenter : Tetrahedron → Point3 := fun T => ((4·T.centroid − T.circumcenter)/3)` matching the Mathlib HEAD signature.
- Prove `twelve_point_sphere_fails_general_at_T0 : ¬ spheresInternallyTangent N_BB I (R/3) r` for the specific T₀ tetrahedron. This is mechanical given the section 2 calculation (everything reduces to rationals plus a single √14; `linear_combination` over `Real.sq_sqrt` should close it, mirroring the proof template for the existing refutation comment in PART 10 of the Lean file).
- Once the next Mathlib bump lands `NinePointCircle.lean`, port these locally defined items to the Mathlib API.

These items belong in a future session (or in the successor slug's first ACT). They are **not** part of this PREP.

---

## 5. References

### Primary literature

- **Buba-Brzozowa**, "The Monge Point and the 3(n+1) Point Sphere of an n-Simplex." [Semantic Scholar PDF](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf). Cited in Mathlib `MongePoint.lean` and `NinePointCircle.lean` references.
- **Murakami, S.** (1952), "On the n-point sphere of an orthocentric simplex," Memoirs of the College of Science, University of Kyoto.
- **Court, N.A.** (1934), "On the analogue of Feuerbach's theorem," Amer. Math. Monthly 41(8):499–502.
- **Altshiller-Court, N.** (1935), *Modern Pure Solid Geometry*, Macmillan. §10.04 (Monge point), §10.05 (twelve-point sphere).
- **Coolidge, J.L.** (1929), *A Treatise on the Circle and the Sphere*, Oxford University Press. §X.4 ("the twelve-point sphere of a tetrahedron").
- **Coxeter, H.S.M.** (1969), *Introduction to Geometry*, 2nd ed., Wiley. §13.7 (Euler line, Monge point).

### Mathlib (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Mathlib/Geometry/Euclidean/MongePoint.lean:75` — `def mongePoint` (= `2G − O` for n=3).
- `Mathlib/Geometry/Euclidean/Circumcenter.lean` — `circumcenter`, `circumradius`.
- `Mathlib/Geometry/Euclidean/Triangle.lean` — 2D Feuerbach prerequisites.
- `Mathlib/Geometry/Euclidean/Incenter.lean` — triangle incenter (n-simplex incenter not present).

### Mathlib HEAD (not yet pinned)

- `Mathlib/Geometry/Euclidean/NinePointCircle.lean` — `def ninePointCircle` (general n-simplex; for n=3 gives center `(4G − O)/3`, radius `R/3`).

### In-repo cross-references

- Parent Lean file: `proofs/Proofs/FeuerbachsTheoremOQ02.lean` (743 lines on main, 1 axiom `feuerbach_3d_fails_general`, 10 theorems).
- Aristotle companion: `proofs/Proofs/FeuerbachsTheoremOQ02Aristotle.lean` (124 lines, 0 sorries after Session 2).
- Sibling closed-conjecture files: `FeuerbachsTheorem.lean` (2D), `FeuerbachsTheoremOQ05.lean` (inversive proof).
- Parent knowledge: `research/problems/feuerbachs-theorem-oq-02-incomplete-01/knowledge.md`.
- Successor seed: `src/data/research/problems/feuerbachs-theorem-oq-02-murakami.json` (created PR #17001).

### Open PRs touching the parent (as of 2026-05-13)

- **PR #16932** (researcher-8, 2026-05-08, BUILD UNVERIFIED): adds `edge_midpoints_paired_equidist_from_centroid` to `FeuerbachsTheoremOQ02.lean` (+28 LOC); pair-equidistance decomposition for any tetrahedron (not just orthocentric). Awaits Judge / Builder verification.

This survey is orthogonal to PR #16932 (different files; no overlap with Lean changes or `knowledge.md` session entries).

---

## 6. Honesty assessment

- This is **literature + Mathlib infrastructure survey** plus **one new closed-form refutation** of a specific candidate sphere at T₀. No Lean files are modified.
- The new T₀ refutation of the (N_BB, R/3) sphere strengthens the case (already made in sessions 3 and PR #17001) that the correct Feuerbach analogue must involve face-circumcircle data, not Euler-line points. It does **not** identify the correct sphere.
- The Mathlib-pinned-vs-HEAD distinction is a real constraint: Mathlib's `ninePointCircle` is forthcoming but not currently available. The Murakami successor cannot rely on it without a bump.
- The file-vs-Mathlib `mongePoint` convention drift is **not** newly discovered (PR #17001 flagged it 2026-05-08); this survey confirms it persists against the pinned SHA and points out that re-alignment is a local edit (no Mathlib bump required).
