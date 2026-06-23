# Literature for feuerbachs-theorem-oq-02-incomplete-01

This directory contains literature pointers, Mathlib infrastructure surveys, and source pointers relevant to the 3D analogue of Feuerbach's theorem for tetrahedra.

## Index

- [`mathlib-twelve-point-sphere-survey.md`](mathlib-twelve-point-sphere-survey.md) — Mathlib `mongePoint` + `ninePointCircle` infrastructure (pinned vs HEAD); closed-form refutation of the Buba-Brzozowa twelve-point sphere `((4G − O)/3, R/3)` as a Feuerbach candidate at T₀. Session S6 (2026-05-13).

## Related Gallery Proofs

- `feuerbachs-theorem` — 2D Feuerbach theorem (incircle tangent to nine-point circle).
- `feuerbachs-theorem-oq-05` — Inversive 2D proof.
- `feuerbachs-theorem-oq-02-murakami` — Successor research slug for the correct 3D sphere (Murakami 1952 / Court 1934); created by PR #17001, currently ORIENT-phase.

## External References

### Twelve-point sphere / Euler sphere of a tetrahedron

- **Buba-Brzozowa**, "The Monge Point and the 3(n+1) Point Sphere of an n-Simplex." [Semantic Scholar PDF](https://pdfs.semanticscholar.org/6f8b/0f623459c76dac2e49255737f8f0f4725d16.pdf). Mathlib's reference for `mongePoint` and `ninePointCircle`.
- **Coolidge, J.L.** (1929), *A Treatise on the Circle and the Sphere*, Oxford University Press, §X.4.

### 3D Feuerbach analogue (open formalization target)

- **Murakami, S.** (1952), "On the n-point sphere of an orthocentric simplex," Memoirs of the College of Science, University of Kyoto.
- **Court, N.A.** (1934), "On the analogue of Feuerbach's theorem," Amer. Math. Monthly 41(8):499–502.
- **Altshiller-Court, N.** (1935), *Modern Pure Solid Geometry*, Macmillan.

### General classical-geometry context

- **Coxeter, H.S.M.** (1969), *Introduction to Geometry*, 2nd ed., Wiley.

## Mathlib pointers (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Mathlib/Geometry/Euclidean/MongePoint.lean` — `Affine.Simplex.mongePoint` (= `2G − O` for n = 3 tetrahedra; matches classical convention, differs from the file's `4G − 3O`).
- `Mathlib/Geometry/Euclidean/Circumcenter.lean` — `circumcenter`, `circumradius`.
- `Mathlib/Geometry/Euclidean/Incenter.lean` — triangle incenter (n-simplex incenter not present; needs local development).
- `Mathlib/Geometry/Euclidean/Triangle.lean`, `MongePoint.lean` `orthocenter` — 2D infrastructure.

## Mathlib HEAD pointers (not yet pinned; tracked for the next bump)

- `Mathlib/Geometry/Euclidean/NinePointCircle.lean` — `Affine.Simplex.ninePointCircle` (generalizes to n-simplex; for n = 3 gives the twelve-point sphere `((4G − O)/3, R/3)`). Author: Weiyi Wang, 2026.
