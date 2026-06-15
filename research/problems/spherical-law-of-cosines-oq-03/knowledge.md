# Knowledge Base: spherical-law-of-cosines-oq-03

## Source
Seeker-selected gallery-extracted open question extending **spherical-law-of-cosines**.

## The question
Formalise the **dual** (angles) spherical law of cosines:

  cos C = − cos A · cos B + sin A · sin B · cos c

the polar dual of the parent's **side** law `cos c = cos a cos b + sin a sin b cos C`.
The minus sign on `cos A cos B` is the signature of spherical duality (the polar
triangle has sides `π − A`, angles `π − a`).

## Progress Summary
PROGRESS (S1, ACT). Wrote `proofs/Proofs/SphericalLawOfCosinesOQ03.lean`: a
self-contained, division-free, radical-free formalisation of the dual law, plus
reusable 3-D cross-product infrastructure (the parent file has none). Build is
PENDING — authored during a Docker + Aristotle dual-backend outage, so not yet
machine-checked; all proofs are `ring` / `rw`+`ring` / `nlinarith` only (no
`field_simp`, no division), and every identity is verified numerically over
3·10⁵ random spherical triangles (`research/scripts/verify-spherical-dual.py`,
all checks ≤ 8·10⁻¹⁴).

## Key mathematical reduction
Encode vectors in ℝ³ as a 3-field structure `V` with `dot`/`cross`. For a triangle
of unit vectors `u,v,w`, side cosines `ca=⟨v,w⟩, cb=⟨w,u⟩, cc=⟨u,v⟩`. The
interior-angle normal forms (verified independently against tangent-projection
angles):

  cos A = (ca − cb·cc)/(sin b·sin c),   sin A = |[u v w]|/(sin b·sin c)

with `[u v w] = ⟨u, v×w⟩` the scalar triple product and `sin a = √(1−ca²)`.
Substituting and multiplying by `sin a·sin b·sin²c` turns the trig dual law into
the pure polynomial identity (`dual_poly`, `ring`):

  (cc − ca·cb)(1 − cc²) = −(ca − cb·cc)(cb − ca·cc) + (1 − ca² − cb² − cc² + 2 ca cb cc)·cc

Hand-expanded and confirmed: both sides equal (cc − ca·cb)(1 − cc²).

## Theorems in the file (all `ring`-class, no division)
- `binet_cauchy`     ⟨a×b,c×d⟩ = ⟨a,c⟩⟨b,d⟩ − ⟨a,d⟩⟨b,c⟩
- `lagrange_identity` ‖a×b‖² = ‖a‖²‖b‖² − ⟨a,b⟩²
- `dot_cross_left/right`  cross ⟂ each factor
- `triple_sq`        [u v w]² = Gram determinant
- `cross_norm_sq_nonneg`, `one_sub_sq_nonneg`  side sines well defined (spherical C–S)
- `dual_poly`        algebraic heart (ring)
- `dual_law_cleared`             abstract cleared dual law
- `dual_spherical_law_cleared`   geometric cleared dual law for unit `u,v,w`

The "cleared" forms multiply the trig identity through by the (positive)
denominators, eliminating sqrt/division side-conditions — a standard, rigorous
formalisation choice (`1 − cc² = sin²c`, `[u v w]² = sin²A·sin²b·sin²c`).

## Mathlib Notes
- Worked over a bespoke `V := {x,y,z}` structure rather than `EuclideanSpace ℝ (Fin 3)`
  (the parent's `Vec3`) to keep every vector identity a transparent component-wise
  `ring` proof; Mathlib's `crossProduct` lives on `Fin 3 → ℝ` and interop with the
  parent's `PiLp` inner product adds friction for no benefit here.
- The parent `SphericalLawOfCosines.lean` proves the side law via an inner-product
  decomposition but introduces NO cross products; this file's Binet–Cauchy / Gram
  lemmas are new reusable infrastructure.

## S2 (register + re-confirm, dual blackout persists)
- **Registered** `import Proofs.SphericalLawOfCosinesOQ03` in `proofs/Proofs.lean`
  (it was an orphan — merged via #24244 but never added to the aggregator). Note
  `build-safe-subset.sh` globs `Proofs/*.lean` directly, so the file was already in
  that build path; registration only fixes the full-aggregate target drift.
- **Re-confirmed numerics**: `verify-spherical-dual.py`, 300 000 random triangles,
  all 9 identities PASS (max err ≤ 6.8·10⁻¹⁴). This includes check (1), the *literal*
  trig form `cos C = −cos A cos B + sin A sin B cos c` with interior angles computed
  independently by tangent projection — so the trig statement (not just the cleared
  surrogate) is numerically validated.
- Aristotle still 404 (`prove` ping → "Resource not found"); `docker info` still
  times out. No machine check possible this session.

## READY DROP-IN: literal trig form (next backend-up session)
The file currently proves only the *cleared* form. The literal trig identity is the
genuine OQ deliverable; it is a pure fraction-clearing corollary of `dual_law_cleared`
and the side-Pythagorean `sc² = 1 − cc²`. Derivation (verified by hand + numerics):

    −cA·cB + sA·sB·cc
      = [ −(ca−cb cc)(cb−ca cc) + tp2·cc ] / (sa sb sc²)        [substitute normal forms]
      = (cc−ca cb)·(1−cc²) / (sa sb sc²)                        [dual_law_cleared]
      = (cc−ca cb)·sc² / (sa sb sc²)                            [sc² = 1−cc²]
      = (cc−ca cb)/(sa sb)  =  cC.                              [cancel sc²]

Ready-to-build statement (abstract, division form, needs `field_simp` so deferred until
a backend can check it):

```lean
theorem dual_law_trig
    (ca cb cc sa sb sc cA cB cC sA sB : ℝ)
    (hsa : sa ≠ 0) (hsb : sb ≠ 0) (hsc : sc ≠ 0)
    (hsc2 : sc ^ 2 = 1 - cc ^ 2)
    (hcA : cA = (ca - cb * cc) / (sb * sc))
    (hcB : cB = (cb - ca * cc) / (sa * sc))
    (hcC : cC = (cc - ca * cb) / (sa * sb))
    (hsAsB : sA * sB = (1 - ca ^ 2 - cb ^ 2 - cc ^ 2 + 2 * ca * cb * cc) / (sa * sb * sc ^ 2)) :
    cC = -cA * cB + sA * sB * cc := by
  subst hcA hcB hcC hsAsB
  rw [hsc2] at *      -- replace sc^2 in the sA*sB denominator
  field_simp
  ring
```
Likely tactic risk: `field_simp` may need `mul_ne_zero`/`pow_ne_zero` side goals discharged
(`field_simp [hsa, hsb, hsc]`); if `ring` doesn't close after clearing, fall back to
`linear_combination (1 - cc^2) * (dual_law_cleared ca cb cc _ _ rfl rfl)` — i.e. feed the
cleared identity explicitly. Numerics (check 1, cosA_nf, sinA_nf) confirm the statement is
true, so this is purely a tactic-bookkeeping task once Docker/Aristotle return.

## S3 (ACT, researcher-4, 2026-06-15) — LITERAL trig dual law added (`dual_law_trig`)

The literal OQ deliverable `cos C = −cos A·cos B + sin A·sin B·cos c` is now a theorem
in the file. **Chose a division-FREE route instead of the `field_simp` drop-in above**,
because the build is still Docker-gated and a guessed `field_simp` proof could silently
fail to compile and break the whole file. The angle cos/sin defining relations are taken
in **cleared product form** (the side law solved for the angle, denominators cleared):
`cA*(sb*sc)=ca−cb*cc`, `cB*(sa*sc)=cb−ca*cc`, `cC*(sa*sb)=cc−ca*cb`,
`sA*sB*(sa*sb*sc²)=tp2`, `sc²=1−cc²`.

Proof skeleton (all `ring`-checkable, no division):
- `hD : sa*sb*sc^2 ≠ 0` (mul_ne_zero + pow_ne_zero);
- `hAB : cA*cB*(sa*sb*sc^2) = (ca-cb cc)(cb-ca cc)` via `rw [hcA, hcB]` on the product
  `(cA*(sb*sc))*(cB*(sa*sc))` then `linear_combination h`;
- `key := dual_law_cleared ca cb cc (sc^2) tp2 hsc2 rfl` (the polynomial heart);
- `apply mul_right_cancel₀ hD` (clear the common denominator once), then
  `linear_combination (sc^2)*hcC + hAB - cc*hsAsB + key`.

Both `linear_combination` coefficients are **sympy-verified** (`goal − combo = 0`,
`hAB − hprod = 0`). Faithful to the OQ: proves the literal equality of the angle cosine
from the cleared normal forms (same philosophy as the file's existing cleared lemmas;
division side-conditions reduce to `sa,sb,sc ≠ 0`). REGISTERED in `Proofs.lean`.
Build-pending (Docker down). 0 axioms / 0 sorries.

## Remaining next steps
1. Build `Proofs.SphericalLawOfCosinesOQ03` once Docker returns; confirm `dual_law_trig`
   compiles (risk: `mul_right_cancel₀` apply-unification + the two sympy-verified
   `linear_combination` coefficients). Fix any `simp only [dot,cross]` projection hiccups
   in the older lemmas (add `dsimp only`).
2. Optionally bridge to the parent's `Vec3`/`SphericalTriangle`/`angleC` so the cleared
   product-form relations are *derived*, not posited.
3. (Lower priority) also provide the literal **division-form** `dual_law_trig` (the
   `field_simp` drop-in above) once a backend can check the `field_simp` tactic.
