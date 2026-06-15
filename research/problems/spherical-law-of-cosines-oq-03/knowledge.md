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

### EXACT symbolic certificate (researcher-1, 2026-06-15 — upgrades "verified by numerics")
`research/problems/spherical-law-of-cosines-oq-03/verify_dual_trig.py` proves the
trig form is a **symbolic** identity (sympy, exact). Over the common denominator
`sa·sb·sc²`, the numerator of `(cC) − (−cA·cB + sAsB·cc)` factors **exactly** as

    numerator  =  (cc − ca·cb) · (sc² + cc² − 1)  =  (cc − ca·cb) · (sc² − (1 − cc²)),

which is identically `0` once `hsc2 : sc² = 1 − cc²`. So the dependence on the
side-Pythagorean identity is a single linear factor. This pins the **exact**
`linear_combination` certificate for the drop-in: after `field_simp [hsa, hsb, hsc]`
clears the denominators, the goal closes with

    linear_combination (cc - ca * cb) * hsc2

(possibly times the denominator-scaling monomial `field_simp` introduces, e.g.
`sa * sb`; if `linear_combination (cc - ca*cb) * hsc2` leaves a nonzero monomial
multiple, multiply the coefficient by that monomial — the residual is always a pure
power of `sa, sb, sc`, never a new polynomial). This replaces the vague
`(1 - cc^2) * dual_law_cleared …` fallback with the precise certificate.

## Remaining next steps
1. Build `Proofs.SphericalLawOfCosinesOQ03` once Docker returns; add the `dual_law_trig`
   drop-in above; fix any `simp only [dot,cross]` projection hiccups (add `dsimp only`).
2. Optionally bridge to the parent's `Vec3`/`SphericalTriangle` and `angleC` so the
   normal-form angle cosines are *derived*, not posited.
