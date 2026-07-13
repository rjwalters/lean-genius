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

## Session 2026-06-15 (researcher-2) — port dual_law_trig to current main (supersedes conflicting #24344)

**Mode:** ACT (Lean, registered file). Dual blackout (Docker `docker info` timeout;
Aristotle `prove` → "Resource not found", re-probed live). Build-pending.

**Problem found:** the literal OQ deliverable `cos C = −cos A·cos B + sin A·sin B·cos c`
(`dual_law_trig`) is **not on main** — it lives only in PR #24344, which is now
**CONFLICTING/DIRTY** (main added `dual_spherical_law_cleared` after #24344 branched, and
the knowledge/state edits diverged). So the theorem is blocked from merging.

**Fix:** ported #24344's `dual_law_trig` verbatim onto **current** main (inserted after
`dual_spherical_law_cleared`, before the namespace end), on a fresh non-conflicting branch.
It depends only on `dual_law_cleared` (present in main, line ~186) and stable names
(`mul_ne_zero`, `pow_ne_zero`, `mul_right_cancel₀`, `linear_combination`). The proof is the
**division-free cleared-hyp** route (NOT `field_simp` — see
`feedback-avoid-field-simp-under-no-build`): clear the common denominator `sa·sb·sc²` once
via `mul_right_cancel₀ hD`, then `linear_combination (sc^2)*hcC + hAB - cc*hsAsB + key` with
`key := dual_law_cleared …`.

**Re-verified the certificate independently this session** (sympy, exact): both residuals 0 —
`goal − [(sc²)·hcC + hAB − cc·hsAsB + key] ≡ 0` and `hAB − h ≡ 0`. So the proof is
mathematically certified; only the Docker typecheck remains.

File: 0 axioms, 0 sorries, +43 LOC (now ~253). `dual_spherical_law_cleared` and the
primal-trig file (`SphericalLawOfCosinesOQ03Primal.lean`, open PR #24391, MERGEABLE) are
untouched — no collision (different file / different theorems).

**Next:** when this merges, PR #24344 can be closed as superseded; build
`Proofs.SphericalLawOfCosinesOQ03` to confirm typecheck.

## Session 2026-06-15 (researcher-5) — geometric grounding: pure cross-product dual law

**Mode:** ACT, post-SOLVED outward enrichment (the literal OQ deliverable
`dual_law_trig` is already on main, 0 axioms / 0 sorries, line 229). Dual blackout
persists (`docker info` times out; Aristotle 404 in recent sessions). Build-pending.

**What was added (Part VI of `SphericalLawOfCosinesOQ03.lean`):** the file proved the
dual law in *cleared abstract* and *cleared geometric* forms, but the angle normal
forms (`cos A = (ca−cb·cc)/(sb·sc)`, etc.) were only *posited* — `dual_law_trig` takes
them as hypotheses. Part VI grounds them in actual geometry, all `ring`/`rw`-only:

- `cosA_num`/`cosB_num`/`cosC_num`: each angle-cosine **numerator** IS a Binet–Cauchy
  inner product of the two edge normals at that vertex. E.g. at vertex `u`,
  `⟨u×v, u×w⟩ = ⟨u,u⟩⟨v,w⟩ − ⟨u,w⟩⟨v,u⟩ = ca − cb·cc` (the unnormalised cos A).
  Proof: `have h := binet_cauchy u v u w; rw [h, hu, dot_comm u w, dot_comm v u]; ring`.
- `sina_sq`/`sinb_sq`/`sinc_sq`: each side-sine **square** IS a Lagrange
  self-inner-product, `⟨u×v, u×v⟩ = 1 − cc² = sin²c`.
  Proof: `rw [lagrange_identity u v, hu, hv]; ring`.
- `dual_law_cross_product_form`: the capstone — the dual law with EVERY numerator and
  side-sine² replaced by its cross-product realisation:
  `⟨w×u,w×v⟩·⟨u×v,u×v⟩ = −⟨u×v,u×w⟩·⟨v×w,v×u⟩ + [u v w]²·⟨u,v⟩`.
  Proof = rewrite the four cross-product terms via cosC_num/sinc_sq/cosA_num/cosB_num
  to reduce to `dual_spherical_law_cleared`, then `exact`. The whole identity now lives
  in the exterior algebra of the three vertex vectors — no bare side cosines.

**Verification:** `verify_geometric_form.py` (3·10⁵ random unit-vector triangles): all
seven geometric identities (3 numerators, 3 side-sine², 1 triple²=Gram) max err ~1e-15.
Every `rw` chain hand-traced against the exact `dual_spherical_law_cleared` statement
(numerator/denominator orderings match verbatim — see proof comments). No `field_simp`,
no division, no radicals: blackout-safe.

**Reusable Lean note:** `binet_cauchy a b c d` gives the dihedral-angle numerator at a
shared vertex directly; pick `a=c=vertex`. The vertex-angle→edge-normal-inner-product
identity is the clean way to connect a spherical angle to cross products without ever
introducing `arccos`/division/`‖·‖`.

**Next:** Docker-up typecheck of Part VI; optional bridge to parent
`SphericalTriangle.angleC` (would introduce `arccos`/division — defer per
`feedback-avoid-field-simp-under-no-build`).

## Session 2026-06-15 (researcher-3) — POLAR DUALITY in Lean (Part VII): the dual law as a side relation among polar vertices

**Mode:** ACT, post-SOLVED outward enrichment. Dual blackout (Docker `docker info` hangs;
Aristotle 404). Build-pending but EXACTLY certified (sympy, residual 0).

**What was added (Part VII of `SphericalLawOfCosinesOQ03.lean`, +82 LOC, 0 ax / 0 sorry):**
PR #24520 (researcher-1) *documented* the polar-triangle duality and certified it
numerically, but recommended the algebraic Lean route as the build-gated next step. This
session implements exactly that route — no `arccos`/division/`‖·‖`, all `ring`/`rw`/
`linear_combination`:

- `polar_inner_uv/vw/wu`: the (unnormalised) polar vertices `U=v×w, V=w×u, W=u×v` satisfy
  `⟨U,V⟩ = cos a·cos b − cos c = −(cos C numerator)`, cyclically. Each is one
  `binet_cauchy` + `rw [·, h_unit, dot_comm ·]; ring`. This is the `π−C` side/angle swap of
  polar duality at the inner-product level (`cos c' = −cos C`).
- `polar_self_uu/vv/ww`: `⟨U,U⟩ = 1 − cos²a = sin²a` (thin wrappers over `sina_sq` etc.).
- `dual_law_polar_form` (capstone): substituting the above into `dual_spherical_law_cleared`
  gives `−⟨U,V⟩·⟨W,W⟩ = −⟨V,W⟩·⟨W,U⟩ + [u v w]²·⟨u,v⟩` — the dual law of `T` written as a
  side-law-shaped relation among the polar vertices. Proof: `rw` the four polar products to
  side-cosine form, then `linear_combination dual_spherical_law_cleared u v w hu hv hw`.

**Exact certificate** (`verify_polar_form.py`, sympy, no floats): (A) the three polar
inner-product identities are component-wise polynomial identities (binet residual 0 each);
(B) the capstone `linear_combination` residual `(goal_lhs−goal_rhs) − (dscl_lhs−dscl_rhs)`
is identically 0. This upgrades #24520's numeric certification to a symbolic proof of the
exact Lean certificate used.

**Reusable note:** to express a vertex angle's cosine *numerator* as a polar-side cosine,
pick `binet_cauchy P Q R S` with the two cross-product arguments sharing the relevant edge;
`⟨v×w, w×u⟩` collapses (via `⟨w,w⟩=1`) to `cos a·cos b − cos c`. This is the clean
division-free realisation of "the polar side opposite a vertex carries minus that vertex's
angle cosine".

**Next:** Docker-up typecheck of Parts VI–VII; the parent-`angleC` bridge remains the only
deferred item (needs `arccos`/division).

## Session 2026-06-15 (researcher-1) — Registered SphericalLawOfCosinesOQ03Primal (name-checked)

**Mode**: REVISIT (MODERATE; Docker blackout live). **Outcome**: registered the merged-but-unbuilt
primal-completion file after a full bearer name-check.

`Proofs/SphericalLawOfCosinesOQ03Primal.lean` (merged via #24391, 3 theorems, 0 sorry/0 axiom)
closes the parent's headline gap `cos c = cos a·cos b + sin a·sin b·cos C` (the parent stops at the
projection inner product). It was on `main` but **unregistered** in `Proofs.lean` — so its theorems
were inspection-only, never machine-checked. No open PR registers it (#24520 doesn't touch
Proofs.lean; #22850's Proofs.lean edit is unrelated). Added `import Proofs.SphericalLawOfCosinesOQ03Primal`
(alphabetically between `…OQ03` and `…OQ05`).

### Bearer name-check (build-free, before registering — grep-clean ≠ build-safe)
Parent-repo lemmas (SphericalLawOfCosines.lean): `Vec3`(:42), `SphericalTriangle`(:120),
`projectPerp`(:166), `SphericalTriangle.angleC`(:170, a `dite` on `‖projA‖=0 ∨ ‖projB‖=0`),
`norm_projectPerp_eq_sin (u n) (IsUnitVec u) (IsUnitVec n)`(:228, `= Real.sin (arcLength u n)`),
`spherical_law_of_cosines_trig`(:262) — all present, signatures match. `sideA := arcLength t.B t.C`
so `Real.sin t.sideA ≡ Real.sin (arcLength t.B t.C)` definitionally (the `.symm` ascriptions
typecheck). Mathlib bearers vs pinned rev 2df2f01: `abs_real_inner_le_norm`
(InnerProductSpace/Basic.lean:453), `Real.cos_arccos {x} (-1≤x) (x≤1)`
(Trigonometric/Inverse.lean:309) — both present, match usage.

**Residual compile risk (one):** `simp only [SphericalTriangle.angleC]; rw [dif_neg (by push_neg; exact ⟨hA,hB⟩)]`
unfolds a def with `let`-bindings + a `dite`; the rewrite assumes the `let`s are zeta-substituted so
the condition reads `‖projectPerp t.A t.C‖ = 0 ∨ …`. Standard idiom, ~85-90% confident; if it fails
the fix is a `show`/`unfold` adjustment, local to `cos_angleC_eq`. Registration is deployer-build-gated,
so any failure surfaces at the deploy build (revert the one import line), not on local users.

### Next steps
- On deploy/Docker build: confirm green; if `cos_angleC_eq` errors on the dite unfold, replace
  `simp only [angleC]` with `unfold SphericalTriangle.angleC` or a `show` of the dite form.
- Gallery `meta.json` for spherical-law-of-cosines-oq-03 still missing (covers dual law OQ03 + this
  primal completion + #24520's polar duality); defer until #24520 settles to describe all three coherently.

## Session 2026-06-15 (researcher-2) — VERIFIED FLIP (Docker recovered)

**Mode:** ACT, machine-check. Docker is back (`docker info` responds; 88% host mem free).
Ran `LEAN_MEMORY_LIMIT=8192 docker-build.sh Proofs.SphericalLawOfCosinesOQ03` → **green,
7743 jobs, exit 0**. This is the first on-record machine check of the now-424-LOC file
(all of Parts I–VII: V-structure infra, Binet–Cauchy/Lagrange/Gram, `dual_poly`,
`dual_law_cleared`, `dual_spherical_law_cleared`, the literal-trig `dual_law_trig`,
`dual_law_cross_product_form`, and the polar-triangle `dual_law_polar_form`). All the
`linear_combination`/`ring`/`rw` certificates that prior sessions certified only
symbolically (sympy) now typecheck.

**Gallery flip:** `src/data/proofs/spherical-law-of-cosines-oq-03/meta.json` was already
present (the "meta.json missing" note above is stale) at `status: formalized` / `badge: wip`
with a BUILD-PENDING assumptions note. Flipped to `status: verified` / `badge: original`,
0 ax / 0 sorry, and rewrote the assumptions string to record the green build.

**Remaining (unchanged, all optional/outward):** the parent-`angleC` bridge (would introduce
`arccos`/division — deferred per `feedback-avoid-field-simp-under-no-build`); and a confirming
build of the sibling `SphericalLawOfCosinesOQ03Primal.lean` (separate file, separate entry).
The OQ03 deliverable itself is now fully closed and machine-verified.
