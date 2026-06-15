# erdos-1047-oq-02: Characterize which polynomials have all convex lemniscate components

Parent: Erdős #1047 (Grunsky / Erdős–Herzog–Piranian). Solved = NO: not all
components of {z : |f(z)| ≤ c} need be convex, even in the regime where the
sublevel set has exactly m = (#distinct roots) connected components. Counter-
examples: Pommerenke (1961) f = zᵏ(z−a) for large k; Goodman (1966)
f = (z²+1)(z−2)²; a referee's f = z(z⁵−1).

OQ-02 asks for a **characterization** of the polynomials all of whose lemniscate
components are convex (open in full generality).

---

## Session 2026-06-14 (Session 1) — FRESH, ORIENT

**Mode:** FRESH. **Outcome:** progress (durable numerical results + tooling).

### The right tool: boundary signed curvature, not area defect

A prior session (R4, erdos-1047 parent) used a convex-hull **area-defect** grid
metric and got inconclusive results — that metric is blind to sub-grid concavity.
The correct, sensitive test is the **signed curvature of the boundary curve**.

For g(x,y) = |f(x+iy)|² (real, smooth, with ∇g ≠ 0 on the boundary since |f|=c>0
there), the component boundary is the level set {g = c}, and the curvature,
calibrated so that a sublevel *disk* {g ≤ c} has κ > 0, is

    κ = ( gₓ² g_yy − 2 gₓ g_y g_xy + g_y² gₓₓ ) / (gₓ² + g_y²)^{3/2}.

A component K of {g ≤ c} is **convex ⟺ κ ≥ 0 on all of ∂K**. Calibration check:
for g = x²+y² the numerator = 8(x²+y²) > 0 (disk is convex). Verified: the unit
circle gives κ = +1.000 exactly.

Two **independent** implementations were built and cross-validated:
1. grid marching-squares contour + Newton-projection onto {g=c} + analytic κ
   (complex form: gₓ = 2 Re(f̄ f′), g_y = −2 Im(f̄ f′), etc.);
2. grid-free / contour-free **polar trace** r(θ) by 1-D root finding of
   |f(r e^{iθ})| = c, then the exact polar-convexity test r² + 2r′² − r r″ ≥ 0.
Both methods agree on every case tested.

### Key findings

**(A) Low-degree / simple-root polynomials: all components convex up to merge.**
- deg 2 Cassini f = z²−1 (roots ±1): both separate components convex for all
  c < c* = 1 (the merge value); κ_min → 0⁺ as c → c*⁻, never negative.
- deg 3 f = z³−z (three simple roots): all three components convex throughout the
  3-component regime, κ_min → 0⁺ at merge.
⇒ Strong evidence: simple-root configurations of low degree are all-convex.

**(B) The non-convexity is a PRE-MERGE NECKING driven by root multiplicity.**
For Pommerenke f = zᵏ(z−a) the component around the multiplicity-k root at 0
develops a non-convex dimple **on the side facing a** (dimple angle ≈ 0), inside
a c-window (c_nc, c*) just below the merge threshold c*. While in this window the
sublevel set still has m = 2 separate components, so this is a genuine
counterexample to Grunsky in the m-component regime.

The **relative width** W(k) = (c* − c_nc)/c* of the non-convex window grows
monotonically with multiplicity k and is — strikingly — **essentially
independent of the inter-root distance a** (identical to 3 decimals at a=1.0
and a=1.3), so W(k) is an *intrinsic function of the multiplicity*:

| k (mult)      | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 10 |
|---------------|---|---|---|---|---|---|---|----|
| W(k) (a=1.0)  | 0.000% | 0.048% | 0.341% | 0.926% | 1.754% | 2.767% | 5.168% | 7.854% |
| W(k) (a=1.3)  | 0.000% | 0.048% | 0.341% | 0.926% | 1.754% | 2.767% | 5.168% | 7.854% |

- k = 1 (simple root): W = 0 — convex through the entire separated regime up to merge.
- k = 2 (double root): W ≈ 0.05% — only at the instant of merging (matches Goodman, see (C)).
- k = 3, 4: thin sliver (W ≈ 0.3–0.9%) right below c*.
- k ≥ 5–6: a robust window (W ≳ 1.8%; component non-convex at, e.g., 0.97 c*),
  matching Pommerenke's original "large k" statement. Dimple depth also grows
  monotonically: worst κ ≈ −0.7 (k=5), ≈ −1.3 (k=7), ≈ −5.6 (k=10) near merge.

(Window widths W(k) = (c*−c_nc)/c* computed by bisection in `window_width.py`;
c* = max_{0<r<a} rᵏ|r−a| is the on-axis barrier height = merge threshold.)

**(C) The gallery's Goodman example needs scrutiny.**
For f = (z²+1)(z−2)² at the stated c = 5^{3/2}/4 ≈ 2.795, the sensitive curvature
test finds **all three components convex** (κ_min ≈ 1.25 around the double root
z=2, κ_min ≈ 5.2 around ±i). Note 5^{3/2}/4 sits essentially at the component-
merge threshold (components merge to one just above it), and the only multiple
root of Goodman's polynomial is a **double** root (k=2) — exactly the regime where
finding (B) predicts at most a razor-thin necking window. The referee example
f = z(z⁵−1) (all simple roots, deg 6) likewise tests all-convex at the stated c.
⇒ The classical counterexamples are real (Pommerenke, large k), but the gallery's
specific Goodman/referee (f, c) pairs do **not** exhibit a non-convex *separate*
component under a sensitive boundary-curvature test. This corroborates the prior
session's suspicion that those specific values are mis-stated or at-merge. The
clean, reproducible counterexample is Pommerenke zᵏ(z−a) with k ≥ 5.

### Toward the characterization (partial)

Evidence points to: a component around a root of multiplicity k is convex
throughout the separated regime **iff** k is small relative to the geometry; the
mechanism is a dimple facing the nearest other root that sharpens as c → c* and
as k grows. A precise characterization likely combines (i) per-root multiplicity
and (ii) inter-root distances controlling how close c can get to merge while
components stay separate. Simple-root, well-separated configurations are
all-convex; high-multiplicity roots force non-convex necking before merge.

### Files

- `research/problems/erdos-1047-oq-02/verify_lemniscate_curvature.py` — grid+contour curvature test (calibrated, Newton-projected).
- `research/problems/erdos-1047-oq-02/pommerenke_scan.py` — analytic complex-curvature, merge-threshold bisection, Pommerenke sweep.
- `research/problems/erdos-1047-oq-02/onset_refine.py` — full c-scan, dimple location.
- `research/problems/erdos-1047-oq-02/robustness_check.py` — independent grid-free polar-trace cross-check.
- `research/problems/erdos-1047-oq-02/window_width.py` — non-convex window width W(k).

### Next steps

- Derive analytically the leading harmonic of r(θ) near 0 for zᵏ(z−a) and the
  convexity threshold |aₙ|(n²+2) > 1 to predict W(k) (the limaçon b ≤ 1/2 bound
  is the n=1 analogue).
- Audit the gallery's Goodman/referee (f, c): check against Goodman (1966)
  primary source; the gallery may need a corrected c or a switch to a clean
  Pommerenke k ≥ 5 example with a computed κ < 0 (addresses the gallery's own
  open question "make counterexamples explicit with computed convexity violations").
- Lean: convexity of level sets is heavy real analysis; defer. The decidable,
  checkable artifact here is the curvature certificate, not a Lean proof.

---

## Session 2026-06-14 (Session 2) — ANALYTIC, ORIENT

**Mode:** build on Session 1. **Outcome:** progress (closed-form curvature +
log-derivative convexity criterion; corrects the dimple mental picture).

Session 1's convexity test was **numerical only** (real Hessian of g = |f|²).
This session derives a **closed form** and validates it to ~4–6 digits against
the Session-1 Hessian formula on the unit circle, Pommerenke z³(z−1), z⁵(z−1)
(including a κ<0 shoulder), and the Goodman example.

### Result 1 — closed-form lemniscate curvature
For analytic f with f ≠ 0 on {|f| = c}, the boundary signed curvature
(calibrated so a sublevel **disk** has κ > 0) is

    κ = |f'/f| · ( 1 − Re( f f'' / (f')² ) ).

So a component of {|f| ≤ c} is **convex ⟺ Re( f f''/(f')² ) ≤ 1** on its
boundary (where f' ≠ 0). This is one complex evaluation — far lighter than the
2×2 real Hessian of |f|² — and intrinsic (scale-free in f).

### Result 2 — reduction to the logarithmic derivative (root data only)
Let w = f'/f = Σⱼ mⱼ/(z − rⱼ) over the **distinct** roots rⱼ with multiplicities
mⱼ. Since f f''/(f')² = 1 + w'/w²,

    κ = − |w| · Re( w'/w² ),     convex ⟺ Re( w'/w² ) ≤ 0,    w' = −Σⱼ mⱼ/(z−rⱼ)².

The convexity test depends **only on the root locations and multiplicities** —
the natural language for the OQ-02 characterization.

### Result 3 — single distinct root is always convex (base case)
f = (z−r)^m ⟹ w'/w² ≡ −1/m identically ⟹ Re(w'/w²) = −1/m < 0 everywhere ⟹
**every** level set convex (they are the circles |z−r| = c^{1/m}). Recovered from
the criterion; this is the m-roots = 1 base case of the characterization.

### Result 4 — on-axis curvature for Pommerenke z^k(z−a) (corrects the picture)
At the two points where the component around 0 meets the real axis perpendicularly
(r′ = 0), exact implicit differentiation gives
- near nose (θ=0, facing a):  r″ = − a r² / [ (a−r)(k(a−r) − r) ],
- far nose  (θ=π):            r″ =   a r² / [ (r+a)(k(r+a) + r) ],

both validated to 5–6 digits vs finite differences. Both give κ = (r − r″)/r² > 0,
so **both on-axis tips stay CONVEX**. The near (facing-a) tip even **sharpens**:
κ_near → +∞ as r → r_saddle = ka/(k+1) (merge), since k(a−r)−r → 0⁺ (measured
κ_near = 16 → 100 → 189 as c/c* = 0.90 → 0.999). Therefore the Session-1
non-convexity is genuinely **off-axis**: two symmetric concave **shoulders**
flanking the sharp tip facing a (numerically θ ≈ ±0.02–0.03π). This refines —
not contradicts — Session 1's "dimple angle ≈ 0": the shoulders sit just beside,
not at, θ = 0. (So the limaçon-at-θ=π heuristic in Session-1's first next-step is
the wrong local model; the non-convexity is a tip-shoulder effect, not a
back-side dimple.)

### Files (added this session)
- `research/problems/erdos-1047-oq-02/curvature_closed_form.py` — derives &
  numerically certifies Results 1–4 (asserts agreement with the Session-1 real
  Hessian to <1e-3; single-root −1/m to 1e-9; on-axis tips convex for all c).

### Next steps (updated)
- Attack the **two distinct roots** case via Result 2: characterize when
  Re(w'/w²) ≤ 0 holds on the whole component boundary for w = m₁/(z−r₁) +
  m₂/(z−r₂); this is the first nontrivial case of the OQ-02 characterization and
  is now a concrete rational-function inequality, not a numerical scan.
- Audit the gallery's Goodman/referee (f, c) against Goodman (1966) and supply a
  clean Pommerenke k ≥ 5 example with a computed κ < 0 (Result 1/2 give the
  explicit value, e.g. κ = −0.93 at θ = 0.02π for z⁵(z−1) at 0.999 c*).
