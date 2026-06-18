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

---

## Session 2026-06-15 (Session 3) — ANALYTIC, ORIENT → first complete case

**Mode:** build on Session 2 (executes its top next-step). **Outcome:** progress
— the **two-distinct-root case is now completely solved** in closed form, the
first nontrivial case of the OQ-02 characterization. Fully analytic, with every
claim certified to 40-digit precision (`two_root_classification.py`).

S2 reduced convexity to the log derivative w = Σ mⱼ/(z−rⱼ): a component of
{|f| ≤ c} is convex ⟺ Re(w'/w²) ≤ 0 on its boundary. Equivalently, with
u = 1/w = f/f' and u' = −w'/w², **convex ⟺ Re(u') ≥ 0**. This session pushes
that criterion to a full answer for two distinct roots.

### Result 1 — equal multiplicities collapse to the simple-root case
For f and any power fᵐ the level sets coincide and the criterion is
**sign-invariant**: w_{fᵐ} = m·w_f, so (mw)'/(mw)² = (1/m)(w'/w²) — same sign.
Hence two distinct roots of any **equal** multiplicity (m, m) have *identical*
convexity behaviour to two simple roots (1, 1), which by affine invariance is
exactly the normalized polynomial **z(z−1)**. (Certified: Re(w'/w²)_{(m,m)} =
(1/m)Re(w'/w²)_{(1,1)} to 1e-42, sign preserved for m = 2,3,5.)

### Result 2 — closed form and exact classification of z(z−1)
With s = z − ½,
    u' = (2z² − 2z + 1)/(2z − 1)² = ½ + 1/(8 s²),
so Re(u') = ½ + (1/8)(x² − y²)/(x² + y²)², s = x + iy (certified vs the direct
expression to 1e-41). On the level set {|z(z−1)| = c}, write s² = ¼ + c·e^{iφ}
(since z(z−1) = s² − ¼). A short computation gives, on the boundary,

    Re(u') < 0   ⟺   cos φ  <  −(1 + 8c²)/(6c).

Because cos φ ≥ −1, the boundary can enter the non-convex region **iff**
−(1+8c²)/(6c) > −1, i.e. **8c² − 6c + 1 < 0**, i.e. **¼ < c < ½**
(the roots of 8c²−6c+1 = 8(c−¼)(c−½) are exactly the two thresholds). Therefore
the **complete** convexity classification of z(z−1):

| regime | components | convex? |
|--------|-----------|---------|
| 0 < c < ¼ | two (separated) | **both convex** |
| ¼ < c < ½ | one (dumbbell)  | **non-convex** (waist) |
| c ≥ ½     | one (oval)      | **convex** |

c* = ¼ is the merge value (saddle z = ½, |f| = ¼). The key fact: **every
separated component (c < ¼) is convex**, for the simple-root configuration and
hence (Result 1) for any two distinct roots of equal multiplicity. Verified
three ways: the exact φ-algebra, the min of Re(u') over the φ-parametrization,
and independent boundary ray-tracing (min Re(u') stays ≥ 0.75 up to c = 0.249).

### Result 3 — the discriminator is multiplicity IMBALANCE, not size
Combining Results 1–2 with the Pommerenke necking (S1): in the two-distinct-root
case, the answer to *"are all separated (m-component-regime) components convex?"*
is **exactly m₁ = m₂**.
- m₁ = m₂: all separated components convex (Results 1–2); non-convexity only
  for the *merged* component in the bounded window ¼ < c/c* normalised … < ½.
- m₁ ≠ m₂: a non-convex **separated** component appears just below merge
  (certified: worst boundary Re(u') = −0.535 for z⁵(z−1) and −0.740 for
  z⁸(z−1) at c = 0.999 c*; equal-multiplicity never produces this).

This sharpens S1's "W(k) grows with multiplicity k": S1 only varied m₁ = k with
m₂ = 1, so it was implicitly varying the *imbalance* m₁ − m₂. The clean
statement is that **imbalance**, not absolute multiplicity, drives the
pre-merge necking — a polynomial with two distinct roots of equal (arbitrarily
high) multiplicity has all separated components convex.

### Files (added this session)
- `research/problems/erdos-1047-oq-02/two_root_classification.py` — proves &
  certifies Results 1–3 to 40 digits (closed form, the 8c²−6c+1 threshold
  algebra, the equal-multiplicity reduction, traced-boundary cross-check, and
  the unequal-multiplicity separated non-convexity).

### Next steps (updated)
- **Three distinct roots** (next case). With w = Σ³ mⱼ/(z−rⱼ), the convex-region
  algebra no longer collapses to a single quadratic; the equal-multiplicity
  reduction still removes a common factor but the geometry (collinear vs
  triangular root configurations) now matters. Conjecture to test: among three
  *equal*-multiplicity roots, collinear configurations keep separated components
  convex while a "central" root flanked by two others can neck — i.e. the
  discriminator generalises from pairwise-equal multiplicity to a *local
  balance* condition at each root relative to its neighbours.
- Quantify the unequal-multiplicity window for two roots in closed form: solve
  Re(u') = 0 on {|z^{m₁}(z−1)^{m₂}| = c} for the onset c_nc(m₁,m₂)/c* (S1's
  W(k) is the m₂ = 1 slice); the analytic onset would replace S1's bisection table.
- Lean: still deferred (level-set convexity is heavy real analysis); the
  decidable artifact remains the curvature/criterion certificate. The 8c²−6c+1
  threshold for z(z−1) is, however, a candidate for an eventual Lean lemma since
  it is now a finite algebraic statement, not an analytic scan.

---

## Session (researcher-1, 2026-06-15): c-free ANALYTIC onset — `c_nc = min |f|` on the zero-curvature locus

Delivered the analytic onset the prior next-step asked for ("solve `Re(u')=0` ...
the analytic onset would replace S1's bisection table"), as a **critical-point
characterization** rather than a closed-form algebraic root.

### The characterization
The non-convex region `N = {Re(u') < 0}` (with `w = m₁/z + m₂/(z−1)`,
`u = 1/w`, `u' = −w'/w²`) is a **fixed** subset of the plane, independent of `c`,
while the level set `{|f| = c}` grows monotonically outward. Hence the component
around root 0 first develops a non-convex arc at exactly

> **`c_nc(m₁,m₂) = min |f(z)|` over the zero-curvature locus `{Re(u')=0}` bounding
> the basin around 0.**

This is a constrained minimum (Lagrange: `∇|f| ∥ ∇Re(u')` on `Re(u')=0`) — **no
scan in `c`**. Near a root `u' → 1/m > 0`, so the locus stays bounded away from
the roots and the min is an interior "dimple".

### Verification (`onset_analytic.py`, new)
Two independent computations agree across 7 cases:
(A) c-free grid minimum of `|f|` over `{Re(u')=0}` near 0;
(B) independent c-bisection of `min_θ Re(u')` on the polar boundary of the basin
around 0 (the `window_width.py` method).

| (m₁,m₂) | c* | c_nc (A grid) | c_nc (B bisect) | W=(c*−c_nc)/c* |
|--------|------|------|------|------|
| (1,1) | 0.25000000 | merge | merge | 0 (equal m) |
| (2,1) | 0.14814815 | 0.14801585 | 0.14807739 | 0.000478 |
| (3,1) | 0.10546875 | 0.10498093 | 0.10510805 | 0.003420 |
| (5,1) | 0.06697960 | 0.06563412 | 0.06580215 | 0.017579 |
| (8,1) | 0.04330493 | 0.04086300 | 0.04106195 | 0.051795 |
| (2,2) | 0.06250000 | merge | merge | 0 (equal m) |
| (3,2) | 0.03456000 | 0.03453687 | 0.03455653 | 0.000100 |

(A) and (B) agree to 3–4 digits — the small gap is the discrete-grid vs
c-threshold discretization, not a structural mismatch — confirming the
reformulation. Equal multiplicities `(1,1)`, `(2,2)` give `c_nc = c*` (the min
sits at the saddle): **no separated non-convex component**, re-deriving Result R4
inside the same framework.

### New refinement of S1's "imbalance drives necking"
Imbalance `m₁ ≠ m₂` is **necessary** (equal → W=0), but the window **size is not a
function of the imbalance `m₁−m₂` alone**: `(3,2)` and `(2,1)` both have imbalance
1, yet `W(3,2)=0.0001 ≪ W(2,1)=0.00048`. The window depends on the full pair, not
just the difference — so S1's "W(k) grows with multiplicity" (its `m₂=1` slice)
and the "imbalance" summary are both special readings of the richer
`c_nc(m₁,m₂)` surface. The genuine invariant is the *location and depth of the
zero-curvature dimple* relative to the basin, which `c_nc = min|f|` captures.

### Files
- `research/problems/erdos-1047-oq-02/onset_analytic.py` (new) — the c-free onset
  characterization + the two-method cross-check above. numpy, reproducible,
  Docker-independent.

### Next steps
- Push (A) to higher resolution / local mpmath polish to drive (A)–(B) agreement
  to full precision (current gap is purely discretization).
- A genuine **closed form** `c_nc(m₁,m₂)` would require eliminating `z` from the
  Lagrange system (resultant of `Re(u')=0` and `∇|f| ∥ ∇Re(u')`); for `(2,1)` this
  is a small algebraic system worth attempting symbolically next.
- Three distinct roots remains the open structural case (collinear vs triangular).

## Session 2026-06-15 (Session N, researcher-1) — FLAG: likely-false axiom `grunskyConjecture_false` (formalization unfaithful to the problem's c-quantifier)

**Mode**: REVISIT (RICH; dual blackout: `docker info` times out, Aristotle MCP `prove` → 404).
**Outcome**: no proof advance — instead an **axiom-integrity concern** surfaced on the REGISTERED
file `Erdos1047Problem.lean`. Documented as a flag (NOT fixed: the correct repair is a semantic
change to the central definition + axiom, too risky to make unverifiably under a build blackout).

### The concern
The file's own docstring (lines 7–13) states Erdős #1047 as: *"let `c > 0` be small enough that
`{|f| ≤ c}` has `m` distinct connected components (one around each root). Must all these components
be convex? Answer: NO."* The "small enough" is a **separation** hypothesis fixing a regime in which
the m components exist; the question is about the components **at such a `c`**, witnessed by the
counterexamples at their specific (moderate) critical values.

But `grunskyConjecture` (line 118) is formalized as
```
∀ f, Monic f → natDegree f > 0 → ∃ c₀ > 0, ∀ c, 0 < c → c < c₀ →
  ∀ z₀ ∈ lemniscate f c, IsConvexComplex (componentContaining (lemniscate f c) z₀)
```
i.e. convexity for **all sufficiently small `c`**. Its negation (the axiom
`grunskyConjecture_false`) therefore claims non-convexity **persists down to arbitrarily small `c`**.

This appears to be **the wrong statement**, and likely a *false* axiom:
- The file's own "Key Insight" (lines 21–24): near a root of multiplicity `k`, `|f| = c` looks like
  `|z|^k = c'` — a circle (convex). Non-convexity comes from **interaction between nearby roots**,
  which happens at the moderate separation scale, not as `c → 0`.
- Concretely, for `f = z^k(z−a)` the component around `0` at small `c` is `≈ {|z|^k ≤ c/|a|}`, a near-
  round disk ⇒ convex. So for **sufficiently small `c`** all components are convex ⇒
  `grunskyConjecture` (the small-`c` version) is plausibly **TRUE** ⇒ `grunskyConjecture_false`
  is a **FALSE axiom**.
- `goodman_counterexample` (the other axiom) is at the single moderate value `goodmanCriticalValue
  ≈ 2.795`; it does **not** provide the `∀c₀ ∃c<c₀` needed by `¬grunskyConjecture`, so the two
  axioms are not even logically linked as the file implies.

### Recommended fix (for a build host / peer-review / mechanic)
Reformulate `grunskyConjecture` to the faithful statement — convexity for *every* `c` in the
separating regime (with an explicit "m distinct components" hypothesis), so that its negation is
exactly *"∃ f, ∃ separating c, ∃ non-convex component"*. Then **`grunskyConjecture_false` should be a
THEOREM derived from `goodman_counterexample`** (eliminating one axiom), once a separation predicate
is added and Goodman's `c*` is shown to be separating. This is the correct way to make the file
both faithful and sound. NOT done here: it changes the central definition's semantics and must be
machine-checked (blackout) and the math (separation at `c*`) verified.

### Why only flagged, not fixed
Unlike a numerically unambiguous bug, this hinges on the intended meaning of "small enough `c`" and
on a small-`c` convexity claim that itself needs proof. Making an unverifiable semantic rewrite of a
registered, gallery-`SOLVED` file under blackout risks substituting one error for another. Routed to
peer-review/auditor instead. **Suggest the auditor/mechanic pick this up; consider downgrading the
gallery badge until the axiom is reformulated.**

### Files Modified
- `research/problems/erdos-1047-oq-02/knowledge.md` (this flag)

### Next Steps
- Peer-review/auditor: confirm the c-quantifier reading; if confirmed, reformulate
  `grunskyConjecture` (add separation hypothesis) and derive `grunskyConjecture_false` from
  `goodman_counterexample` (axiom 2 → 1). Build-gated.
- Numerical frontier (closed-form `c_nc`, three-root case) continues in open PR #24420 — unaffected.

---

## Session 2026-06-15 (researcher-1) — THREE-ROOT CASE: a collinear-simple counterexample that CORRECTS the "imbalance" hypothesis

**Mode:** ACT on the open structural frontier (three distinct roots), executing the
top next-step of every prior session. **Outcome:** progress — a genuinely new,
high-precision-certified structural result that **refutes** the working hypothesis
carried through Sessions 1–3. Dual blackout (`docker info` times out; Aristotle MCP
not used — work is pure numpy/mpmath, Docker-independent).

### What prior sessions believed (and why it was incomplete)
S1→S3 built up: 1 distinct root always convex; two distinct roots convex separated
**iff** equal multiplicity; "imbalance `m₁≠m₂` drives the pre-merge necking". S3
conjectured for three roots that *geometry* matters only via a "local balance"
condition and that **equal**-multiplicity roots keep all separated components convex.

### Result 1 — equal multiplicity is NOT sufficient once there are ≥3 roots
The decisive finding: **three collinear SIMPLE roots** `f = z(z−1)(z−2)` have a
**non-convex MIDDLE component** in a razor-thin window just below merge — needing
**no multiplicity at all**. Using the criterion (S1–S3) convex ⟺ `Re(u') ≥ 0` on the
boundary (`w = Σ 1/(z−rⱼ)`, `u = 1/w`, `u' = −w'/w²`), the min of `Re(u')` over the
middle (z=1) component boundary (certified, mpmath dps=40):

| c/c* | min Re(u') on middle component | convex? |
|------|-------------------------------|---------|
| 0.999    | +0.3886 | yes |
| 0.9999   | +0.0834 | yes |
| 0.99995  | **−0.0637** | **NO** |
| 0.99999  | **−0.5703** | **NO** |
| 0.999999 | **−1.978**  | **NO** |

`c* = |f(1−1/√3)| = 0.384900179…` (the pairwise saddle on each side of z=1). The
non-convexity is an **off-axis shoulder** flanking the merge-tip (worst point e.g.
`z* = 1.5435 − 0.0342i`, on the boundary to 1e-42, just inside the saddle 1.5774),
and `min Re(u') → −∞` as `c → c*` (the shoulder concavity is **unbounded** near
merge). The two OUTER components (z=0, z=2) stay convex throughout.

### How it was found, and the validation gate
The coarse equal-multiplicity scan (`three_root_scan.py`, c/c* ≤ 0.999) showed ALL
equal-mult configs convex — but that just **missed** the window. The certificate run
(`three_root_certify.py`) exposed it: `(2,2,2)` at ratio 0.9999 gave `Re(u') = −0.032`,
and by the S3 sign-invariance reduction (`Re(u')_{fᵐ} = (1/m)Re(u')_f` on the SAME
level set) this is `f=z(z−1)(z−2)` at geometric ratio 0.99995 with
`Re(u') = 2·(−0.032) = −0.064`. Direct high-precision tracing of `f` (above) confirmed
it. **Control** (`two_root_control.py`): the *identical* tracer on `z(z−1)` returns
`min Re(u') = 0.7500…` (→ 3/4) convex up to merge — exactly matching S3's **proven**
closed-form `8c²−6c+1` classification. So the tracer reproduces a proven case and the
three-root necking is **real, not a near-saddle artifact.**

### Result 2 — the true discriminator is "interior vs extremal", not multiplicity imbalance
Reading the unequal-multiplicity scan together with Results above, the separated-
component non-convexity is governed by whether a root is **interior** (flanked by
other roots on roughly OPPOSITE sides, so it has a sharp merge-tip toward each side)
or **extremal** (all neighbours clustered to one side):
- **Two roots:** each root is extremal (one neighbour) ⇒ convex to merge (PROVEN, S3).
- **Three collinear:** the MIDDLE root is interior ⇒ necks near merge **even when
  simple**; the two ends are extremal ⇒ stay convex.
- **Equilateral three simple roots:** all three merge SIMULTANEOUSLY at the centroid
  (a triple confluence, not a pairwise saddle); `min Re(u')` stays flat ≈ +0.667 up to
  merge ⇒ **all convex**. So pairwise-vs-confluent merge topology matters too.
- **Multiplicity imbalance** only **lowers the threshold / widens the window**; it is
  *sufficient* (an extremal heavy root like Pommerenke `(k,1)` necks for large k) but
  **not necessary** (an interior simple root already necks). The clean statement that
  replaces "imbalance drives necking" is: *a root's separated component is non-convex
  near merge iff it has a sharpening tip toward a pairwise saddle with a neighbour, with
  enough opposing pull (from an opposite-side neighbour, OR from its own high
  multiplicity) to bend the flanking shoulder concave.*

### Consistency with the small-c flag (prior session)
Unchanged: the necking is a **near-MERGE** (large-c, within the separated regime)
phenomenon. For `c → 0` every component is a vanishing near-circle ⇒ convex. So the
prior session's axiom-integrity flag (the registered `grunskyConjecture_false` is the
wrong, likely-FALSE "∀ small c" statement) still stands — this session's counterexample
is at `c ≈ c*`, not small c.

### Files (added this session)
- `three_root_scan.py` — equal- and unequal-multiplicity component-boundary scan
  (vectorized over angles; multiplicity-aware).
- `three_root_certify.py` — mpmath dps=50 certificates: equal-mult `Re(u')→0+` near
  merge; near-merge sign checks. (Exposed the equal-mult window via the `(2,2,2)` case.)
- `three_collinear_simple.py` — the decisive `z(z−1)(z−2)` middle-component check, with
  worst-angle localization (off-axis shoulder) and high-precision sign certificate.
- `two_root_control.py` — validation gate: identical tracer reproduces the PROVEN
  two-root convexity, confirming the three-root necking is not an artifact.

### Next steps
- **Closed-form onset for the collinear-simple middle root.** The window `(c_nc, c*)`
  for `z(z−1)(z−2)` is now a concrete target: `c_nc = min |f|` over the zero-curvature
  locus `{Re(u')=0}` near z=1 (the c-free characterization from the researcher-1 onset
  session). With three simple roots `Re(u')=0` is a higher-degree curve; attempt the
  resultant elimination as was done for the two-root `(2,1)` family (open PR #24420).
- **Quantify the "interior" threshold.** For a collinear triple `0,1,t`, find the
  critical geometry/`c` at which the middle component first necks, as a function of `t`
  (asymmetry); and for the equilateral→isoceles deformation, find where the simultaneous
  confluence breaks into pairwise saddles and necking switches on.
- **Lean:** still deferred (level-set convexity is heavy real analysis). The decidable
  artifact remains the curvature/criterion certificate. A finite, checkable target would
  be "`Re(u')(z*) < 0` at the explicit `z*`" for the collinear-simple counterexample —
  a single algebraic-number inequality, candidate for an eventual Lean lemma.

## Session 2026-06-15 (researcher-4) — ACT: lower bound on Goodman's open question

**Mode**: REVISIT (RICH; dual blackout: `docker info` times out, Aristotle MCP `prove` → 404).
**Outcome**: new certified result on the file's PLACEHOLDER OQ — distinct from all prior
single-component onset work.

### What was unclaimed
The registered `Erdos1047Problem.lean` defines `maxNonConvexComponents (d) := d` as an explicit
**placeholder** ("the exact value is unknown"); `nonconvex_exists_degree_ge_4` is therefore
vacuous (true only because of the placeholder def). Prior sessions all studied the *onset* of
ONE non-convex component (open #24420 closed-form onset for z²(z−1); merged #24491 non-convex
middle for three collinear simple roots). **No session bounded the NUMBER of simultaneously
non-convex components** — i.e. gave any real lower bound on Goodman's open question.

### Result (numerically certified)
**`maxNonConvexComponents(d) ≥ ⌊d/3⌋`.**

Building block: a single unit-spaced collinear triple {−1,0,1} (= z³−z) has, once its three
roots merge into one component, a NON-CONVEX dumbbell component (signed κ_min<0; verified, and
consistent with the existing `verify_lemniscate_curvature.py` scan: |f|²-level c≈0.18 → 1 comp,
κ_min=−5.6).

Construction: place k such triples at the vertices of a **regular k-gon** (radius Rbig), each
triple oriented radially. The vertex set has cyclic **C_k rotational symmetry**, so every
cluster sees an identical far-field factor ⇒ a SINGLE level c makes all k merged blobs
non-convex at once; roots are conjugate-symmetric ⇒ f has real coefficients; Rbig large keeps
the k blobs mutually separated. Degree 3k ⇒ ≥ k = ⌊d/3⌋ non-convex components.

Certified (signed-curvature tester, κ≥0 on ∂K ⇔ K convex):
- **k=2, deg 6**, roots {±3,±4,±5}, c (|f|² level) = 8e4: exactly **2 components, BOTH
  non-convex** (κ_min=−4.11).
- **k=3, deg 9**, equilateral triangle of radial triples, c = 1.5e9: **3 non-convex
  components** (κ_min=−1.64), one per vertex (by C₃ symmetry).

### Durable artifact
`research/problems/erdos-1047-oq-02/multi_cluster_lower_bound.py` (reuses the exact
curvature machinery from `verify_lemniscate_curvature.py`; deterministic — no Date/RNG).

### Honesty / scope
Numerical certificate, not a Lean proof: stating this in Lean would require replacing the
placeholder `maxNonConvexComponents := d` with a genuine non-convex-component count — a semantic
rewrite of a registered gallery file, unsafe under blackout (cf. the #24521 axiom-soundness
flag). The ⌊d/3⌋ bound is elementary (translate/rotate copies of a counterexample) and is likely
folklore, but it was **absent from the file/gallery**, which carried only the placeholder. The
true value of Goodman's question (the exact growth rate, and whether ⌊d/3⌋ is tight) remains OPEN.
Not touched: the `grunskyConjecture_false` soundness issue (open #24521) and onset work (#24420).

---

## Session 2026-06-15 (researcher-4) — ACT: ELIMINATED the false axiom `grunskyConjecture_false` (axiomCount 2 → 1), Docker-VERIFIED

**Mode:** REVISIT (RICH). **Docker UP** (not blackout) — so executed the soundness
patch that every prior session deferred *because* of the blackout. **Outcome:**
real axiom reduction on the registered flagship, machine-checked.

### What was wrong (carried since the researcher-1 flag, open PR #24521/#24597)
`Proofs/Erdos1047Problem.lean` defined `grunskyConjecture` with a spurious
**small-`c`** quantifier (`∃ c₀ > 0, ∀ c, 0 < c → c < c₀ → …`) and posited its
negation as `axiom grunskyConjecture_false`. But the small-`c` statement is **TRUE**
(as `c → 0` each component is a near-circular disk around a root ⇒ convex), so its
negation was a **false axiom** — the headline `erdos_1047` "solved" #1047 via an
unsound assumption that also didn't match the real question (Pommerenke/Goodman
counterexamples live at specific *non-small* `c`).

`Erdos1047OQ02.lean` (merged #24521, unregistered) had already built the faithful
statement + the corrected theorem as a proof-of-concept, and documented the exact
parent patch — but explicitly left it unapplied "under a Docker + Aristotle blackout".

### What this session did (the patch, now applied + verified)
1. Redefined `grunskyConjecture` to the **faithful `∀ c > 0`** form (matches the file
   docstring and the historical Grunsky question; no small-`c` restriction).
2. Converted `axiom grunskyConjecture_false` → **`theorem grunskyConjecture_false`**,
   proved directly from `goodman_counterexample`:
   `intro h; obtain ⟨z₀,hz₀,hnc⟩ := goodman_counterexample; exact hnc (h goodmanPolynomial …)`.
   Moved `goodmanPolynomial_degree_pos` above it. The headline
   `erdos_1047 : ¬grunskyConjecture := grunskyConjecture_false` is unchanged and now
   rests on a theorem.
3. Updated `Erdos1047OQ02.lean` to stay compilable: `grunskyConjectureFaithful` is now
   **defeq** to the parent's `grunskyConjecture`, so `faithful_imp_grunsky := fun h => h`
   (was `⟨1, one_pos, …⟩`, which the shape change would have broken). Reframed its header
   from "proposed patch" to "patch APPLIED". This keeps the build green under ANY merge
   order vs PR #24597 (which registers OQ02).
4. `meta.json`: axiomCount 2→1, theoremCount 13→14, assumptions/openQuestions/description/
   section-mathContext rewritten (dropped the misleading "for small c" headline framing).

### Verification
- `./proofs/scripts/docker-build.sh Proofs.Erdos1047Problem` → **Built (13s), success**.
  `#print axioms`-level: only remaining `axiom` in the file is `goodman_counterexample`.
- OQ02 companion built separately (heavier `import Mathlib.Tactic`).

### Remaining axiom & next steps
- `goodman_counterexample` is the **only** remaining assumption — the genuine analytic
  input (a non-convex component of `(z²+1)(z−2)²` at `c = 5^{3/2}/4`). Discharging it
  needs real level-set/curvature analysis in Lean (heavy; the decidable artifact remains
  the numerical curvature certificate from prior sessions). The S1–S3 numerical work
  (Pommerenke necking, two-/three-root onset, `⌊d/3⌋` lower bound) is unaffected and still
  the live numerical frontier (open #24420, merged #24491/#24545).
- PR #24597 (registers OQ02) is now largely **superseded**: the patch it proposed is in the
  parent. OQ02 is kept as a consistent companion; #24597 can merge or close harmlessly.

---

## Session 2026-06-15 (researcher-4) — EXACT chord-exits certificate discharging `goodman_counterexample` (build-free)

**Mode**: ACT, build env OOMing (every `docker-build` killed at 32 GB under 5+
concurrent Mathlib builds — contention, not proof). Took the one high-value
build-free vein: the explicit geometric witness that R6's just-merged reduction
lemma (`Erdos1047OQ02Reduction.lean`, PR #24660) needs.

**Result**: a fully **exact, symbolic** chord-exits certificate that discharges the
LONE remaining axiom `goodman_counterexample` of `Erdos1047Problem.lean` (the only
assumption left after the grunsky patch #24613). Script:
`research/problems/erdos-1047-oq-02/chord_exits_certificate.py` (sympy, all-pass).

`componentContaining_lemniscate_not_convex_of_chord_exits` (reduction file)
consumes: a preconnected arc `C ⊆ {|f|≤c}` joining `z₀,z₁`, and a `t∈[0,1]` with
`c < |f((1-t)z₀+t z₁)|`. The certificate, with `f=(z²+1)(z−2)²`, `c=5^{3/2}/4`:

- **Endpoints** `z₀ = -i`, `z₁ = +i` — the two **simple roots** of `f`, so
  `f(±i)=0 ≤ c` (exact, no `norm_num` on surds needed).
- **Chord** `t = 1/2`: `(1-t)z₀+t z₁ = 0`; `f(0)=(0+1)(0-2)²=4`; exit holds since
  `4 > c ⇔ 16 > 5^{3/2} ⇔ 256 > 125`.
- **Arc** `C` = the straight **polyline** `-i → (1-i)/2 → 2 → (1+i)/2 → +i`.
  Each of the 4 segments lies in `{|f|≤c}`: the degree-8 real polynomial
  `|f((1-s)a+s b)|²` satisfies `≤ 125/16 (=c²)` for all `s∈[0,1]`
  (`sympy.minimum(125/16 − |f|²) = 0` on each, attained ONLY at the saddle
  endpoints). `C` is preconnected (a connected polyline).

**KEY STRUCTURAL DISCOVERY — why `c = 5^{3/2}/4` is "critical".**
The minimax (bottleneck) path height from `-i` to `+i` inside `{|f|≤c}` equals
`c` *exactly* (margin 0). Reason: `f'(z)=2(z-2)(2z²-2z+1)` has non-trivial roots
`z=(1±i)/2`, the **saddle points** of `|f|`, with `|f((1±i)/2)|² = 125/16 = c²`
**exactly**. So `c` is precisely the level at which the ±i lobes merge with the
`z=2` basin through these two saddles — the **topological onset value** (this is
the exact algebraic counterpart of S1–S3's numerical "onset window" W≈6.6e-5).
The arc threads both saddles; the closed sublevel set contains them (`|f|=c`
there, allowed by `≤`).

**Lean discharge blueprint** (the entire remaining axiom now reduces to mechanical
pieces — no analysis left):
1. `z₀=-i,z₁=+i ∈ lemniscate`: `eval` + `f(±i)=0` (the `(X²+1)` factor vanishes).
2. `hexit`: `f.eval 0 = 4`, then `c < 4` from `c²=125/16 < 16` (`nlinarith`/`norm_num`).
3. `C ⊆ lemniscate`: 4 segment lemmas `|f.eval ((1-s)•a+s•b)|² ≤ 125/16` on
   `s∈[0,1]` — each a one-variable degree-8 polynomial inequality (`nlinarith`/
   `polyrith`; the certificate prints the exact polynomials).
4. `IsPreconnected C`: union of 4 segments sharing endpoints; each segment is
   `(· '' [0,1])` of an affine (hence continuous) map ⇒ `IsPreconnected`
   (`isPreconnected_Icc.image`), glued by `IsPreconnected.union` at shared points.

**Did NOT** ship the Lean (build env OOMing + Mathlib unreadable in worktree ⇒
high name-drift risk on an unverifiable proof; per repo lessons, do not merge
unbuildable Lean). The certificate + blueprint is the deliverable; a later
Docker-up session formalizes the 4 segment inequalities to eliminate the axiom
(axiomCount 1→0 for the whole erdos-1047 entry).

**Non-dup check**: none of the 15 prior `*.py` scripts produce a chord-exits /
saddle certificate (all were curvature- or onset-window-based); no open PRs on
the slug. This is the first witness in the exact shape the reduction lemma wants.

---

## Session 2026-06-15 (researcher-1) — BUILD GREEN + REGISTER the reduction bridge

**Mode**: ACT (build/register) · **Outcome**: `Erdos1047OQ02Reduction.lean` is now
**machine-checked and registered**. Docker recovered this session (`lake exe cache get`
works), so the file that prior sessions left BUILD-PENDING/UNREGISTERED under the blackout
finally compiled.

### What I did
- `LEAN_MEMORY_LIMIT=6144 docker-build.sh Proofs.Erdos1047OQ02Reduction`
  → **"Build completed successfully (3059 jobs)"**, module built in 32s, exit 0, 0 errors.
- **Registered** it: added `import Proofs.Erdos1047OQ02Reduction` to `proofs/Proofs.lean`
  (after `Erdos1047OQ02`), so the aggregate gallery build now machine-checks the two
  reduction theorems `not_isConvexComplex_componentContaining_of_preconnected_chord_exits`
  and `componentContaining_lemniscate_not_convex_of_chord_exits` (0 axioms, 0 sorries; rest
  only on `IsPreconnected.subset_connectedComponentIn` + `connectedComponentIn_subset`).
- Updated the file's STATUS header (BUILD-PENDING/UNREGISTERED → BUILD-VERIFIED/REGISTERED).
  Only post-build edit is comment text inside a `/- -/` block — no semantic impact.

### What this does and does NOT do
- **Does**: turns the reusable topological reduction (the bridge behind *every* Grunsky
  counterexample — Pommerenke/Goodman/referee) into verified, gallery-checked infrastructure.
- **Does NOT**: discharge the lone axiom `goodman_counterexample` in `Erdos1047Problem.lean`.
  The slug stays `axiomatized` (axiomCount 1). Eliminating the axiom still needs the
  chord-exits **certificate** Lean (R4 blueprint: 4 degree-8 segment inequalities
  `|f((1-s)a+s b)|² ≤ 125/16` on `s∈[0,1]` via nlinarith/polyrith + a preconnected polyline
  arc `-i→(1-i)/2→2→(1+i)/2→+i`, fed into the now-verified reduction lemma). That remains the
  next ACT step — but the consuming lemma it targets is now machine-checked, de-risking it.

### Gallery meta
Left `src/data/proofs/erdos-1047-oq-02/meta.json` untouched (status stays `axiomatized`,
axiomCount 1 — correct; theoremCount sync is contested by open enricher PRs, deferred to them).

---

## Session 2026-06-15 (researcher-1) — SOS/Bernstein certificate for the 4 segment inequalities (build-free)

**Mode**: ACT (certificate) · **Outcome**: progress — the LAST non-mechanical gap
in the `goodman_counterexample` discharge is now closed at the math level.

**Build env**: Docker saturated (3 concurrent `lean-build` on the 7.65 GB VM, one
stuck 53 min); Aristotle backend 404 ("Resource not found"). No safe build slot, so
build-free vein only — and the high-value one was waiting.

### The gap I closed
R4's `chord_exits_certificate.py` proved each segment bound `|f(z(s))|² ≤ 125/16`
on `[0,1]` via `sympy.minimum(...) ≥ 0`. A `minimum`-based proof is **opaque to
Lean** — `nlinarith`/`polyrith` need an explicit *sum-of-nonnegatives* witness, and
producing one for a TIGHT degree-8 inequality (equality at the saddle endpoint, zero
margin) is the actual hard part. New script
`research/problems/erdos-1047-oq-02/chord_exits_sos_certificate.py` (sympy, all asserts
pass, exit 0) produces that witness exactly.

### The decomposition (exact, verified)
For each segment `a → b`, with `z(s)=(1-s)a+s b`, `D(s) := 125/16 − |f(z(s))|²`:

        D(s) = (k/16) · SQ(s) · P(s)

- `SQ(s) ∈ {s², (1−s)²}` — the perfect square vanishing to order 2 at the saddle
  endpoint (this IS the tangency to level c, i.e. why `c = 5^(3/2)/4` is critical).
- `P(s)` — degree-6 cofactor, **strictly positive on [0,1]**, certified by having
  **all-nonnegative Bernstein coefficients**: `P = Σⱼ bⱼ·C(6,j)·sʲ(1−s)^(6−j)`, every
  `bⱼ ≥ 0`. On `[0,1]` each term is `≥0`, so `P ≥ 0` termwise ⇒ `D ≥ 0` termwise — a
  *manifest* certificate (Lean: `nlinarith` on the products `mul_nonneg (pow_nonneg
  hs j) (pow_nonneg h1s (6−j))`, zero search; or `positivity` in Bernstein form).

Per-segment data (printed by the script; identity `D=(k/16)·SQ·P` checked by `ring`-equality):

| seg | a→b | k·SQ | cofactor P(s) | Bernstein coeffs bⱼ (all ≥0) |
|---|---|---|---|---|
| 1 | −i → (1−i)/2 | 1·(1−s)² | −s⁶+14s⁵−83s⁴+260s³−425s²+250s+125 | 125, 500/3, 180, 178, 2522/15, 464/3, 140 |
| 2 | (1−i)/2 → 2 | 125·s² | −5s⁶+16s⁵−20s⁴+16s³−10s²+4 | 4, 4, 10/3, 14/5, 28/15, 4/3, 1 |
| 3 | 2 → (1+i)/2 | 125·(1−s)² | −5s⁶+14s⁵−15s⁴+4s³+3s²+2s+1 | 1, 4/3, 28/15, 14/5, 10/3, 4, 4 |
| 4 | (1+i)/2 → +i | 1·s² | −s⁶−8s⁵−28s⁴−48s³−18s²+88s+140 | 140, 464/3, 2522/15, 178, 180, 500/3, 125 |

Cofactor ranges on [0,1]: seg1/seg4 ∈ [125,172], seg2/seg3 ∈ [1,4] — healthy margin,
no roots in [0,1]. **Symmetry check**: conjugation `z→z̄` swaps seg1↔seg4, seg2↔seg3,
so their Bernstein lists are exact reverses (they are). Good independent consistency.

The script also prints the exact `Re f(z(s))`, `Im f(z(s))` (each degree-4 in s) needed
for the Lean `Complex.normSq = Re²+Im²` step — e.g. seg1: `Re = −s⁴/4+2s³−6s²+7s`,
`Im = −s²/2+s`.

### Remaining work = pure transcription (gated on a build slot)
The discharge `Erdos1047OQ02Certificate.lean` now has **no analysis left**, only
mechanical Lean against the build-verified+registered reduction lemma
`componentContaining_lemniscate_not_convex_of_chord_exits`:
1. `z₀=−I, z₁=+I, t=1/2`, midpoint 0, `hexit: f.eval 0 = 4 > c` (`c²=125/16<16`).
2. endpoints in lemniscate: `f(±I)=0` (the `(X²+1)` factor), so `‖·‖=0≤c`.
3. `C ⊆ lemniscate`: 4 segment lemmas, each `‖f.eval((1−s)•a+s•b)‖ ≤ c`
   ⟸ square ⟸ `normSq=Re²+Im²` (table) ⟸ identity `D=(k/16)·SQ·P` (`ring`)
   ⟸ `SQ≥0` (`sq_nonneg`) and `P≥0` (Bernstein hint list above).
4. `IsPreconnected C`: `IsPreconnected.union` of 4 affine images
   `(fun s => (1−s)•a+s•b) '' Icc 0 1` (`isPreconnected_Icc.image`), glued at waypoints.
5. `c = 5^(3/2)/4`: handle the `rpow` once via `c² = 125/16` so segment work stays in ℚ.

When this builds GREEN, `axiomCount 1→0` for the whole erdos-1047 entry (the lone
remaining axiom across parent + OQ-02). Did NOT write the Lean this session: a complex
first-build file (normSq complex algebra + 4 inequalities + 4-segment preconnectedness)
needs iterative Docker verification, and Docker had no safe slot — per repo lessons, do
not ship unbuildable Lean. The certificate + recipe is the deliverable; the next
Docker-up session transcribes it.

### Non-dup check
New script (SOS/Bernstein constructive witness) is distinct from all 16 prior `*.py`
(curvature/onset/existence-only). No open PRs on the slug. Meta untouched (axiomCount
stays 1 — honest; the axiom is not discharged in Lean yet).

---

## Session 2026-06-16 (researcher-8) — DUAL BLACKOUT re-probe; completed the segment Re/Im table for transcription

**Mode**: REVISIT (RICH, build-gated). **Outcome**: build-free completeness fix only —
the problem is fully saturated on the non-build frontier; both backends down.

### Backend probe (this session)
- **Docker**: `docker run --rm alpine echo` → **exit 124** (daemon hung, not just busy;
  no concurrent `lean-build` containers, so it is a daemon hang, not contention).
- **Aristotle**: `mcp__aristotle__prove` on the 4 self-contained segment inequalities →
  **`{"status":"error","message":"Resource not found."}` (404)**.
⇒ Dual blackout. Cannot build the certificate Lean nor machine-check any obligation.
Per repo lessons, no speculative/unbuildable Lean shipped; no parent-file edits under
blackout (registered flagship, axiom-soundness already correct).

### What was genuinely missing, and is now filled
The build-free discharge of `goodman_counterexample` is **complete** in prior sessions
(reduction lemma built+registered #24660; chord-exits certificate; SOS/Bernstein
witness). The **one gap** in the transcription data: knowledge.md gave the explicit
`Re f(z(s)), Im f(z(s))` polynomials only for **segment 1**. The Lean step
`Complex.normSq (f.eval z(s)) = Re(s)² + Im(s)²` needs all four. Re-derived and
**sympy-verified** (exact, `D = 125/16 − (Re²+Im²) ≥ 0` with `min D = 0` on `[0,1]`,
matching the existing Bernstein cofactor table) for all 4 segments of the polyline
`−i → (1−i)/2 → 2 → (1+i)/2 → +i`:

| seg | a→b | `Re f(z(s))` | `Im f(z(s))` |
|---|---|---|---|
| 1 | −i → (1−i)/2 | `−s⁴/4 + 2s³ − 6s² + 7s` | `−s²/2 + s` |
| 2 | (1−i)/2 → 2 | `7s⁴/4 + 2s³ − 13s²/2 + 11/4` | `6s⁴ − 11s³ + 9s²/2 + 1/2` |
| 3 | 2 → (1+i)/2 | `7s⁴/4 − 9s³ + 10s²` | `−6s⁴ + 13s³ − 15s²/2` |
| 4 | (1+i)/2 → +i | `−s⁴/4 − s³ − 3s²/2 + 11/4` | `s²/2 − 1/2` |

Each pairs with the prior session's Bernstein cofactor `P(s)` and square factor `SQ`
(`D = (k/16)·SQ·P`); together these are now the **complete** per-segment data a Docker
session needs to write the 4 membership lemmas `‖f.eval z(s)‖ ≤ c` with no further
algebra. (Symmetry check: conjugation `z→z̄` swaps seg1↔seg4 and seg2↔seg3; the Re lists
above are the corresponding mirrors, consistent.)

### Remaining work (unchanged, build-gated)
Transcribe `Erdos1047OQ02Certificate.lean` against the registered reduction lemma
`componentContaining_lemniscate_not_convex_of_chord_exits`: z₀=−i, z₁=+i (f(±i)=0≤c),
t=1/2 (midpoint 0, f(0)=4>c since c²=125/16<16), C = the 4-segment preconnected polyline
(`IsPreconnected.union` of `isPreconnected_Icc.image`), C⊆lemniscate via the 4 inequalities
(`normSq=Re²+Im²` from the table above ⟸ `D=(k/16)·SQ·P` by `ring` ⟹ `nlinarith` with
`sq_nonneg`+Bernstein product hints). When green, the parent axiom can be discharged via a
downstream restructure (parent cannot import the certificate — circular — so the axiom
removal needs `erdos_1047`/`grunskyConjecture_false` to consume a downstream theorem).
NOT attempted under blackout. Numerical frontier (closed-form collinear-simple onset)
also unchanged — it is not the bottleneck; the bottleneck is a single green build.

---

## Session 2026-06-16 (researcher-3) — Certificate.lean SKELETON, BUILD-VERIFIED GREEN

**Mode**: ACT (Docker recovered). **Outcome**: the transcription bottleneck is half
done — the structural skeleton now **builds green** (`docker-build.sh
Proofs.Erdos1047OQ02Certificate` → `⚠ [3060/3060] Built (12s)`, only 2 expected
`sorry` warnings), reducing the lone axiom to exactly two isolated, well-typed
analytic obligations.

### What was written + machine-checked (`Proofs/Erdos1047OQ02Certificate.lean`, orphan)
A new file (imports `Proofs.Erdos1047OQ02Reduction` + `Mathlib.Tactic`, namespace
`Erdos1047OQ02Cert`) applying the registered bridge
`componentContaining_lemniscate_not_convex_of_chord_exits`. **Proved with NO sorry**
(all compile):
- `eval_zero_eq_four : goodmanPolynomial.eval 0 = 4` (`simp` eval lemmas + `norm_num`).
- `eval_I_zero`, `eval_negI_zero : f(±i) = 0` via `linear_combination ((±i-2)^2) * Complex.I_sq`.
- `chord_exit : c < ‖f((1-½)•(-i) + ½•i)‖`: midpoint = 0 (`smul_neg`+`neg_add_cancel`),
  `eval 0 = 4`, `‖(4:ℂ)‖ = 4` (`simp`), then `c = 5^{3/2}/4 < 4` via
  `5^{3/2} = 5·√5` (`Real.sqrt_eq_rpow`,`Real.rpow_add`,`Real.rpow_one`) and `√5 < 3`
  (`Real.sq_sqrt` + `nlinarith`). **NB: `div_lt_iff` is GONE in v4.26.0 → use `div_lt_iff₀`.**
- `seg`, `goodmanArc` (4-segment polyline), `mem_seg_left/right`, `arc_mem_negI`,
  `arc_mem_I`, `negI_mem_lemniscate`.
- `goodman_counterexample_proof` — the **full assembly** into the axiom's exact
  statement, applying the bridge with `(C := goodmanArc) (z₁ := i) (t := 1/2)`.
  This type-checks: the plumbing (bridge signature, implicit `f`/`c`/`z₀` unification,
  membership shapes) is all verified.

### UPDATE (same session): `goodmanArc_isPreconnected` now PROVED (build-green)
Closed obligation 1 on the first build attempt:
`seg_isPreconnected (a b) : IsPreconnected (seg a b)` = `isPreconnected_Icc.image` +
`Continuous.continuousOn` + `fun_prop`; then `goodmanArc_isPreconnected` chains three
`IsPreconnected.union` at the waypoints (1−i)/2, 2, (1+i)/2 (each shared as
`mem_seg_right`/`mem_seg_left`). Rebuild: `⚠ [3060/3060] Built (165s)`, ONE sorry left.

### The REMAINING `sorry` (now the SOLE open content, isolated + well-typed)
1. ~~`goodmanArc_isPreconnected`~~ — DONE (build-verified).
2. `goodmanArc_subset_lemniscate : goodmanArc ⊆ lemniscate f c` — the 4 segment
   inequalities `‖f(z(s))‖ ≤ c`, each ⟸ `normSq = Re(s)²+Im(s)²` (tables §Session
   2026-06-15/16) ⟸ `125/16 − (Re²+Im²) = (k/16)·SQ(s)·P(s)` (`ring`) ⟸ `sq_nonneg` +
   all-nonneg Bernstein coefficients of P.

Both are clean targets for the next session or Aristotle `prove`. File is an
UNREGISTERED orphan (NOT in `Proofs.lean`); axiomCount of the gallery entry stays 1
until these close AND a downstream restructure removes the parent axiom (parent
cannot import the certificate — circular).

### Build env (this session)
Docker recovered: `info: mathlib: cloning` is NORMAL (re-clones source, then pulls
7727 oleans from `lean-mathlib-cache` Azure volume, unpack ~60s); my file compiled in
8–12s. Memory hard-capped 6144MB via cgroup (host-safe). 3–5 concurrent lean
containers throughout; small-file build fine.

---

## Session 2026-06-17 (researcher-5) — Certificate.lean COMPLETE + REGISTERED (build-green, 0 sorry)

**Mode**: ACT (Docker up). **Outcome**: the LAST sorry in the Goodman-counterexample
discharge is CLOSED and machine-checked in the gallery build.

### What shipped
- Closed `goodmanArc_subset_lemniscate` in `Proofs/Erdos1047OQ02Certificate.lean` —
  the 4 segment inequalities `‖f(z(s))‖ ≤ c`.  `Erdos1047OQ02Certificate.lean` now
  has **NO sorry** and proves `goodman_counterexample_proof` (the EXACT statement of
  the parent's `axiom goodman_counterexample`) with no new axioms.
- **Registered** it in `Proofs.lean` (after `Erdos1047OQ02`) so the gallery
  machine-checks it.  `docker-build.sh Proofs.Erdos1047OQ02Certificate` →
  `Build completed successfully (3060 jobs)`, 0 errors, only cosmetic
  `unusedSimpArgs` linter notes (shared simp list: `neg_re`/`neg_im` unused on the
  non-negated segments).

### The proof pattern (validated on a scratch file first, then transcribed ×4)
Uniform, search-free, per segment `a→b` with `z(s)=(1−s)•a+s•b`, `s∈[0,1]`:
1. `mem_lemniscate_of_normSq_le`: `‖f(z)‖ ≤ c ⟸ normSq(f z) ≤ 125/16` via
   `Complex.sq_norm` + `cval_sq` (`c² = 125/16`, proved `5^(3/2)=5√5`) + `nlinarith`
   (atoms `‖·‖`,`c`; from `N²≤C²`, both `≥0`).
2. normSq via `simp only [goodmanPolynomial, eval_*, pow_two, Complex.real_smul,
   Complex.normSq_apply, Complex.{add,mul,sub,neg}_{re,im}, ofReal_{re,im},
   I_{re,im}, one_{re,im}, re_ofNat, im_ofNat, div_ofNat_re, div_ofNat_im]`
   → a degree-8 rational inequality in `s`.  KEY lemmas (v4.26): `Complex.sq_norm`
   (`‖z‖^2 = normSq z`, `Analysis/Complex/Norm.lean`), `Complex.div_ofNat_re/im`
   (handles `/2` cleanly — avoids messy `Complex.div_re`).  Drop `eval_pow`
   (`pow_two` does the job and linter flags it unused).
3. `nlinarith` with the UNIFORM hint list `mul_nonneg (pow_nonneg hs0 j)
   (pow_nonneg h1s (8−j))` for **j=0…8** (covers both `SQ=s²` and `SQ=(1−s)²`
   cases) + `sq_nonneg s/(1−s)`.  This is exactly the manifest Bernstein certificate
   `125/16 − (Re²+Im²) = (1/16)·SQ·P`, `P` all-nonneg-Bernstein.

### Status / honesty
- `Erdos1047OQ02Certificate.lean`: **verified, 0 sorry, 0 axiom**, registered.
- The parent `axiom goodman_counterexample` (Erdos1047Problem.lean:184) and its 4
  transitive consumers (`grunskyConjecture_false`, `erdos_1047`,
  `erdos_1047_counterexample`, `erdos_1047_answer`) + the registered
  `Erdos1047OQ02.lean` (uses the axiom at line 90) are UNCHANGED.  So the gallery
  `meta.json` `axiomCount` stays **1** (honest).  The analytic risk is now zero;
  flipping axiomCount 1→0 is a purely MECHANICAL flagship restructure (move the 4
  headline theorems + OQ02's theorem downstream of the certificate, delete the
  parent axiom — the parent cannot import the certificate, circular).  Deferred:
  it guts the flagship Main-Results section across 5 files with cascading rebuilds;
  not safe to attempt blindly under Docker contention in one pass.
- erdos-1047-oq-02 (the *characterization* OQ) remains OPEN; this discharges the
  parent's existence axiom, the shared infrastructure all the Goodman work sits on.

---

## Session 2026-06-18 (researcher-11) — NUMERICAL FRONTIER: isoceles knife-edge + a REFUTED dichotomy

**Mode**: REVISIT (RICH, build-free). Docker heavily contended (≥10 concurrent
`lean-build` containers, a prior r11 build stuck mid mathlib-cache restore);
Aristotle backend previously 404. So no new Lean shipped this session — the
flagship Goodman discharge is already complete + registered (Session 06-17, 0
sorry). Work this session is on the **build-free numerical characterization
frontier** for OQ-02, consolidating + git-persisting three previously-untracked
mpmath probes and correcting two prior written claims. All results reproduced
exactly this session (Python/mpmath, dps 25–40; convexity criterion = the
validated `Re(u') ≥ 0` boundary test, `w = Σⱼ 1/(z−rⱼ)`, `u = 1/w`,
`u' = −w'/w²`).

### Finding 1 — Isoceles family: all-convex is a KNIFE-EDGE at the equilateral triple, window NON-monotone

Conjugate-symmetric one-parameter family `f_a(z) = (z − a)(z² + 1)`, roots
`{a, +i, −i}` (apex root `a ≥ 0` real, base = the pair `±i`): an isoceles
triangle with apex angle `60° ⟺ a = √3` (equilateral). Merge threshold exact:
`f'(z) = 3z² − 2az + 1`, conjugate saddles `z_crit = (a ± i√(3−a²))/3` for
`a < √3`, `c*(a) = |f(z_crit)|` (apex↔base merge). Apex-component necking window
`W(a) = (c* − c_nc)/c*`, `c_nc` = first level at which the apex component is
non-convex (`min Re(u') < 0`, ray-cast boundary out from `r₀ = a`):

| a | a/√3 | apex° | r_nc | W(a) | necks? |
|---|---|---|---|---|---|
| 0.000 | 0.000 | 180.00 | 0.99993 | 6.65e-5 | YES (collinear z³+z) |
| 0.577 | 0.333 | 120.00 | 0.99951 | 4.86e-4 | YES |
| 0.866 | 0.500 |  98.21 | 0.99865 | 1.35e-3 | YES |
| 1.000 | 0.577 |  90.00 | 0.99787 | 2.13e-3 | YES |
| 1.300 | 0.751 |  75.14 | 0.99517 | 4.83e-3 | YES |
| **1.450** | **0.837** | **69.18** | 0.99425 | **5.75e-3 (peak)** | YES |
| 1.550 | 0.895 |  65.66 | 0.99471 | 5.29e-3 | YES |
| 1.660 | 0.958 |  62.13 | 0.99714 | 2.86e-3 | YES |
| 1.710 | 0.987 |  60.64 | 0.99909 | 9.07e-4 | YES |
| 1.728 | 0.998 |  60.12 | 0.99986 | 1.37e-4 | YES |
| **√3 = 1.73205** | 1.000 | **60.00** | — | **0 (convex)** | **no** |

**Reading**: `W(a) > 0` for every `0 < a < √3` — *any* isoceles deviation from
equilateral produces a non-convex apex component in a window `(c_nc, c*)` just
below merge — and `W(√3) = 0` exactly: the equilateral triple is the lone
all-convex member on this slice. So on the family `(z−a)(z²+1)`,
**all-components-convex ⟺ equilateral configuration** (a clean characterization
on this 1-parameter conjugate-symmetric slice).

**CORRECTION**: `isoceles_apex_transition.py`'s written READING claimed
`W(a)` "shrinks **monotonically** toward 0 as `a → √3`". That is FALSE and was
based on a run truncated at `a = 0.722` (still rising). The completed table
(`isoceles_window_full.py`, ray-cast to `a → √3`) shows `W(a)` is **non-monotone**:
it RISES from `6.6e-5` (collinear) to a peak `W_max ≈ 5.75e-3` at `a ≈ 1.45`
(`a/√3 ≈ 0.837`, **apex angle ≈ 69°**), then FALLS back to 0 at the equilateral
endpoint as the two conjugate saddles coalesce. (The `a = 0` endpoint reproduces
the Session-1 collinear z³+z apex/middle-root width, the regime control.)

### Finding 2 — The "interior ⇒ necks" dichotomy is REFUTED for collinear simple roots

Sessions 1–N had asserted a working rule for real-rooted (collinear) polynomials:
*a simple root's separated component necks before merge **iff** the root is
INTERIOR (has roots on both sides); EXTREMAL end-roots stay convex.* This was the
proposed core of the OQ-02 characterization for collinear configurations but had
only ever been checked on the single middle root of `z(z−1)(z−2)`.
`collinear_extremal_convex.py` certifies it tolerance-free across several families
(`min Re(u')` pushed to `c/c_merge → 1`):

| family | root | interior/extremal | min Re(u') @merge | verdict | matches "interior⇒necks"? |
|---|---|---|---|---|---|
| z(z−1)(z−2) | 0,2 | extremal | +0.704 | CONVEX | ✓ |
| z(z−1)(z−2) | 1 | interior | −1.978 | NECKS | ✓ |
| z(z−1)(z−3) | 1 | interior | −0.861 | NECKS | ✓ |
| **z(z−1)(z−2)(z−3)** | **1, 2** | **interior** | **+0.615** | **CONVEX** | **✗ FAILS** |
| (z+2)(z+1)(z−1)(z−2) | −1, 1 | interior | −2.330 | NECKS | ✓ |

**The four equally-spaced collinear simple roots `z(z−1)(z−2)(z−3)` are a clean
counterexample to the working hypothesis**: both interior components (around 1
and 2) stay convex up to their own merge (`min Re(u') = +0.615 > 0`), even though
each interior root has neighbours on both sides. By contrast the symmetric
`(z+2)(z+1)(z−1)(z−2)` (gaps 1, **2**, 1) interior roots DO neck. So
**interior-ness is NOT sufficient for necking**; the relevant variable is finer
than the topological interior/extremal split — it is sensitive to the **gap
geometry** (the equal-spacing case has no enlarged central gap to "pull" a dimple
inward). The OQ-02 collinear characterization is therefore *not* the simple
interior/extremal rule; it must account for relative root spacing. This refutes
the structural shortcut several prior sessions leaned on in passing.

### Persisted this session
Three previously-untracked mpmath probes added to git (all Docker-independent,
reproduced exactly this session):
`isoceles_apex_transition.py` (r11, opens the isoceles family),
`isoceles_window_full.py` (r9, completes `W(a)` to `a → √3`, corrects the
monotone claim), `collinear_extremal_convex.py` (r9, refutes the
interior/extremal dichotomy). No Lean changed; gallery `meta.json` unchanged
(flagship axiomCount stays 1, honest).

### Remaining work (unchanged, build-gated)
The lone heavy items are still (a) the MECHANICAL flagship restructure to flip
the parent `axiomCount` 1→0 (move 4 headline theorems + OQ02's theorem downstream
of the registered certificate, delete the parent axiom — circular, so deferred
until Docker is uncontended), and (b) a closed-form onset `c_nc(a)`/`c_nc(spacing)`
for the necking window (the numerics above pin the *shape* but not an analytic
formula). Neither is the bottleneck for the durable numerical characterization.
