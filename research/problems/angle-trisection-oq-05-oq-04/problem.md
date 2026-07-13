# Problem: Strengthening Huzita-Hatori to capture curved-crease origami

**Slug**: `angle-trisection-oq-05-oq-04`
**Parent**: `angle-trisection-oq-05` — *Origami (paper folding) can solve cubic
and quartic equations via the Huzita-Hatori axioms.* Verified (0 axioms /
0 sorries / 27 theorems / 695 lines, `proofs/Proofs/AngleTrisectionOQ05.lean`).
**Sibling proofs**:
- `angle-trisection-oq-05-oq-01` — k-fold origami constructibility via
  p-smooth numbers (`AngleTrisectionOQ05OQ01.lean`, 0/0/24/294, completed).
- `angle-trisection-oq-05-oq-02` — omega-fold algebraic completeness
  (`AngleTrisectionOQ05OQ02.lean`).
- `angle-trisection-oq-05-oq-03` — minimum-fold characterization
  (`AngleTrisectionOQ05OQ03.lean`).

## Plain Statement

The seven straight-crease Huzita-Hatori axioms (`HHAxioms` structure in
`AngleTrisectionOQ05.lean:108`) characterise the points constructible by
folds whose crease is a **line segment**. In real-world origami the crease
need not be straight: a single **curved fold** along a smooth planar
curve γ produces two developable strips of paper meeting along γ. The
mathematical theory of curved-crease origami was initiated by D. A.
Huffman (1976), formalised in the smooth setting by Fuchs and
Tabachnikov (1999), and surveyed for the constructibility setting by
Demaine, Demaine, Hart, Price and Tachi (2011).

**The open question** is whether the Huzita-Hatori axiom system can be
*strengthened* — i.e. given a coherent additional axiom or family of
axioms — so that the resulting system captures **exactly** the points
constructible by single curved-crease folds. Equivalently, we ask for an
algebraic / axiomatic characterisation of the **curved-fold-constructible
field** that mirrors the
"`α` is origami-constructible iff `[ℚ(α):ℚ]` divides `2^a · 3^b`"
classification (`AngleTrisectionOQ05.lean:575` `origami_degree_classification`).

## Why this Matters

1. **First differential-geometric extension of Huzita-Hatori.**
   The seven axioms in the parent file all assert existence of an
   *algebraic* crease line satisfying point-and-line incidence
   conditions. Curved-crease origami forces explicit primitives for
   geodesic curvature, fold angle as a function of arclength, and
   compatibility between the two sides of the crease. These primitives
   are absent from the gallery to date and from Mathlib.

2. **Bridge to multi-fold completeness.**
   `AngleTrisectionOQ05OQ01` and `OQ02OQ03` already establish that
   *k-fold simultaneous straight folds* form a strict hierarchy reaching
   algebraic completeness (every positive degree is omega-fold
   constructible). A *single* curved fold is conjecturally at least as
   strong as some finite number of straight folds; quantifying the gap
   between "curved single-fold" and "multi-fold straight" is the natural
   sequel. The OQ-04 axiomatisation provides the language to ask the
   question precisely.

3. **Algebraic-completeness ceiling.**
   It is known (Demaine-Demaine-Hart-Price-Tachi 2011, Section 5) that
   curved-crease origami can *trace* a transcendental curve (e.g. an
   elastica), so the curved-fold-constructible *set of curves* strictly
   contains the algebraic curves. But whether the curved-fold-constructible
   *field of point coordinates* strictly contains the omega-fold straight
   field is **open**; an axiomatic characterisation is the natural tool
   to settle it.

4. **Mathlib gap.**
   Mathlib has the smooth-manifold machinery (`Mathlib.Geometry.Manifold`)
   and curvature for plane curves (`Mathlib.Geometry.Euclidean.Curvature`,
   `Mathlib.Analysis.Calculus.LineDeriv.Basic`) but **no developable
   surface API** and **no folding / crease primitive**. A gallery-side
   formalisation of even the *axiomatic* curved-crease layer (with
   compatibility expressed pointwise on γ) is a candidate to propagate
   upstream as `Mathlib.Geometry.Origami.Curved` once the API stabilises.

## Mathematical Specification

### A.1 Local theory of a curved fold (Fuchs-Tabachnikov 1999)

Let γ : [0,L] → ℝ² be a unit-speed smooth planar curve (the crease in
the unfolded paper). Let θ : [0,L] → (0, π) be the **dihedral fold-angle
profile** — the angle between the two paper half-planes after folding.

The crease γ acquires two extrinsic curvatures after folding:
- κ_g(s) : the **geodesic curvature** in the paper (intrinsic; equals
  the signed planar curvature of γ since the paper is flat).
- κ_n(s) : the **normal curvature**, fully determined by the fold angle
  and the geodesic curvature via the **Fuchs-Tabachnikov identity**:

> **Fold compatibility (Fuchs-Tabachnikov 1999, Theorem 1):**
> `κ_n(s) = κ_g(s) · cot(θ(s) / 2)`

Both ruled developable strips on either side of γ are uniquely
determined by `(γ, θ)` and the compatibility identity. The straight-fold
limit `κ_g ≡ 0` reproduces the H-H axioms (then `κ_n ≡ 0` and the two
sides remain flat planar strips).

### A.2 Constructibility from curved folds

A real number `α ∈ ℝ` is **curved-fold constructible** if there exists
a finite sequence of operations
- mark points and straight lines from the H-H axioms,
- perform a single curved fold along an analytic curve `γ` with fold
  profile `θ`, marking the **endpoints**, **tangent intersections** and
  **rule-line images** as new constructible points,

producing the algebraic point `(α, *)`. The closure under these
operations is a field `K_curved ⊇ K_origami ⊇ ℚ`.

Three structural open questions sit beneath this definition:

| ID | Statement | Status |
|----|-----------|--------|
| OQ-A | Is `K_curved = K_origami` (no algebraic gain)? | Conjectured FALSE (Demaine et al. 2011) |
| OQ-B | Is `K_curved` contained in `K_(omega-fold)` straight (i.e. algebraic)? | Open; folklore YES |
| OQ-C | Does a *finite axiomatisation* (in the H-H style) generate `K_curved`? | The OQ-04 question itself |

### A.3 The axiomatic strengthening (proposal)

The natural extension is to add **one** axiom schema parametrised by a
smooth curve type `Γ` and a fold profile `Θ`:

> **Axiom O8 (Curved Fold):**
> For any analytic unit-speed `γ : [0,L] → ℝ²` and analytic
> `θ : [0,L] → (0,π)` satisfying the Fuchs-Tabachnikov compatibility
> identity `κ_n(s) = κ_g(s) · cot(θ(s)/2)`, there exists a fold whose
> crease is `γ` and whose dihedral profile is `θ`; the rule lines on
> each side and their endpoints on `γ` are constructible points.

Whether this axiom system collapses to a finite Huzita-Hatori-style
list (a fixed set of axioms each parametrised by *finitely many* marked
points) is the precise content of OQ-04.

## Mathlib Infrastructure Map

| Need | Mathlib (pinned 2026-05) | Status |
|------|--------------------------|--------|
| Plane curve `γ : ℝ → ℝ²` smooth | `Mathlib.Analysis.Calculus.ContDiff.Basic` | available |
| Signed planar / geodesic curvature `κ_g(s)` | `Mathlib.Geometry.Euclidean.Curvature.Plane` | partial; only `curvatureOfFunction` for graphs |
| Developable surface / rule line | — | **GAP** (no formalisation) |
| Fold-angle profile θ on a curve | — | **GAP** |
| Fuchs-Tabachnikov identity | — | **GAP** |
| H-H axioms (straight crease) | `AngleTrisectionOQ05.HHAxioms` | gallery-only |
| Origami-constructible field | `AngleTrisectionOQ05.IsOrigamiConstructible` | gallery-only |
| Omega-fold constructibility | `AngleTrisectionOQ05OQ02` | gallery-only |
| Analytic-vs-smooth (Cω vs C∞) | `Mathlib.Analysis.Analytic.Basic` | available, lightly used |

## Reference Reading

| # | Paper / Book | Why |
|---|--------------|-----|
| 1 | Huffman, D. A. (1976). *Curvature and creases: A primer on paper.* IEEE Trans. Comput. C-25(10), 1010-1019. | First mathematical treatment; introduces rule-line / developable framework. |
| 2 | Fuchs, D.; Tabachnikov, S. (1999). *More on paperfolding.* Amer. Math. Monthly 106(1), 27-35. | Smooth differential geometry of a single curved fold; Theorem 1 above. |
| 3 | Demaine, E. D.; Demaine, M. L.; Hart, V.; Price, G. N.; Tachi, T. (2011). *(Non)existence of pleated folds: How paper folds between creases.* Graphs Combin. 27(3), 377-397. | Constructive curved folds; transcendental crease curves. |
| 4 | Tachi, T. (2010). *Origamizing polyhedral surfaces.* IEEE Trans. Vis. Comput. Graph. 16(2), 298-311. | Algorithmic construction; useful for axiom-style discretisation. |
| 5 | Alperin, R. C.; Lang, R. J. (2006). *One-, two-, and multi-fold origami axioms.* 4OSME, 371-393. | Comparison framework for axiom-style origami strength. |
| 6 | Mitani, J. (2009). *A design method for 3D origami based on rotational sweep.* CAD Appl. 6(1), 69-79. | Constructive procedures with algebraic origami curves. |
| 7 | Geretschläger, R. (1995). *Euclidean constructions and the geometry of origami.* Math. Mag. 68, 357-371. | Bridge between H-H and other geometric construction systems. |

## Proposed Decomposition

| Session | Phase | Target |
|---------|-------|--------|
| **S1** (this) | OBSERVE | Survey: literature, primitives, Mathlib gap, axiom-strengthening proposal. Markdown + JSON only. |
| **S2** | ORIENT | Add `CurvedCrease` structure (γ, θ, compatibility hypothesis) to a new file `AngleTrisectionOQ05OQ04.lean`; state the conservativity lemma `straight_fold_recovers_HH`. |
| **S3** | ACT | Prove `straight_fold_recovers_HH`: any curved fold with `κ_g ≡ 0` reduces to a single straight-line fold satisfying one of `HHAxioms` (case analysis on the endpoint incidence; ~120 lines). |
| **S4** | ACT | Prove `curved_fold_implies_origami_or_transcendental` (≤Demaine 2011, Section 5 idea): the **points** on γ at unit-speed parameter values `s ∈ ℚ ∩ [0,L]` lie in `K_curved`; if γ is algebraic of degree ≤ d, those points lie in `K_origami` (~80 lines, requires algebraicity hypothesis on γ). |
| **S5+** | ACT | Tractable target: state OQ-A explicitly as a Lean conjecture `K_curved = K_origami → False` with the elastica witness sketched in Demaine et al. 2011. Sorry-bearing theorem statement to be discharged later. |

The S2 / S3 pair is the minimum tractable formalisation deliverable: it
introduces the curved-fold primitive **and** proves it reduces to H-H in
the straight limit (i.e. the new system is genuinely an extension).
