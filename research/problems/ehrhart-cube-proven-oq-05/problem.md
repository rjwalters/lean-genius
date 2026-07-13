# Problem: Derive Pick's theorem from a general Ehrhart polynomial existence theorem

## Statement

### Plain Language

The parent gallery proof `ehrhart-cube-proven` proves the Ehrhart
polynomial of the unit cube $L([0, 1]^d, n) = (n+1)^d$ from first
principles (0 axioms, 0 sorries, 296 lines). The companion
infrastructure file `EhrhartPolynomials.lean` axiomatizes the
general Ehrhart existence theorem and proves a *conditional* Pick's
formula `picks_from_ehrhart` (line 218) that derives Pick's identity
$A = i + b/2 - 1$ FROM the hypothesis that the Ehrhart polynomial
evaluated at $n = 1$ equals $\text{area} + b/2 + 1$.

OQ-05 asks: **can the conditional `picks_from_ehrhart` be upgraded
to an unconditional Pick's theorem via Ehrhart polynomial existence?**
Concretely, the question is whether the four Ehrhart axioms in
`EhrhartPolynomials.lean` — (a) `ehrhart_theorem` (existence of the
Ehrhart polynomial), (b) `ehrhart_leading_coeff_volume` (leading
coefficient is the volume), (c) Ehrhart constant term identity
(`ehrhart_constant_term` already verified, no axiom), (d)
`ehrhart_macdonald_reciprocity` — can be specialized to lattice
polygons (d = 2) to derive the linear-term coefficient identity
"$L_P(n) = A n^2 + (b/2) n + 1$" for ALL lattice polygons, and then
substituted into `picks_from_ehrhart` to discharge the standalone
`picks_theorem` axiom in `PicksTheorem.lean`.

### Three Sub-questions

The OQ-05 question decomposes into three interlocking sub-questions:

1. **Q1 (Linear-term coefficient identity, d = 2 specialization):**
   for every lattice polygon $P$ with area $A$, interior count $i$,
   boundary count $b$, prove the linear coefficient of $L_P(n) =
   A n^2 + c_1 n + 1$ equals $b/2$. Mathematically follows from
   Ehrhart-Macdonald reciprocity at $n = -1$ combined with the
   interior count identity. **This is the technical heart of OQ-05.**

2. **Q2 (Discharge `picks_theorem` axiom):** combine Q1 with
   `picks_from_ehrhart` (already proven, line 218 of
   `EhrhartPolynomials.lean`) to prove `picks_theorem` from
   `PicksTheorem.lean` as a theorem rather than an axiom. The
   technical bridge is connecting the `SimpleLatticePolygon`
   structure (from `PicksTheorem.lean`) to the `LatticePolygon`
   structure (from `EhrhartPolynomials.lean`); they have parallel
   but non-identical signatures.

3. **Q3 (Discharge `ehrhart_theorem` + `ehrhart_leading_coeff_volume`
   + `ehrhart_macdonald_reciprocity` axioms):** the full unconditional
   answer requires proving the three remaining Ehrhart axioms in
   `EhrhartPolynomials.lean` themselves. Each is a major undertaking
   (~500-1500 Lean lines).

The minimum-viable formalization target is **Q1+Q2 ASSUMING the
three Ehrhart axioms remain** — this is the question literally asked
("derived from a general Ehrhart polynomial existence theorem,"
where the existence theorem itself remains axiomatic but Pick's
identity is then a theorem). The unconditional answer (Q3) is a
long-term Mathlib contribution.

### Formal Statement (target form, Q1)

The technical heart: for a lattice polygon $P$, the Ehrhart polynomial
$L_P : \mathbb{Q} \to \mathbb{Q}$ satisfies the explicit form $A n^2
+ (b/2) n + 1$.

```lean
import Proofs.EhrhartPolynomials

namespace EhrhartCubeProvenOQ05

/-- The Ehrhart polynomial of a 2D lattice polygon, expanded form. -/
theorem ehrhartPoly_2d_explicit (P : EhrhartPolynomials.LatticePolygon) :
    ∀ n : ℚ, P.ehrhartPoly.eval n =
      P.area * n ^ 2 + (P.boundaryPoints : ℚ) / 2 * n + 1 := by
  sorry

end EhrhartCubeProvenOQ05
```

The bridge to `PicksTheorem`:

```lean
/-- Pick's theorem (unconditional, derived from Ehrhart polynomial
existence applied to 2D lattice polygons). -/
theorem picks_theorem_from_ehrhart
    (P : PicksTheorem.SimpleLatticePolygon)
    (hP : ∃ Q : EhrhartPolynomials.LatticePolygon,
      Q.area = P.area ∧
      Q.boundaryPoints = P.boundary_count ∧
      Q.interiorPoints = P.interior_count) :
    P.area = P.interior_count + P.boundary_count / 2 - 1 := by
  obtain ⟨Q, h_area, h_bound, h_int⟩ := hP
  -- combine ehrhartPoly_2d_explicit + picks_from_ehrhart
  sorry
```

The hypothesis `hP` is a *bridge axiom* identifying the two parallel
polygon structures. Discharging `hP` itself requires showing that
every `SimpleLatticePolygon` arises as a `LatticePolygon` — a
non-trivial geometric construction (the `LatticePolygon` carries an
ambient `LatticePolytope 2` structure with explicit lattice point
count function, while `SimpleLatticePolygon` is just the discrete
triple).

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - combinatorics
  - ehrhart-theory
  - polytopes
  - lattice-points
  - pick-theorem
  - cardinality
  - wiedijk-92
```

**Significance**: 6/10 — moderate-high. Discharging the standalone
Pick's theorem axiom is a clean axiom-count reduction in the
gallery, AND the bridge construction Q2 establishes the first
gallery-internal cross-reference between two axiomatized proofs
(picks-theorem + ehrhart-polynomials), demonstrating that the
gallery's axioms are internally coherent. Pick's theorem is
Wiedijk #92.

**Tractability**: 5/10 — moderate. Q1 is the technical heart and
hinges on a clean algebraic derivation from Ehrhart-Macdonald
reciprocity at $n = -1$ (the polynomial evaluation). The reciprocity
axiom is available in `EhrhartPolynomials.lean`. Q2 requires the
bridge construction between `SimpleLatticePolygon` and
`LatticePolygon`. Q3 (discharging the three Ehrhart axioms) is OUT
OF SCOPE for an S2-S5 deliverable.

## Three Routes

### R1 — Conditional Pick's theorem via Ehrhart (recommended for S2-S5)

Reduce `picks_theorem` to the three already-axiomatized Ehrhart
identities. Pipeline:

1. **Setup** (S2, ~50 lines): create
   `proofs/Proofs/EhrhartCubeProvenOQ05.lean` with imports of
   `Proofs.EhrhartPolynomials` and `Proofs.PicksTheorem`.
2. **Q1 derivation** (S3, ~200 lines): prove
   `ehrhartPoly_2d_explicit` for any `LatticePolygon`. Strategy: use
   `ehrhart_macdonald_reciprocity` at $n = -1$ (giving $L_{P^\circ}(1)
   = i = (-1)^2 L_P(-1) = L_P(-1)$) to extract the linear-term
   coefficient. The constant term and leading coefficient are
   already pinned (= 1 and = area). Three coefficients + three data
   points (values at $n = -1, 0, 1$) determines the polynomial
   uniquely.
3. **Q2 bridge** (S4, ~150 lines): construct
   `picks_theorem_from_ehrhart` connecting the two polygon types.
   Either via the bridge-axiom approach above OR via a direct
   construction `simpleLatticePolygon_to_latticePolygon` that
   produces a `LatticePolygon` for any
   `SimpleLatticePolygon` by axiomatizing the lattice-point count
   function (one new axiom OR a reduction to the existing
   `ehrhart_theorem` axiom).
4. **Q2 close** (S5, ~100 lines): use Q1 + Q2 + `picks_from_ehrhart`
   to derive `picks_theorem` as a theorem. This may leave
   `picks_theorem` in `PicksTheorem.lean` itself unchanged (since
   that file declares it `axiom`) — the new theorem lives in
   `EhrhartCubeProvenOQ05.lean` and is named `picks_theorem_derived`,
   showing the axiom is *not necessary* given Ehrhart.

Total: ~500 Lean lines. 0 sorries in the deliverable theorems; 3
inherited axioms from `EhrhartPolynomials.lean` (`ehrhart_theorem`,
`ehrhart_leading_coeff_volume`, `ehrhart_macdonald_reciprocity`).
The PR title and gallery entry should be honest: "Pick's theorem
*conditional on Ehrhart polynomial existence*."

### R2 — Unconditional Pick's theorem (long-term, ~3000+ lines)

Discharge the three Ehrhart axioms in `EhrhartPolynomials.lean`
themselves. Each requires substantial Mathlib infrastructure:

| Ehrhart axiom | Estimated effort | Approach |
|---------------|-----|----|
| `ehrhart_theorem` (existence) | ~1500 lines | Stanley's generating function proof: $\sum_{n \ge 0} L_P(n) t^n = h^*(t)/(1-t)^{d+1}$ |
| `ehrhart_leading_coeff_volume` | ~800 lines | $L_P(n)/n^d \to \operatorname{vol}(P)$ as $n \to \infty$ (Riemann-sum argument) |
| `ehrhart_macdonald_reciprocity` | ~1000 lines | Brion's polytope decomposition + half-open shellings |

Each Mathlib contribution is ~3-6 months of formalization effort.
R2 is therefore the strategic horizon, not a single-session goal.

### R3 — Direct triangulation proof of Pick's theorem (~1000 lines)

The classical proof of Pick's theorem doesn't require Ehrhart at all:
triangulate the polygon into unit lattice triangles, verify Pick's
formula for the unit right triangle ($A = 1/2, i = 0, b = 3$), and
prove additivity under polygon gluing. Mathlib lacks the polygon
triangulation infrastructure but has `Convex.SimplexCategory`-style
abstract simplicial complex machinery. This is `picks-theorem-oq-01`
("Can the picks_theorem axiom be proved constructively via
triangulation?") — a SEPARATE OQ family. R3 is mentioned for
completeness but is orthogonal to OQ-05 (which specifically asks
for the Ehrhart-derivation angle).

## Mathlib Infrastructure Map

### What exists (Mathlib v4.26.0 + gallery)

- **`Proofs.EhrhartPolynomials`**: contains `LatticePolytope d` (line ~70),
  `ehrhartCount` (line 91), `ehrhart_theorem` axiom (line 108),
  `ehrhart_leading_coeff_volume` axiom (line 141),
  `ehrhart_macdonald_reciprocity` axiom (line 178), `LatticePolygon`
  structure (line 200), `picks_ehrhart` definition (line 213),
  **`picks_from_ehrhart` theorem (line 218, ALREADY PROVED)**,
  `ehrhart_2d_at_zero` / `ehrhart_2d_at_one` (lines 224, 230).
- **`Proofs.PicksTheorem`**: contains `SimpleLatticePolygon`
  structure (line 102), `picks_theorem` axiom (line 148),
  `picks_theorem_explicit` (line 152, derived from axiom),
  `interior_from_area_boundary` (line 156).
- **`Proofs.EhrhartCubeProven`**: 296 lines, 0 axioms, 0 sorries —
  proves $L([0,1]^d, n) = (n+1)^d$ from first principles. Verified
  status.
- **`Proofs.EhrhartCrossPolytope`, `EhrhartSimplexProven`**: sibling
  axiom-free proofs of Ehrhart polynomials for cross-polytopes and
  simplices. Demonstrates Ehrhart is provable axiom-free on specific
  polytope families.
- **Mathlib**: `Polynomial`, `Polynomial.eval`, `Polynomial.degree`,
  `Polynomial.coeff`, plus the entire algebraic machinery. No
  dedicated Ehrhart theory in Mathlib at v4.26.0.

### What is MISSING for OQ-05 (R1 scope)

- **The bridge function `simpleLatticePolygon_to_latticePolygon`**:
  no existing function maps `SimpleLatticePolygon` to
  `LatticePolygon`. The two structures have parallel but distinct
  signatures — `LatticePolygon` extends `LatticePolytope 2` (with a
  lattice point count function) while `SimpleLatticePolygon` is a
  bare data structure. Constructing the bridge requires either
  (a) instantiating `LatticePolytope 2` for a polygon, which itself
  needs a lattice point count function, OR (b) introducing a fresh
  bridge axiom asserting their equivalence.
- **An algebraic-extraction lemma** showing that a polynomial of
  known degree, leading coefficient, and constant term, plus one
  Macdonald-reciprocity evaluation, uniquely determines the linear
  coefficient. Mathlib has `Polynomial.degree_eq` and `Polynomial.eval`
  but no direct interpolation lemma. Q1 may need ~50 lines of
  custom algebraic manipulation.

### What is MISSING for OQ-05 (R2 scope, deferred)

- **`ehrhart_theorem` proof**: would require a formal definition of
  "Ehrhart polynomial" as a polynomial-of-degree-$d$ such that
  evaluating at any $n \in \mathbb{N}$ gives the lattice point count.
  Stanley's generating function proof + uniqueness from polynomial
  identity on $\mathbb{N}$.
- **`ehrhart_leading_coeff_volume` proof**: Riemann-sum
  $L_P(n)/n^d \to \operatorname{vol}(P)$ argument; needs a measure-theoretic
  characterization of polytope volume, which Mathlib has for
  general convex bodies but not specifically for lattice polytopes.
- **`ehrhart_macdonald_reciprocity` proof**: Brion's half-open
  decomposition or Stanley's $h^*$-vector positivity argument.

## Known Results (literature)

### Proven

- **Pick (1899)**: $A = i + b/2 - 1$ for any simple lattice polygon
  (Sitzungsber. Lotos, Prag). Original proof via triangulation
  argument.
- **Ehrhart (1962)**: $L_P(n)$ is a polynomial of degree $d$ in $n$
  for any $d$-dimensional lattice polytope (C. R. Acad. Sci. Paris).
- **Macdonald (1971)**: $L_{P^\circ}(n) = (-1)^d L_P(-n)$ (Ehrhart-Macdonald
  reciprocity, Proc. London Math. Soc.).
- **Stanley (1980)**: $\sum_{n \ge 0} L_P(n) t^n$ is a rational
  function with numerator the $h^*$-vector polynomial and
  denominator $(1 - t)^{d+1}$.
- **Gallery: `EhrhartCubeProven.lean`** (Lean Genius, verified):
  $L([0,1]^d, n) = (n+1)^d$.
- **Gallery: `EhrhartCrossPolytope.lean`, `EhrhartSimplexProven.lean`**:
  axiom-free Ehrhart polynomials for crosses and simplices.
- **Gallery: `EhrhartPolynomials.lean`** line 218 `picks_from_ehrhart`
  theorem: assuming $L_P(1) = A + b/2 + 1$, Pick's formula follows.

### Open (Lean formalization)

- **Q1 of OQ-05** (this OBSERVE): the unconditional linear-term
  coefficient identity for 2D lattice polygons.
- **Q3 of OQ-05** (R2 scope): the three Ehrhart axioms in
  `EhrhartPolynomials.lean`.
- **`picks-theorem-oq-01`** (separate OQ family): constructive
  triangulation proof of Pick's theorem.
- **Mathlib has no Ehrhart theory at v4.26.0**.

## Path Decomposition (proposed for R1)

| Stage | Deliverable | Lines (est.) | Future Status |
|-------|-------------|-------------|----------------|
| S1 | This OBSERVE survey (text-only) | — | doc-only |
| S2 | `Proofs/EhrhartCubeProvenOQ05.lean` — imports + Q1 stub + Q2 stub | ~80 | `formalized` (2 sorries) |
| S3 | Q1: `ehrhartPoly_2d_explicit` | ~200 | reduces to 1 sorry |
| S4 | Q2: bridge construction `simpleLatticePolygon_to_latticePolygon` | ~150 | reduces to 0 sorries |
| S5 | Q2 close: `picks_theorem_derived` theorem | ~80 | **conditional-verified** (3 inherited Ehrhart axioms) |
| S∞ | R2 unconditional discharge of 3 Ehrhart axioms | ~3000+ | Mathlib roadmap |

The S5 deliverable status is honestly "`picks_theorem` proved
*conditional on Ehrhart polynomial existence + Macdonald reciprocity*"
— a meaningful axiom-count reduction (the standalone `picks_theorem`
axiom is replaced by the structurally weaker assumption "Ehrhart
exists for 2D polygons"), but not a full axiom discharge.

## Numerical Sanity (worked examples)

For each lattice polygon below, verify $A = i + b/2 - 1$ AND that
the Ehrhart polynomial $L_P(n) = A n^2 + (b/2) n + 1$ correctly
predicts $L_P(0) = 1$ (the trivial point) and $L_P(1) = A + b/2 + 1
= i + b$ (total lattice points).

| Polygon | $A$ | $i$ | $b$ | $A = i + b/2 - 1$? | $L_P(1) = i + b$? |
|---------|-----|-----|-----|---|---|
| Unit square $[0,1]^2$ | 1 | 0 | 4 | $1 = 0 + 2 - 1$ ✓ | $1 + 2 + 1 = 4 = 0 + 4$ ✓ |
| $[0,2]^2$ | 4 | 1 | 8 | $4 = 1 + 4 - 1$ ✓ | $4 + 4 + 1 = 9 = 1 + 8$ ✓ |
| Unit right triangle | 1/2 | 0 | 3 | $1/2 = 0 + 3/2 - 1$ ✓ | $1/2 + 3/2 + 1 = 3 = 0 + 3$ ✓ |
| $[0,3]^2$ | 9 | 4 | 12 | $9 = 4 + 6 - 1$ ✓ | $9 + 6 + 1 = 16 = 4 + 12$ ✓ |
| Pentagon (1,0),(2,1),(1,2),(0,1) | 2 | 1 | 4 | $2 = 1 + 2 - 1$ ✓ | $2 + 2 + 1 = 5 = 1 + 4$ ✓ |

All five examples verify both directions. The Ehrhart polynomial
predicts the lattice point counts at $n = 1$ exactly, providing the
empirical bridge from Ehrhart theory to Pick's formula.

### Macdonald reciprocity sanity (unit square)

For the unit square $P = [0, 1]^2$, $A = 1$, $b = 4$, $i = 0$.
- $L_P(n) = (n + 1)^2 = n^2 + 2n + 1$ ✓ (matches $A n^2 + (b/2) n + 1$).
- $L_{P^\circ}(n) = (n - 1)^2 = n^2 - 2n + 1$ for $n \ge 1$ (interior
  points only).
- Macdonald: $L_{P^\circ}(1) = i = 0$. Check: $(-1)^2 L_P(-1) = L_P(-1)
  = 1 - 2 + 1 = 0$. ✓

So $L_P(-1) = 0$ for the unit square — consistent with Macdonald.
For a general lattice polygon, $L_P(-1) = i$ (the interior count) by
Macdonald, which is one data point that pins the linear-term
coefficient of the Ehrhart polynomial.

## References

- G. A. Pick, *Geometrisches zur Zahlenlehre*, Sitzungsber. Lotos
  (Prag) **19** (1899), 311-319 — original Pick's theorem.
- E. Ehrhart, *Sur les polyèdres rationnels homothétiques à n
  dimensions*, C. R. Acad. Sci. Paris **254** (1962), 616-618 —
  original Ehrhart polynomial.
- I. G. Macdonald, *Polynomials associated with finite cell-complexes*,
  J. London Math. Soc. **(2) 4** (1971), 181-192 — Ehrhart-Macdonald
  reciprocity.
- R. P. Stanley, *Decompositions of rational convex polytopes*, Ann.
  Discrete Math. **6** (1980), 333-342 — $h^*$-vector and generating
  function approach.
- M. Beck, S. Robins, *Computing the Continuous Discretely*, Springer
  UTM (2nd ed. 2015) — standard textbook on Ehrhart theory.
- Gallery parent: `proofs/Proofs/EhrhartCubeProven.lean` (Lean
  Genius, verified, 0 axioms, 296 lines).
- Gallery axiom container: `proofs/Proofs/EhrhartPolynomials.lean`
  (Lean Genius, 3 axioms `ehrhart_theorem` + `ehrhart_leading_coeff_volume`
  + `ehrhart_macdonald_reciprocity`, contains `picks_from_ehrhart`
  conditional theorem at line 218).
- Gallery axiom: `proofs/Proofs/PicksTheorem.lean` line 148
  `axiom picks_theorem` — the standalone axiom that OQ-05 targets.

## Honesty / Calibration

This S1 OBSERVE is **doc-only**. The OQ-05 deliverable target is
**not an axiom-free proof of Pick's theorem** — it is the *bridge
theorem* `picks_theorem_derived` that derives Pick's identity from
the (already-axiomatized) Ehrhart existence + Macdonald reciprocity.
This is a meaningful structural reduction: the gallery currently
treats `picks_theorem` and the three Ehrhart axioms as independent
assumptions; S5's deliverable shows they are NOT independent,
collapsing the gallery's axiom dependency graph.

The full unconditional answer (R2, discharging the three Ehrhart
axioms) is a Mathlib-contribution-scale undertaking (~3000+ lines)
and is deferred.

## Anti-Targets (do NOT attempt in S2-S5)

- **Do not attempt to prove `ehrhart_theorem`, `ehrhart_leading_coeff_volume`,
  or `ehrhart_macdonald_reciprocity` from scratch.** Each is ~800-1500
  Lean lines.
- **Do not modify `PicksTheorem.lean`'s `axiom picks_theorem`** —
  that file is the gallery's canonical Pick's theorem entry; OQ-05's
  deliverable is a parallel theorem in a new file, not a rewrite.
- **Do not modify `EhrhartPolynomials.lean`'s axioms** — they are
  the foundation of the conditional reduction.
- **Do not pursue triangulation-based proofs of Pick's theorem** —
  that is `picks-theorem-oq-01`'s scope, NOT OQ-05's.
- **Do not introduce new axioms beyond a single bridge axiom** for
  Q2's structure-conversion (and even that should be replaced by
  a constructive bridge function if feasible).

## No-Edit Guarantee (this S1)

This S1 OBSERVE iteration modifies ONLY:

- `research/problems/ehrhart-cube-proven-oq-05/problem.md` (new)
- `research/problems/ehrhart-cube-proven-oq-05/knowledge.md` (new)
- `research/problems/ehrhart-cube-proven-oq-05/state.md` (new)
- `src/data/research/problems/ehrhart-cube-proven-oq-05.json` (new)

No `proofs/`, `src/data/proofs/`, `proofs/Proofs.lean`, or any
parent / sibling proof file is touched. No Lean compilation is
required for this PR.
