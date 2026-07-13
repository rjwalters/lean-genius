# Problem: Desargues' theorem over free modules of rank 3 over non-commutative rings

**Slug**: desargues-theorem-oq-01-oq-03
**Created**: 2026-07-09T16:03:15-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $D$ be a (possibly non-commutative) division ring and let $M = D^3$ be the free
left $D$-module of rank $3$, so that $\mathbb{P}^2(D)$ is the projective plane whose
points are $1$-dimensional subspaces of $M$. For triangles
$\triangle ABC$ and $\triangle A'B'C'$ in general position, the forward direction of
Desargues' theorem asserts

$$
\left(\bigcap \{AA', BB', CC'\} \neq \varnothing\right)
\;\Longrightarrow\;
P, Q, R \text{ are collinear},
\qquad
\begin{aligned}
P &= AB' \cap A'B,\\
Q &= BC' \cap B'C,\\
R &= CA' \cap C'A.
\end{aligned}
$$

Equivalently: *perspective from a point $\Rightarrow$ perspective from a line*. The task
is to formalize this over $D$ in the coordinate model, where the commutative-ring proof
(the master identity $\det(P,Q,R) = \det(AA',BB',CC')\cdot\det(A,B,C)\cdot\det(A',B',C')$)
must be replaced by an argument that does not assume $xy = yx$ and does not assume a
well-behaved determinant.

### Plain Language

Desargues' theorem says that if two triangles are "in perspective from a point" (the three
lines joining corresponding vertices meet at one point), then they are also "in perspective
from a line" (the three points where corresponding sides meet all lie on one line). The
gallery already has a fully verified proof over any *commutative* ring $K$, driven by a
degree-9 polynomial determinant identity that the `ring` tactic closes. This problem asks:
does the theorem still hold, and can it be formalized, when the coordinate ring is a
*non-commutative* division ring $D$ (a "skew field") such as the quaternions? Classically the
answer is **yes** — Desargues holds in exactly those projective planes coordinatizable by a
division ring, commutative or not — but the polynomial-identity machinery breaks because
determinants over non-commutative rings are no longer multilinear or multiplicative in the
usual sense.

### Why This Matters

- **Sharp characterization of Desarguesian planes.** Hilbert's *Grundlagen der Geometrie*
  and Artin's *Geometric Algebra* establish that a projective plane satisfies Desargues'
  theorem iff it is coordinatizable over a division ring. The non-commutative case is the
  essential half of this equivalence: it is precisely where Desargues holds but **Pappus
  fails** (Pappus forces commutativity, by the Hessenberg–Artin theory). Formalizing OQ-03
  makes the boundary between the two configuration theorems machine-checked.
- **Tests Mathlib's non-commutative linear algebra.** The commutative proof leans entirely on
  `Matrix.det` and `ring`. A non-commutative formalization forces a genuinely different
  toolkit (Dieudonné determinant, or a determinant-free synthetic/quasideterminant argument),
  exercising `DivisionRing`, left/right module structure, and non-commutative
  `noncomm_ring`-style normalization.
- **Foundational for skew projective geometry in Lean.** A working non-commutative model of
  $\mathbb{P}^2(D)$ is a prerequisite for formalizing the fundamental theorem of projective
  geometry, collineations over skew fields, and quaternionic/octonionic projective spaces.

## Known Results

### What's Already Proven

- **Desargues over any commutative ring $K$** — gallery proof `desargues-theorem-oq-01`
  (`Proofs/DesarguesTheoremOQ01.lean`, 0 sorries, 0 axioms). Forward direction over any
  `CommRing`, converse over any `IntegralDomain`, via the master identity
  $\det(P,Q,R)=\det(AA',BB',CC')\cdot\det(A,B,C)\cdot\det(A',B',C')$.
- **Desargues over $\mathbb{R}$** — original gallery proof `desargues-theorem`.
- **Hilbert (1899), *Grundlagen der Geometrie*** — a projective plane is Desarguesian iff it
  is coordinatizable by a division ring (not necessarily commutative).
- **Artin (1957), *Geometric Algebra*** — algebraic development of $\mathbb{P}^n(D)$ over a
  division ring, including the coordinatization theorem and the role of Desargues.
- **Dieudonné determinant** — a well-defined determinant $\mathrm{GL}_n(D) \to D^\times/[D^\times,D^\times]$ for matrices over a division ring, the standard replacement for the commutative determinant.

### What's Still Open

- No Lean formalization of $\mathbb{P}^2(D)$ or Desargues' theorem over a non-commutative
  division ring currently exists in the gallery or (to our knowledge) in Mathlib.
- Which proof route is most tractable in Lean: (a) Dieudonné-determinant analogue of the
  commutative identity, (b) synthetic/coordinate-free argument via central collineations, or
  (c) an explicit component computation using `noncomm_ring`.
- Whether the converse (perspective from a line $\Rightarrow$ from a point) can be captured in
  the same non-commutative framework with a suitable non-degeneracy hypothesis.

### Our Goal

Formalize the **forward direction** of Desargues' theorem for the coordinate plane
$\mathbb{P}^2(D)$ over a general division ring $D$, using rank-3 free left $D$-modules. Success
is a Lean statement `desargues_forward_D` with 0 sorries whose hypotheses and conclusion
faithfully render "perspective from a point $\Rightarrow$ perspective from a line" and which,
specialized to a `Field`, recovers the existing commutative result. The converse and a
non-Desarguesian counterexample (cf. OQ-02) are out of scope for the first milestone.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| desargues-theorem-oq-01 | Direct parent: commutative-ring proof this problem generalizes; supplies the master identity and cross-product setup | Custom cross product, `Matrix.det`, degree-9 `ring` identity |
| desargues-theorem | Original real-coordinate Desargues; baseline statement of perspectivity | Cross products, determinants over $\mathbb{R}$ |
| desargues-theorem-oq-02 | Complementary: Moulton-plane non-Desarguesian counterexample showing dependence on line structure | Synthetic incidence, counterexample construction |
| desargues-theorem-oq-04 | Related: self-duality of Desargues over commutative rings, same algebraic framework | Projective duality, determinant symmetry |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Dieudonné determinant analogue.**
   Replace `Matrix.det` with the Dieudonné determinant $\det{}^D : \mathrm{GL}_3(D) \to D^\times_{\mathrm{ab}}$ and re-derive a multiplicative master identity in the abelianization $D^\times/[D^\times,D^\times]$.
   - Why it might work: the Dieudonné determinant *is* multiplicative, and "collinear $\iff$ determinant vanishes" survives as a rank condition ($\det^D$ is only defined on invertibles, but singularity = rank $< 3$ is well-defined).
   - Risk: Mathlib has limited Dieudonné-determinant support; much infrastructure (well-definedness, multiplicativity) may have to be built or axiomatized first, and the collinearity predicate must be phrased as a rank condition, not a scalar identity.

2. **Approach B — Synthetic central-collineation argument.**
   Formalize Desargues via the group of central collineations of $\mathbb{P}^2(D)$: perspectivity from a center is a collineation, and its action forces the axis. This is the standard non-metric proof and never touches determinants.
   - Why it might work: purely incidence-theoretic, hence agnostic to commutativity; matches Hilbert/Artin exposition.
   - Risk: requires substantial projective-plane and collineation-group scaffolding in Lean that does not yet exist; large upfront cost.

3. **Approach C — Direct component computation with `noncomm_ring`.**
   Keep the cross-product / coordinate style of OQ-01 but track left/right scalar placement carefully and close the resulting non-commutative polynomial obligations with `noncomm_ring` (and hand-guided rewriting).
   - Why it might work: reuses the concrete, already-understood OQ-01 skeleton.
   - Risk: the OQ-01 identity is *false* verbatim over non-commutative $D$ (it relies on multilinearity that needs $xy=yx$); a corrected identity in $D_{\mathrm{ab}}$ or a rank statement is needed, so this likely collapses back into Approach A.

### Key Difficulties

- Determinants over non-commutative rings are neither multilinear nor multiplicative; the
  entire degree-9 `ring` identity of OQ-01 is unavailable.
- Left- vs. right-module conventions: $D^3$ as a left module means scalars multiply on one
  side, and collinearity/incidence must be phrased consistently.
- Choosing a collinearity predicate that is meaningful over $D$ (rank $< 3$ of the coordinate
  matrix, rather than "$\det = 0$").
- Mathlib coverage: `DivisionRing`, modules over noncommutative rings, and matrix rank exist,
  but the Dieudonné determinant and non-commutative projective geometry are thin or absent.

### What Would a Proof Need?

- Key lemma 1: a well-defined "singularity/rank-3" collinearity predicate for triples in $D^3$
  that specializes to $\det = 0$ over a field.
- Key lemma 2: a multiplicative surrogate for the master identity, e.g. an equation in
  $D^\times/[D^\times,D^\times]$ (Dieudonné) relating perspectivity data to collinearity of
  $P,Q,R$; or a purely synthetic collineation lemma.
- Technical requirements: `Module D (Fin 3 → D)` with correct handedness,
  `DivisionRing D`, matrix-rank / invertibility infrastructure, and a specialization lemma
  proving the new statement reduces to `desargues_forward_K` when $D$ is commutative.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The commutative proof's central engine (`ring` on a determinant identity) does not transfer;
  a mathematically different argument is required, not a mechanical port.
- Non-commutative projective geometry and the Dieudonné determinant are largely unformalized
  in Mathlib, so significant foundational scaffolding must be built.
- The mathematics is classical and settled (Hilbert/Artin), so there is no research risk about
  *whether* the theorem holds — only about formalization strategy and effort.
- A concrete, motivating special case ($D = \mathbb{H}$, the quaternions) is available for
  sanity-checking definitions.

**Estimated Effort**:
- Exploration: 1–2 weeks (survey Mathlib's noncommutative-module and matrix-rank support;
  pick predicate and route)
- If tractable: 3–6 weeks (build minimal $\mathbb{P}^2(D)$ model + forward direction)
- If hard: unknown (if full Dieudonné-determinant infrastructure must be developed first)

## References

### Papers
- Hilbert, D., *Grundlagen der Geometrie* (1899) — Desargues characterizes division-ring
  coordinatizable planes; the commutative-vs-noncommutative distinction via Pappus.
- Artin, E., *Geometric Algebra* (1957) — coordinatization of $\mathbb{P}^n(D)$ over division
  rings; Desargues and the Hessenberg–Artin relationship to Pappus.
- Dieudonné, J., "Les déterminants sur un corps non commutatif," *Bull. SMF* 71 (1943) —
  construction of the determinant over a division ring.

### Online Resources
- https://en.wikipedia.org/wiki/Desargues%27s_theorem — statement, projective-plane
  characterization, Desarguesian vs. non-Desarguesian planes.
- https://en.wikipedia.org/wiki/Dieudonn%C3%A9_determinant — the non-commutative determinant.
- https://en.wikipedia.org/wiki/Non-Desarguesian_plane — context for when Desargues fails.

### Mathlib
- `Mathlib.Algebra.Field.Basic` / `DivisionRing` — the coordinate structure $D$.
- `Mathlib.LinearAlgebra.Matrix.Determinant.Basic` — commutative determinant (baseline; must
  be replaced for $D$).
- `Mathlib.LinearAlgebra.Matrix.Rank` — matrix rank, candidate for the collinearity predicate.
- `Mathlib.Tactic` (`noncomm_ring`) — normalization in non-commutative rings.
- `Mathlib.Algebra.Quaternion` — concrete non-commutative division ring for testing.

## Metadata

```yaml
tags:
  - projective-geometry
  - triangles
  - perspective
  - collinearity
  - concurrence
  - commutative-ring
  - linear-algebra
  - classic
  - research
related_proofs:
  - desargues-theorem-oq-01
  - desargues-theorem
  - desargues-theorem-oq-02
difficulty: high
source: user-request
created: 2026-07-09T16:03:15-07:00
```
