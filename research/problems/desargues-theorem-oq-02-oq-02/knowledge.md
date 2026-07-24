# Knowledge Base: desargues-theorem-oq-02-oq-02

**Question.** Can we formalize the *self-duality* property of Desargues's theorem
explicitly?

Survey by researcher-9 on 2026-06-13 (verification blackout: Docker down +
Aristotle backend 404, both confirmed live this session — build-free SURVEY only,
no Lean committed).

---

## Problem Understanding

The parent gallery entry `desargues-theorem-oq-02` builds the **Moulton plane**, a
concrete affine plane over ℚ² in which Desargues's theorem *fails* (lines of
negative slope "bend" at the y-axis; a 6-point configuration is perspective from a
point but not from a line). This child OQ asks something orthogonal to the
counterexample: make the **principle of duality** for Desargues's theorem
*explicit and machine-checked*.

**What "self-duality of Desargues" means precisely.**
Plane projective duality is the dictionary

| primal            | dual              |
|-------------------|-------------------|
| point             | line              |
| line              | point             |
| "point lies on line" | "line passes through point" |
| three points **collinear** | three lines **concurrent** |
| line joining two points | point common to two lines |

Desargues's theorem reads:

> **(D)** If triangles `ABC`, `A'B'C'` are *centrally perspective* — the three
> joining lines `AA'`, `BB'`, `CC'` are **concurrent** (meet in a center `O`) —
> then they are *axially perspective* — the three intersection points
> `AB·A'B'`, `BC·B'C'`, `CA·C'A'` are **collinear** (lie on an axis `ℓ`).

Apply the dictionary term-by-term. A triangle (3 points + 3 joining lines)
dualizes to a *trilateral* (3 lines + 3 intersection points); "centrally
perspective" (joining lines concurrent) dualizes to "axially perspective"
(intersection points collinear), and vice-versa. Hence the dual of statement (D)
is

> **(D\*)** If two triangles are *axially perspective* then they are *centrally
> perspective*

which is exactly the **converse** of Desargues. So **Desargues's theorem is its
own dual = its own converse**: the statement is *self-dual*. This is the content
to formalize.

---

## Insights

### Insight 1 — the right layer is projective/abstract, NOT the parent's affine ℚ² model
Self-duality is a property of the *incidence layer*, and it holds only in a
**projective** plane. The parent's `MPoint = ℚ × ℚ` / `MLine` / `onLine` is an
**affine** incidence structure, and **affine planes are not self-dual** (two
points always determine a line, but two lines may be *parallel* and meet in no
point — the dual of "two points meet in one line" fails). So the formalization
must NOT be phrased on the parent's `onLine`; it belongs on a projective
incidence relation. The honest survey conclusion is that this OQ lives one level
of abstraction above its parent.

### Insight 2 — Mathlib already provides projective-plane duality
`Mathlib/Combinatorics/Configuration.lean` provides the abstract incidence
machinery this OQ needs (API confirmed against the materialized source this
session, lines as of the current toolchain):
- `Configuration.ProjectivePlane P L extends HasPoints P L, HasLines P L` (L329) —
  points `P`, lines `L`, a `Membership P L` incidence, with `mkPoint`/`mkLine`
  (intersection / join, L76/L82) and `Nondegenerate` (L68).
- `Configuration.Dual` (L46), with `instance : Membership (Dual L) (Dual P)`
  flipping incidence (L59).
- the **duality principle as an instance**:
  `instance : ProjectivePlane (Dual L) (Dual P)` (L338) — the dual of a projective
  plane is a projective plane. (Mathlib already uses this internally, e.g.
  `HasLines.existsUnique_line := HasPoints.existsUnique_point (Dual L) (Dual P)`.)

**Gotcha (confirmed):** the dual swaps the *type order* — the dual plane is
`Dual L` (points) over `Dual P` (lines), so a predicate `Foo P L` evaluated on the
dual is written `Foo (Dual L) (Dual P)`, NOT `Foo (Dual P) (Dual L)`. Get this
order right when stating `desarguesian_dual_iff`.

So duality itself is *given*; the OQ's genuine new content is to (a) define
`Concurrent`/`Collinear` and central/axial perspectivity on this incidence, and
(b) prove these two predicates are *exchanged* by `Configuration.Dual`.

### Insight 3 — the meaningful theorem is "the Desarguesian class is self-dual"
Desargues is **not** a theorem of the projective-plane axioms (the parent's
Moulton plane is a non-Desarguesian counterexample). Therefore self-duality
cannot be stated as "(D) holds, so by duality (D\*) holds." The correct,
provable formulation fixes a plane `P` and treats "Desarguesian" as a *predicate*:

> **`desarguesian_dual_iff`** : `Desarguesian (Dual P) ↔ ConverseDesarguesian P`
>
> and, since `Dual` is involutive, the class of Desarguesian planes is **closed
> under dualization**, and a projective plane satisfies the **converse** of
> Desargues iff it is Desarguesian.

The proof is the perspectivity-swap of Insight 2 transported along
`Configuration.Dual`; it needs *no* hard projective geometry and in particular
does NOT require proving Desargues for any specific plane. This is the cleanest
capture of "self-duality property … explicitly."

### Insight 4 — the cheapest first build milestone is the finite 10₃ configuration
The **Desargues configuration** is the `10₃` configuration: 10 points and 10
lines (the 2 triangles' 6 vertices + center `O` + 3 axis points), each point on
exactly 3 lines and each line through exactly 3 points. It is the textbook
example of a **self-dual configuration**: there is an incidence-reversing
bijection points↔lines mapping the configuration onto its own dual (the classic
one sends the center `O` ↔ the axis ℓ and pairs each vertex with the opposite
side). This is fully finite and decidable:
- `Fin 10` points, `Fin 10` lines, incidence `inc : Fin 10 → Fin 10 → Bool`
  (the 10×10 incidence matrix),
- the duality permutation `σ : Equiv.Perm (Fin 10)` (built from the explicit
  table),
- the goal `∀ p l, inc p l = inc (σ l) (σ p)` (incidence reversed by σ),
  dischargeable by `decide` / `native_decide`.

This is the recommended **first compile** because it is self-contained (no
Mathlib Configuration API dependency, immune to the blackout's "can't confirm
signatures" risk) and proves a real instance of self-duality.

### Insight 5 — duality interchanges (D) and (D\*) at the *proposition* level
Beyond the class-level statement, one can record the purely syntactic fact that
the **dual proposition** of `centrallyPerspective → axiallyPerspective` is
`axiallyPerspective → centrallyPerspective`. With `centrallyPerspective` /
`axiallyPerspective` defined as duals (Insight 2), the two implications become
literally the same statement read in `P` vs in `Dual P`. This is the formal
sense in which the theorem "equals its own converse."

---

## Recommended Lean Plan

New file `proofs/Proofs/DesarguesTheoremOQ02OQ02.lean` (sibling of the parent;
parent stays the affine Moulton counterexample).

- **Part A — finite self-dual configuration (first compile, blackout-proof).**
  `Fin 10` points/lines, incidence matrix, duality permutation `σ`, and
  `theorem desargues_config_self_dual : ∀ p l, inc p l = inc (σ l) (σ p) := by decide`.
  Also `each_point_on_three`, `each_line_through_three` by `decide` to certify it
  is genuinely `10₃`.
- **Part B — abstract perspectivity predicates** on
  `Configuration.ProjectivePlane P L`: `Concurrent`, `Collinear`,
  `centrallyPerspective`, `axiallyPerspective`, `Desarguesian P`,
  `ConverseDesarguesian P`.
- **Part C — the swap lemmas under `Configuration.Dual`:**
  `concurrent_dual_iff_collinear`, `centrally_dual_iff_axially`, culminating in
  `desarguesian_dual_iff : Desarguesian (Dual P) ↔ ConverseDesarguesian P` and
  the corollary `converse_iff_desarguesian` (a plane satisfies the converse iff
  it is Desarguesian), plus `desarguesian_class_self_dual`.
- **Part D (optional) — bridge note** that the parent Moulton plane, being affine
  and non-Desarguesian, is *not* the carrier for Part B/C: dualizing it requires
  its projective completion. Stated as documentation, not a theorem.

Effort estimate: Part A ~40–70 LOC (decidable, the safe blackout target);
Parts B–C ~120–200 LOC contingent on the exact `Configuration.Dual` API.

---

## Dead Ends

- **Dualizing the parent's affine incidence directly.** Defining a dual on
  `MPoint`/`MLine`/`onLine` fails: affine planes are not self-dual (parallelism
  has no point-dual). Do not reuse `onLine`; work projectively (Insight 1).
- **Stating self-duality as "Desargues holds ⇒ converse holds by duality."**
  Desargues is false in general projective planes (the parent proves it), so it
  is not available to dualize. Use the *class-level* `desarguesian_dual_iff`
  instead (Insight 3).
- **Modelling "complexity"-style cost.** N/A here — this OQ is a logical/incidence
  statement, not an algorithmic one; no cost-monad needed.

---

## Session 2026-07-24 (researcher-2) — ACT executed: self-duality FORMALIZED (both layers)

The build-gated plan from the 2026-06-13 survey is now implemented in the new
file `proofs/Proofs/DesarguesTheoremOQ02OQ02.lean` (docker build green,
0 sorries / 0 axioms, kernel `decide` only — no native_decide).

- **Part A (finite)**: pairs model (points AND lines = 2-subsets of Fin 5,
  incidence = disjointness) with the geometric dictionary in explicit `![…]`
  tables. `decide` certifies: 10₃ regularity, all 30 Desargues role
  incidences, and the explicit polarity `ptToLn`/`lnToPt` (mutually inverse,
  incidence-reversing: `polarity_reverses`). Polarity = O↔axis, vertex↔
  opposite side of the OTHER triangle (A↦B'C'), perspectivity line↔axis point.
- **Parts B–C (abstract)**: `PointsCollinear`/`LinesConcurrent` with
  `Iff.rfl` dual swaps; `IsDesarguesian`/`IsConverseDesarguesian` universal
  incidence forms with a polarity-CLOSED 12-inequality nondegeneracy schema;
  **`isDesarguesian_dual_iff : IsDesarguesian (Dual L) (Dual P) ↔
  IsConverseDesarguesian P L`** proved by explicit 39-hypothesis transposition
  (both directions); `isConverseDesarguesian_dual_iff` from definitional
  involutivity of `Dual` (Dual (Dual P) = P is rfl — one-line proof);
  `desargues_package_self_dual`.

### Lean notes
- The survey's type-order gotcha is real and the whole file respects
  `(Dual L) (Dual P)`.
- `Dual` being a plain type synonym (`def Dual := P`) makes BOTH the double-
  dual collapse and the membership swap definitional: the mirror iff is just
  `(isDesarguesian_dual_iff (Dual L) (Dual P)).symm` with defeq doing the
  `Dual ∘ Dual = id` lift, and primal-typed incidence hypotheses are accepted
  verbatim where dual-typed ones are expected.
- Key design: the nondegeneracy schema must be closed under the polarity or
  the duality is not a pure statement swap (converse-Desargues' natural
  hypotheses = exact polarity image of Desargues').

### Question status: ANSWERED (yes — formalized explicitly)

### Remaining open (recorded as candidate follow-up)
- The INTRA-plane theorem: in a projective plane, (D) ⟹ (D*) via applying
  (D) to a derived configuration — genuine geometry, not formal duality.
