# H7 low-degree polynomial-calculus audit

Date: 2026-08-26.  Scope: bounded algebraic gate for divergence-round-72
candidate P2, on the 861 semantic edge variables of a canonical H7 parent.
No Macaulay matrix was built.

## Generator degrees

In the Boolean quotient, use `x_e^2 = x_e`.  The native H7 equations have:

- linear degree equalities and empty-mask units;
- quadratic Boolean equations;
- one monomial equation for every surviving forbidden C4 witness.

An exact pass through the canonical fixed-support `status` function splits
the 687,260 C4 generators as follows:

| polynomial degree | generator count |
|---:|---:|
| 2 | 15,680 |
| 4 | 671,580 |

There are no cubic C4 generators.  In particular, a polynomial-calculus
refutation of degree at most three cannot consume any of the 671,580
quartic generators that carry almost all of the C4 information.

## The degree-three-visible subsystem is satisfiable

For the hard F6/t2 mask, I emitted the exact compact degree constraints and
mask units, retained all 15,680 quadratic C4 clauses, and omitted only the
quartic witnesses.  The reproducible builder and semantic witness checker is
`sat49/probe_h7_polynomial_calculus_degree_gate.py`.  The resulting CNF has
17,633 variables and 49,245
clauses, SHA-256
`04fe5b2129fc9de43809a78608c52fd1f1933ebb94198097630269e4c642db56`.
Kissat 4.0.4 returned `SAT` in the bounded run.  The semantic edge assignment
was then checked directly against every low-vertex degree target, all 21 mask
bits, and the complete retained quadratic-C4 set.

Therefore no polynomial-calculus proof of any degree can refute that
visible subsystem, and a degree-at-most-three proof of the full parent is
impossible: such a proof has no legal use of the omitted degree-four
generators.

## Degree-four scale

The exact squarefree monomial counts for 861 variables are:

| maximum degree | monomials |
|---:|---:|
| 2 | 371,092 |
| 3 | 106,380,282 |
| 4 | 22,845,351,537 |

Merely indexing the full degree-four Boolean-quotient column space takes
about 2.86 GB at one bit per monomial, before row indices, coefficients, or
elimination state.  The starting system also has 671,580 distinct quartic
rows.  Thus the proposed sparse Macaulay rank test at degree four is already
outside a bounded probe by several orders of magnitude; multiplying any
quartic generator would only increase the degree and basis.

## Verdict

**CUT for the proposed low-degree Macaulay/Nullstellensatz mechanism.**
Degree at most three is rigorously excluded by a genuine satisfying model of
everything it can see.  A generic degree-four Macaulay construction begins
with 22.8 billion columns and 671,580 quartic generators, so it is not a
compact alternative certificate route.  This does not rule out a future
hand-derived sparse polynomial identity using a tiny selected monomial
support; it does rule out searching for that identity by the proposed full
low-degree rank calculation.  The H7 certified baseline remains 14/43.
