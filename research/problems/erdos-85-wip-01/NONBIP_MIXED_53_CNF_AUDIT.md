# `[5,3]` displayed-triangle CNF/Kissat audit

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [5,3]`.

Status: deterministic CNF and fail-closed semantic verifier banked; both
displayed-defect-triangle cases remain **UNKNOWN** at 120 seconds.

## Exact interface and scope

`cnf_nonbip_mixed_53_exterior_carrier.py` is an independent Boolean encoding
of the interface in `probe_nonbip_mixed_53_exterior_carrier.py`.  It retains:

* one symmetric loopless ambient adjacency on 64 vertices;
* internal/cross degrees `(5,3)` on the 40-shore and `(3,5)` on the 24-shore;
* at most one common neighbor for every pair and exactly one for each
  cross-shore pair;
* internal defect adjacency iff the common-neighbor count is zero, with
  defect degree seven on both shores;
* the displayed large-shore defect triangle, the complete canonical fixing
  of its three disjoint ambient neighborhoods in each shore, and the two
  ambient-triangle-edge symmetry cases; and
* the redundant carrier cross-part defect-hit clauses.

It deliberately omits connectivity and all triangle-free nonbipartite
`C5+` cases.  Hence the two CNFs exhaust only the displayed-triangle subcase,
not the full `[5,3]` branch.

## Encoding checks

Ambient edges occupy the first 2016 variables in lexicographic order.
Common-neighbor witnesses are shared Tseitin AND variables.  A Sinz
sequential encoding enforces common-neighbor at-most-one, and cross pairs add
the corresponding at-least-one clause.  Internal defect variables are
equivalent to the absence of all such witnesses.  Exact degrees use an exact
threshold recurrence, asserting threshold `k` and refuting threshold `k+1`.

The exact-cardinality encoding was exhaustively checked with Kissat on all
16 assignments of exact-2-of-4: precisely the six weight-two assignments
were SAT.  The sequential at-most-one encoding was independently checked on
all 16 four-bit assignments: precisely weights zero and one were SAT.  Both
checks reported zero mismatches.

The model verifier does not trust auxiliary variables as graph semantics.  It
first requires one `SATISFIABLE` status, a complete in-range assignment, and
satisfaction of every emitted clause.  It then reconstructs the graph from
the first 2016 variables and independently checks all degrees, common-neighbor
bounds/equalities, the derived defect degrees and triangle, every canonical
internal and exterior neighborhood, and every carrier-hit clause.  No SAT
model was produced in this audit, so the terminal verifier path has not yet
accepted a real model.

## Deterministic instances

Both cases contain 313600 variables and 997653 clauses.  Fresh emission gave:

```text
ambient triangle edges 0:
  bytes 17501247
  sha256 320fe3170503c07614ca26e7f90742195dcff12d64f384c240f7b5a62f8b5b49

ambient triangle edges 1 (canonical edge 0--1):
  bytes 17501246
  sha256 9af15d023d44352afa5b6902fd06e2f33b2510d50f2d35ebf2a1f3d2a3757d20
```

The one-byte size difference is the sign of the fixed `a_0_1` unit; variable
and clause counts are identical.

## Bounded Kissat result

Kissat 4.0.4 was run with `--time=120` on each exact CNF.  Both returned exit
code zero and `s UNKNOWN` at 119.99 process seconds:

```text
case 0: 418416 conflicts, 5356861 decisions, 3238319213 propagations
case 1: 457855 conflicts, 5570838 decisions, 3137628180 propagations
```

This is neither SAT nor UNSAT.  The native CNF route is operational and
substantially exercises the instance, but the displayed-triangle subcase
remains unresolved.  The next computational improvement should exploit the
three fixed carrier parts or add sound owner/Gram consequences; simply
raising the same generic time bound has no proof value.
