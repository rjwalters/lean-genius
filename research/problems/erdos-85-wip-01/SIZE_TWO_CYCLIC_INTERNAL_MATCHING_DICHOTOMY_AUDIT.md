# Size-two cyclic internal matching dichotomy audit

## Terminal role

The no-empty packing target splits at a fixed internal fibre graph.  Full
vertex support and degree one give a perfect matching.  Otherwise some
vertex has internal degree at least two, hence the diagonal block contributes
an off-diagonal two-step path and consumes a same-fibre codegree slot.  This
audit tests whether the perfect-matching side is a genuine residual branch.

## Bounded exact result

`size_two_cyclic_full_probe.py` now accepts
`--require-internal-perfect-matching`, requiring every base in every allowed
fibre to have exactly one internal neighbour.  With exact row and column hits
and undirected reciprocity, but **without any agreement caps**, the result is:

```text
q=4, a=1: UNSAT
q=6, a=1: UNSAT
q=8, a=1: UNSAT
```

At q=8 the corresponding directed instance is SAT, so reciprocity is the
essential obstruction rather than the hit equations alone.  A grouped q=8
reciprocity core is

```text
33 34 35 37 44 45 47 57
```

where `tu` denotes transpose symmetry between fibre blocks `t,u` (for the
allowed labels at `a=1`).  The core is sufficient and deletion-order
dependent, not a minimal mathematical certificate.

## Consequence and remaining link

The no-cap full-support q8 model is therefore necessarily irregular; its
banked profiles exhibit this directly.  This makes the useful exhaustive
dichotomy sharper:

1. some fibre is not fully supported, giving the quantitative
   `collision >= q-s_t` pressure;
2. every fibre is fully supported, and reciprocity must force an internally
   irregular fibre (the q-generic version of the bounded result above);
3. that irregular fibre has an internal two-path, which consumes one of the
   at-most-one common-target slots for its endpoint pair.

Steps 2 and 3 are not yet a contradiction.  The missing terminal theorem is
an integer, pair-rooted lower bound showing that external routes must also
give a common target for sufficiently many endpoint pairs of internal
two-paths.  This would collide with the occupied cap slot.  Scalar pinched
moments cannot express that overlap; the endpoint labels must be retained.

The bounded result is evidence for a q-generic reciprocity parity lemma, not
permission to replace it with an enumeration.

## Local two-path charging is false

The probe also supports `--force-internal-two-path T X Y Z` together with
`--only-cap-pair T X Z`.  This forces the internal common neighbour `Y` of
the endpoint sources and retains only their one common-target cap.  At q=8,
a=2, all admissible representatives tested are SAT, including

```text
(t,x,y,z) = (3,0,1,2), (3,0,1,3), (3,0,2,4), (4,0,1,2).
```

Thus one internal two-path does not make exact hits and reciprocity force a
second common target for the same endpoints.  The remaining positive-
variance theorem must aggregate many labelled endpoint pairs; a local
two-path-to-cap-violation lemma is false.
