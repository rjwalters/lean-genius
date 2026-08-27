# NONBIP-CONNECTED triangle-incidence Ward audit

## Candidate

Let `H` be the vertex-by-triangle incidence matrix and set

```text
C = A H - 2 H.
```

C4-freeness makes `C` a 0/1 matrix: `C[x,tau]=1` exactly when `x` is
outside the triangle `tau` and adjacent to its unique attachment vertex.  Thus

```text
wt(C_x) = B_x,
wt(C_x,H_x,H_x) = B_x + 2t_x = (A t)_x.
```

The divergence-78 proposal was to generate a doubly-even binary code from the
defect-edge differences `C_x+C_y`, use Ward's intersection criterion, and put
the rooted rows in one shadow coset.

## Exact algebraic interface

Over `F_2`,

```text
C C^T = A (H H^T) A,
H H^T = diag(t) + (A + K),
```

where `K` is the triangle-free-edge graph and `A+K` is the triangle-edge
graph modulo two.  On a defect edge `xy`, the diagonal term vanishes because
`x,y` have no common neighbor.  Hence

```text
|C_x intersect C_y| = (A (A-K) A)[x,y]  (mod 2).
```

This counts length-three ambient paths from `x` to `y` whose middle edge lies
in a triangle.  It vanishes when `xy` itself is a triangle-free ambient edge
(otherwise those four edges form a C4), but it is not forced to vanish on a
nonadjacent defect edge.

## Decisive q=4 counterprofile

`nonbip_connected_triangle_incidence_code_q4.py` checks all 256 calibration
models.  Every model has 24 defect-edge generators.  Exactly eight have weight
`2 mod 4`, and 40 unordered generator pairs have odd intersection.  The
offending edge profile is

```text
Axy=0, t_x=t_y=2, B_x=B_y=2,
|C_x intersect C_y|=1, wt(C_x+C_y)=2.
```

It occurs eight times per model.  Thus the span of the raw defect-edge row
differences is not doubly even.  Augmenting each row to `(C_x,H_x,H_x)` does
not repair it: `H_x` and `H_y` are disjoint on a defect edge, so the generator
weight becomes

```text
2 + 2(t_x+t_y) = 10 = 2 (mod 4).
```

This is a universal counterexample to the proposed Ward-code statement, not
an absence-of-evidence result.  The rooted target itself still holds on the
same rows; it simply does not arise from a doubly-even difference code.

## q=5 scope correction

The suggested q=5/order-25 full-graph falsifier is vacuous: a 5-regular graph
on 25 vertices would have odd degree sum `125`.  The previous 120-second
UNKNOWN result was a parity-hard impossible base encoding and supplies no
propagation evidence.  The next nonvacuous finite control would have even
degree (q=6 or the actual binary q=8), but no such control is needed to refute
the raw Ward claim because q=4 already does.

## Verdict

The triangle-incidence matrix remains a clean way to state the target, but the
preferred doubly-even-code mechanism is **cut**.  Any coding-theoretic repair
must add new coordinates whose contribution cancels the explicit
`t=2`, odd-intersection generator above and must prove Ward's pairwise
intersection conditions.  Merely appending copies of `H`, or invoking a code
shadow without constructing such a correction, does not do so.
