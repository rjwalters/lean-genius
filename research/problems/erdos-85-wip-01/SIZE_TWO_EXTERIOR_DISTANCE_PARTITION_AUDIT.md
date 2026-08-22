# Size-two exterior distance-partition audit

## Setup

Let `C` be a weight-two second-order-defect component in a symmetric
q-regular C4-free graph `G` on `q^2` vertices.  Put

```text
R = V minus C,        |R| = q(q-2),
K = G induced on R,  d = degree(K) = q-2.
```

Every `z in R` has a two-point trace `tr(z)=N_G(z) intersect C`.  Distinct
outside vertices have distinct traces, and each point of `C` occurs in
exactly `q-2=d` outside traces.

For fixed `z`, define:

* `p(z)` = the number of K-neighbors of `z` whose trace intersects `tr(z)`;
* `tau_K(z)` = the number of K-neighbors `w` of `z` with disjoint trace for
  which `z,w` also have a common K-neighbor;
* `far_disjoint(z)` = the number of `w != z` with disjoint trace which are
  neither K-neighbors nor joined to `z` by a K-two-path.

## Exact local law

```text
far_disjoint(z) = 1 + p(z) + tau_K(z),     with p(z) in {0,2}.
```

Proof by an exact distance partition:

1. The two trace endpoints of `z` each occur in `d-1=q-3` other traces.
   No trace can share both endpoints with `z`.  Hence the number of other
   traces disjoint from `tr(z)` is

   ```text
   q(q-2) - 1 - 2(q-3) = (q-2)^2 + 1 = d^2+1.
   ```

2. Every ordered nonbacktracking K-two-walk from `z` ends at a trace
   disjoint from `tr(z)`.  Otherwise the endpoint and `z` already have their
   shared component point as a G-common-neighbor, and the middle K-vertex
   would be a second one.  C4-freeness also makes different two-walks have
   different endpoints.  Thus exactly `d(d-1)` disjoint traces lie at
   K-distance two.

3. Of the `d` K-neighbors, exactly `d-p(z)` have disjoint trace.  Their
   overlap with the distance-two set has cardinality `tau_K(z)`: these are
   precisely the incident K-edges lying in a K-triangle.  Therefore the union
   of disjoint K-neighbors and disjoint distance-two vertices has size

   ```text
   (d-p(z)) + d(d-1) - tau_K(z) = d^2-p(z)-tau_K(z).
   ```

   Subtracting from `d^2+1` proves the display.

4. Finally `p(z)` is zero or two.  If the two trace points are H-adjacent,
   each cross edge already has the other trace point as its unique common
   neighbor, so `p(z)=0`.  Otherwise each of the two cross edges has a unique
   exterior resolver.  The resolvers are distinct because a repeated one
   would duplicate the two-point trace, so `p(z)=2`.

Summing over `z` gives the global form

```text
#{unordered far disjoint pairs}
  = |R|/2 + #{non-edge traces} + 3 * #{K-triangles}.
```

Indeed `sum_z p(z)/2` is the number of non-edge traces, while
`sum_z tau_K(z)=6` times the number of K-triangles.

## Exact relation to the triangle-free-edge graph

The tempting identification of `far_disjoint` with the whole exterior defect
graph is false: an exterior K-edge with disjoint traces and no K-common-
neighbor is itself a triangle-free A-edge and hence a D-edge.  Accounting for
these missing edges gives the correct pointwise identity

```text
degree_T(z) + p(z) + tau_K(z) = q-2.        (*)
```

Indeed among the `q-2-p(z)` disjoint-trace K-neighbors, exactly `tau_K(z)`
lie in a unique K-triangle and all the rest are T-neighbors.  Thus exterior
K-edges partition uniquely into:

* exterior T-edges;
* shared-trace resolver edges;
* the three edges of unique K-triangles.

If `a(C)` is the number of edge-traces, the number of resolver edges is
`q(q-2)-a(C)`.  Reducing the global edge partition modulo three at binary q
gives

```text
a(C) = |E(T[R])| (mod 3).
```

This is valid but supplies no new global pressure.  The internal ledger gives
`|E(T[C])| = 2q-a(C) (mod 3)`, so `a(C)` cancels after adding the two regions:

```text
|E(T)| = 2q (mod 3).
```

For `q=2^k`, this is exactly the already-banked global triangle-free-edge
congruence `|E(T)| = 2^(3k-1) (mod 3)`, because the two powers of two differ
by the even exponent `2k-2`.  Therefore the exterior mod-three route closes
at the existing global ledger; it does not force cycle synchronization.

## Relation to the q=16 reduced witness

The `C6 disjoint-union C26` eigenline/desynchronization model in
`q16_weight_two_cycle_sync_reduced_sat.py` already fixes the 224 traces and
the 198 shared-endpoint resolver edges, so it realizes the `p(z)` layer:
26 edge-traces have `p=0`, and 198 non-edge traces have `p=2`.  Completing
the remaining exterior adjacency must realize the distance law above in
addition to the 6,272 cross-block exact-cover equations.

The exact-cover linear system is consistent over `F_2`, `F_3`, and `F_5`.
Thus no scalar weighted congruence at these primes can kill the completion.
The real LP is **UNKNOWN** (HiGHS returned no primal point or infeasibility
proof in 120 seconds), so no real-feasibility claim is made.  The obstruction,
if one exists, lies beyond the tested modular interfaces and must ultimately
use the simultaneous 0/1 distance partition and C4-free codegree condition.

## Scope

This is a q-generic nonlinear identity, not a terminal.  Its Moore-style
slack is exactly one after the forced trace-intersection classes are removed,
which makes it a plausible consumer for diameter/excess or perfect-matching
arguments.  On its own it is an accounting equality and does not exclude a
completion.  A useful next lemma would have to bound the K-triangle term or
show that the `1+p(z)` far vertices cannot be placed compatibly across all
traces.
