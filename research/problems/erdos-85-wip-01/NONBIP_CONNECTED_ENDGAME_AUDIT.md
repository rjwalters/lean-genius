# NONBIP-CONNECTED endgame audit

Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`, candidate (vi).

Status: strategic audit, 24 August 2026.  This does not close the node.

## The verified chain

For a hypothetical binary square-order candidate, connectedness of the
second-order defect graph `D` currently feeds two independent chains.

1. `binarySquare_regular_pred_le_defectCut_of_pos` gives the sharp lower
   bound `q-1` for every nonzero defect cut.  This proves that `D` is
   maximally edge-connected and, through
   `binarySquare_connected_secondOrderDefect_erase_connected` and the
   two-separator Mantel modules, that deleting one or two vertices cannot
   disconnect `D`.
2. The incidence bottleneck

   ```text
   E = AD - (J-A) = qA - A^3 + (q-1)J
   ```

   has nonzero integral zero-sum rows.  The closed-star residue strengthens
   its Frobenius lower bound to

   ```text
   ||E||_F^2 >= q^3+2  (k even),
   ||E||_F^2 >= q^3+4  (k odd),
   ```

   as formalized by
   `connected_binarySquare_dyadic_incidenceBottleneck_energy_ge_cube_add_two`
   and its odd-exponent sibling.  The same fact is an exact lower bound on
   the sixth adjacency moment.

The large three-separator tree is an attempt to extend item 1 from deletion
of two vertices to deletion of three.  Its recent bottom-slice chain is

```text
B48 paired wing profiles
  -> dyadic q mod 3 selection
  -> B51 zero/one P-core budget
  -> B50' exceptional-wing localization.
```

This is genuine classification progress, but it is not currently an
endgame.

## Geometric meaning of the incidence bottleneck

The flag-diagonal symmetric-configuration terminology gives `E` an exact
classical interpretation.  Under the self-polar identification, fix a point
`p` and a line label `z`.  Then

```text
(AD)_(p,z)
```

counts lines `y` through `p` which are parallel (nonconcurrent) to line `z`.
Indeed `A_(p,y)=1` is incidence and `D_(y,z)=1` says that the two labelled
lines have no common point.  If `p` lies on `z`, this count is zero.  If
`(p,z)` is an anti-flag, then

```text
E_(p,z) = number of lines through p parallel to z - 1.       (E-parallel)
```

Consequently `E=0` is precisely the type-C elliptic-semiplane parallel
axiom on this symmetric configuration: every anti-flag has exactly one
parallel through its point.  Even the usual “at most one” formulation forces
equality here.  All incident entries of `E` are zero, every anti-flag entry
would be nonpositive, and each row sum of `E` is zero because both `AD` and
`J-A` have row sum `q(q-1)`.

This also explains the connected nonvanishing theorem geometrically.  A
connected hypothetical candidate is not merely “not yet recognized” as an
elliptic semiplane: every point-row must violate the parallel axiom, balancing
anti-flags with no parallel (`E=-1`) against anti-flags with at least two
parallels (`E>=1`).  Thus the flag-diagonal completion target is exactly the
existing incidence-bottleneck target, not an independent missing theorem.
The energy `||E||_F^2` measures the total squared parallel-axiom defect.

Equivalently, for a fixed line `z`, let `c_z` be the number of intersecting
pairs among the `q-1` lines parallel to `z`.  Those lines have total
incidence `q(q-1)` on the `q(q-1)` points outside `z`.  Linearity gives

```text
sum_p E_(p,z)^2 = 2 c_z.                                (E-almost-spread)
```

Thus each bottleneck column measures how far the parallel family is from a
partial spread.  A pointwise bound `c_z <= q/2` would be a strong sufficient
form of the proposed cube upper after summing over `z`.  Standard partial-
spread deficiency theorems do not provide it: they assume the subspaces are
already pairwise disjoint and lie in an ambient projective, polar, or
translation geometry.  Here `c_z>0` and the absence of such an ambient
completion are exactly the two difficulties to be overcome.

## The missing arrow

No checked theorem or stated conjecture in the outline consumes
`vertexConnectivity(D) >= 4`.  More generally, no fixed connectivity lower
bound is known to imply singularity of `A`, an upper bound on the designated
spectral dimension, or an upper bound on `||E||_F^2`.  Therefore closing the
three-separator tree would prove a stronger property of `D` but would not
shorten a verified implication chain to `False`.

This matters structurally: a `(q-1)`-regular graph can have vertex
connectivity as large as `q-1`.  Thus repeatedly excluding separators has
no automatic terminal before the maximum possible connectivity, and even
maximal connectivity is not itself incompatible with the spectral and
determinant conditions recorded in `NONBIP_CONNECTED.md`.  An endgame must
use the special integral square-root identity `A^2=L_D+J`, not connectivity
alone.

## Candidate (vi): exact upper-bound terminal

The shortest consumer of the banked strict-energy theorem is the following
entrywise upper bound:

```text
INCIDENCE-BOTTLENECK-CUBE-UPPER
  Under the binary square-order, regular, C4-free hypotheses,
  if D is connected then ||AD-(J-A)||_F^2 <= q^3.
```

Together with the already proved dyadic strict lower bound, this gives
`q^3+2 <= q^3` immediately.  Equivalently, via
`binarySquare_regular_incidenceBottleneck_frobenius_eq_sixthTrace_sub_baseline`,
one may target the matching sixth-moment upper bound.  No wrapper should be
built before the upper bound itself exists.

At present this is a **candidate statement, not an axiom believed proved or
even independently validated**.  Its conditional Lean composition is being
handled separately; this audit does not duplicate that wrapper.  The exact
obstacle is visible in the row model: an entry of `E` is occupancy-minus-one
among `q-1` defect-neighbour blocks.  C4-freeness controls pairwise block
intersections, but the current ledger gives only a lower bound on row energy;
it gives no global upper bound on repeated occupancy.  A viable proof must
add a global packing constraint on those repeated occupancies.  Higher
vertex-connectivity does not provide that constraint by itself.

There is already a decisive calibration against overgeneralizing it.  In the
exact `q=4` fixed-free ambient control, every E-row has energy six, so
`||E||_F^2=96>64=q^3`; its defect graph is the disconnected `[8,8]` case.
Consequently the cube upper is false as a generic binary-incidence theorem.
Any viable version must genuinely use both connectedness and the intended
`k>=3` range, rather than merely carry those hypotheses unused.

There is also an exact graph-theoretic reformulation which fixes the scale
of the missing input.  Put `r=q-1`, and for `x in V(D)` let `t_x` be the
number of edges induced by `N_D(x)` (equivalently, the number of triangles
of `D` containing `x`).  Since `D` is `r`-regular and
`S_x={x} union N_D(x)` has `q` vertices,

```text
delta_D(S_x) = r q - 2 e_D(S_x)
             = (q-1)(q-2) - 2 t_x.
```

The row representation and `sum_x t_x = 3 tau(D)` therefore give the exact
global identity

```text
||AD-(J-A)||_F^2 = q^2 (q-1)(q-2) - 6 tau(D),              (E-triangle)
```

where `tau(D)` is the number of (unordered) defect triangles.  Hence
`INCIDENCE-BOTTLENECK-CUBE-UPPER` is equivalent to the very strong lower
bound

```text
6 tau(D) >= q^2 (q^2 - 4q + 2).                            (triangle-lower)
```

Relative to the elementary maximum
`tau(D) <= q^2 (q-1)(q-2)/6`, this says that the triangle deficit from a
disjoint union of `K_q`'s is at most `q^3/6`.  Connectivity points in the
opposite local direction: it makes every closed-star cut positive and, via
the banked maximal-connectivity theorem, supplies the *lower* energy bound.
It does not by itself make `D` sufficiently close to a union of cliques.
Thus a proof of the cube upper must now be advertised honestly as a
polarity/square-root-driven **triangle lower bound for `D`**, not as a cut or
connectivity estimate.  The sixth-moment restatement is algebraically the
same demand, since `(E-triangle)` already eliminates the repeated-occupancy
variables exactly.

Nor can bounded-degree clique stability finish after producing this
near-clique conclusion.  There is a uniform connected defect-only control at
exactly the permitted scale.  Begin with `q` disjoint copies of `K_q`, choose
a tree on the copies, and for each of its `q-1` edges perform a
degree-preserving two-switch: delete one internal edge in each endpoint
clique and replace the pair by two cross edges.  Internal edges can be chosen
so that all switches are legal; the quotient on the original cliques
contains the chosen tree.  The resulting graph is connected,
`(q-1)`-regular, and nonbipartite.

Each deleted clique edge belongs to `q-2` triangles.  New cross triangles or
overlap among destroyed triangles only improve the estimate, so its triangle
deficit is at most

```text
2 (q-1)(q-2).
```

By `(E-triangle)`, its closed-star cut sum is therefore at most
`12(q-1)(q-2)`, which is at most `q^3` for every `q>=8`.  Thus connected
regular nonbipartite graphs satisfying the proposed numerical cube upper are
abundant even after a sharp stability theorem has identified the near-clique
shape.  The construction is only a defect-graph control: it is not asserted
to admit a symmetric zero-one square root `A` with `A^2=L_D+J`.  Precisely
that integral square-root/self-indexing condition is now the sole possible
source of a contradiction on this route.

## The `mu=-1` blind spot, split by exponent parity

On a simultaneous adjacency/defect eigenvector, `E` acts by

```text
theta (mu+1),       theta^2 = q-1-mu.
```

The banked `incidenceBottleneck_mulVec_eq_zero_iff_mu_eq_neg_one` proves
that the only nonprincipal kernel is `mu=-1`.  There the adjacency square is
`q I`.

- If `k` is odd, `q=2^k` is not a rational square.  The `+sqrt(q)` and
  `-sqrt(q)` multiplicities on every rational `mu=-1` primary sector must
  pair, so that sector has trace zero.  The blind spot therefore cannot
  carry any of the required nonprincipal trace `-q`.
- If `k` is even, `sqrt(q)` is integral.  The same argument supplies no sign
  pairing.  A pure blind-spot escape cancelling the principal trace would
  require signed multiplicity imbalance exactly `sqrt(q)` between the two
  adjacency roots.  This is the precise open `mult_D(-1)` / sign-imbalance
  problem recorded in the outline.

The useful missing blind-spot statement is therefore

```text
BLIND-TRACE-ZERO:
  trace(A restricted to ker(D+I)) = 0.
```

It is automatic in the odd-exponent branch and genuinely additional in the
even-exponent branch.  It removes the exact kernel of `E`, but it is **not by
itself a terminal**: designated square-in-eigenfield factors with
`mu != -1` can still contribute trace.  Any account claiming that
BLIND-TRACE-ZERO alone closes `NONBIP-CONNECTED` skips this remaining family.

## Designated-factor alternative

The honest algebraic child is the designated-factor route already isolated
in the outline.  `connectedNonbipartite_designatedFactor_finrank_sq_growth`
forces the intrinsic designated dimension to grow, while all certified
residual sectors have trace zero.  The missing statement is an **upper bound
on the total dimension of square-in-eigenfield factors** strong enough to
prevent their signed traces from summing to `-q`.  This route uses
`A^2=L_D+J` directly and has a terminal; the separator route presently does
not.

## Work-allocation conclusion

Do not extend the separator classification to a new B53 solely to obtain
four-connectivity.  Resume it only if either

- a graph-facing consumer of four-connectivity is stated, or
- a separator lemma also proves the repeated-occupancy packing needed for
  `INCIDENCE-BOTTLENECK-CUBE-UPPER`.

Otherwise the load-bearing targets beneath `NONBIP-CONNECTED` are the
incidence-energy upper bound above or the designated-dimension upper bound.
Within the latter, odd `k` has no `mu=-1` trace escape; even `k` additionally
requires BLIND-TRACE-ZERO or a sharp bound on its signed root imbalance.
