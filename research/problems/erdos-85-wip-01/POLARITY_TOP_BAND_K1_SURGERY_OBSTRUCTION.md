# Even-polarity top-band `k=1`: no delete-one/add-two repair

## Scope

This is a calibration result for one construction path in Goal #7, not a
plateau-localization theorem and not a constraint on unrelated graphs at
order `q^2`.  The source is the characteristic-two polarity core already
formalized as `Polarity.evenCore K`: delete the absolute line and its nucleus
from the orthogonal-polarity graph.  It is a `q`-regular C4-free graph on
`q^2-1` vertices, where `q=|K|`.

For `q>=8` this core has **no** tight delete-one/add-two repair preserving
q-regularity and C4-freeness. The mixed-selector count reduces a possible
repair to a pure selector split; the triangle through each removed matching
edge then excludes that split. This closes the previously open residual
in this audit (2026-09-06). It does not exclude larger surgeries or
unrelated q-regular graphs on q² vertices.

The subsequent `POLARITY_BOUNDED_SURGERY_OBSTRUCTION.md` extends the
construction-side exclusion: deleting k vertices and adding k+1, while
only removing survivor edges, requires `q<=3k²+5k`. If ell>0 old-old
edges are inserted, it instead requires `q<=2ell+k²+3k+2`. Thus bounded
edit counts cannot scale to unbounded q. The present k=1 argument has
the sharper threshold q>=8 when no old-old edges are inserted.

## Affine symplectic coordinates

Take the absolute line to be

```text
ell = { (X0:X1:X2) : X0+X1+X2=0 }
```

and its nucleus to be `N=(1:1:1)`.  Normalize every point outside `ell` to
have coordinate sum one and translate the affine plane by `N`.  The surviving
vertices identify with

```text
V = K^2 \ {0},
u ~ v  iff  omega(u,v)=1,
omega((a,b),(c,d))=ad-bc.
```

In characteristic two `omega` is symmetric.  For nonzero `x`, its
neighborhood is the affine line

```text
L_x = {n : omega(x,n)=1}
```

of cardinality `q`.  Distinct `u,v` have a common neighbor exactly when they
are linearly independent, and then it is the unique solution of
`omega(u,z)=omega(v,z)=1`.

## Tight one-root normal form

Delete a root `x`, delete an arbitrary set `R` of survivor edges, and add new
vertices `w0,w1`.  Let `f` be the indicator of the gadget edge `w0w1`, and
let `A_i` be the old-neighbor selector of `w_i`.  If the result is
`q`-regular, then

```text
|A_i| = q-f,                                             (1)
1_{v in A_0}+1_{v in A_1}
  = 1_{v in L_x}+deg_R(v),                              (2)
2|R| = q-2f.                                            (3)
```

C4-freeness gives `|A_0 intersect A_1|<=1` for **both** values of f.
The earlier version incorrectly asserted disjointness when f=1; a single
shared neighbor only forms a triangle with the gadget edge. The weaker
bound is sufficient below. Consequently `deg_R(n)<=1` on `L_x`,
`deg_R(y)<=2` off `L_x`, and at most one vertex has multiplicity two.

If an external vertex `y` has `R`-degree two, it is the unique common selector
vertex.  Then no point of `L_x` is `R`-incident, since that would create a
second selector intersection.

## Mixed-pair bound

Fix `y notin L_x` and `n in L_x` occurring in the same selector.  If `y,n`
are dependent, they were already safe, and there is at most one such `n`.
Otherwise let `z` be their unique common neighbor.  It is not the deleted
root `x`, because `y notin L_x`.  The pair can become safe only if `yz` or
`nz` belongs to `R`.

For a fixed removed neighbor `z` of `y`, at most one `n in L_x` satisfies
`omega(n,z)=1`.  This is a second affine-linear equation on `L_x`; the only
constant-one exception would be `z=x`, already excluded.  If every external
vertex has `R`-degree at most one, at most one point of `L_x` is itself
`R`-incident, because such a point is the unique possible selector
intersection.  Therefore every external selector vertex coexists with at
most

```text
1 dependent point + 1 point relieved through its R-mate
                  + 1 R-incident point of L_x = 3 points of L_x.       (4)
```

If instead a unique external vertex `y` has `R`-degree two, it belongs to
both selectors and their `L_x` parts are disjoint.  All `q` points of `L_x`
must coexist with `y` across those two selectors, but only the dependent
point and the at most two solutions supplied by the two removed neighbors
can do so.  Hence this case forces `q<=3`.

## The residual forms

Assume now that external `R`-degree is at most one.  Put

```text
a = sum_{n in L_x} deg_R(n) <= 1,
r_i = |A_i \ L_x|.
```

Equations (1)-(3) give

```text
r_0+r_1 = q-2f-a.                                       (5)
```

If both `r_i` are positive, (4) gives
`r_i >= q-f-3` for each selector.  Together with (5),

```text
2(q-f-3) <= q-2f-a,
q <= 6-a <= 6.                                          (6)
```

Thus for `q>=8` one selector has no external vertex.  Equations (1)-(3) now
determine the remaining possibilities.

* If `f=0`, after swapping indices,

  ```text
  A_0 = L_x,
  a is 0 or 1,
  R is a matching of q/2 edges with exactly a endpoints in L_x,
  A_1 = V(R).
  ```

  In particular every endpoint of every R-edge belongs to A_1, including
  the possible shared root-neighbor when a=1.

* If `f=1`, R is a matching of `(q-2)/2` edges with a root-neighbor
  endpoints, where a is 0 or 1. After swapping indices,

  ```text
  A_0 is a (q-1)-subset of L_x,
  A_1 is the remaining point of L_x together with V(R),
  |A_1 intersect L_x| = 1+a.
  ```

  The possible root-neighbor endpoint of R lies in both selectors; the
  root-neighbor omitted from A_0 is not R-incident, by (2). Again, all
  endpoints of every R-edge belong to A_1.

## The matching-edge triangle closes both residuals

If uv is an edge of the characteristic-two core, then `z=u+v` is a
nonzero vertex distinct from u and v, and

```text
omega(u,z)=omega(u,u+v)=1,
omega(v,z)=omega(v,u+v)=1.
```

Thus uv lies in the triangle uvz. Take any edge uv of the matching R.
Both endpoints lie in A_1. If z is not the deleted root x, the edges uz
and vz survive: neither can lie in R because R is a matching already
containing uv. Then `w1-u-z-v-w1` is a C4, contradiction. Therefore
every R-edge must have `u+v=x`. But this implies
`omega(x,u)=omega(x,v)=1`, so **both** its endpoints lie in L_x.

The residual forms have at most one R-endpoint in L_x in total. Hence R
has no edge. This contradicts `|R|=(q-2f)/2>0` for q>=8.

We obtain:

> **Polarity top-band tight-k1 exclusion.** Let `K` be a finite field of
> characteristic two, `q=|K|`, and `q>=8`.  Any tight delete-one/add-two
> compensated repair of `Polarity.evenCore K` fails q-regularity or
> C4-freeness. Survivor edges may be removed arbitrarily; both choices of
> the edge between the two new vertices are covered.

The same triangle observation rules out delete-zero/add-one repair by
removing a matching from this core: regularity forces a matching of q/2
edges whose endpoints all attach to the new vertex, and the old triangle
vertex is never deleted. This addresses the polarity-core specialization
of the external-matching target in `COMPENSATED_SURGERY_SCALING_AUDIT.md`,
not that target for arbitrary source graphs or larger deleted sets.

## Formalization status

`Erdos85PolarityEven.lean` already supplies the source graph, cardinality,
regularity, C4-freeness, and the projective incidence facts behind the mixed
pair bound.  The repository does not yet package the affine chart equivalence
with `K^2\{0}` or a tight compensated-surgery structure expressing (1)-(3).
Those interfaces would be substantially larger than this calibration result,
so this audit records the exact reduction without adding a Lean wrapper.
