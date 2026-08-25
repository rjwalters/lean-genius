# Even-polarity top-band `k=1`: reduction to a pure selector split

## Scope

This is a calibration result for one construction path in Goal #7, not a
plateau-localization theorem and not a constraint on unrelated graphs at
order `q^2`.  The source is the characteristic-two polarity core already
formalized as `Polarity.evenCore K`: delete the absolute line and its nucleus
from the orthogonal-polarity graph.  It is a `q`-regular C4-free graph on
`q^2-1` vertices, where `q=|K|`.

The result does **not** prove that this core has no tight delete-one/add-two
repair.  It proves that for `q>=8` every such repair is forced into one of two
very asymmetric residual forms.  This corrects an initially tempting but
false inference from the mixed-selector count: a selector may consist almost
entirely of the deleted root's neighborhood, in which case that count has no
leverage.

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

C4-freeness gives `|A_0 intersect A_1|<=1` for `f=0` and makes the selectors
disjoint for `f=1`.  Consequently `deg_R(n)<=1` on `L_x`,
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

  The unresolved condition is that this second
  selector (the `q` external endpoints when `a=0`, or the exceptional
  root-neighbor plus `q-1` external endpoints when `a=1`) has no
  common-neighbor conflict after the matching edges are removed.  Thus the
  residual includes both the external-matching and one-cross-endpoint forms.
  When `a=0`, the pure split `A_0=L_x`, `A_1=V(R)` is exactly Card #15
  evidence 105's `k=0`-equivalent matching extension.  It is refuted on both
  `d=4` controls but remains open q-generically at the top-band excess
  `e=q-4`; the low-excess orientation estimates are vacuous here.

* If `f=1`, the selectors are disjoint, so (2) forces `a=0` and makes `R` an
  external matching of `(q-2)/2` edges.  After swapping indices,

  ```text
  A_0 is a (q-1)-subset of L_x,
  A_1 is the remaining point of L_x together with V(R).
  ```

  Every external endpoint must be safe with that one exceptional root
  neighbor, and the external endpoints must be mutually safe after removal.

Therefore:

> **Polarity top-band tight-k1 reduction.**  Let `K` be a finite field of
> characteristic two, `q=|K|`, and `q>=8`.  Any tight delete-one/add-two
> compensated repair of `Polarity.evenCore K` is, up to exchanging the new
> vertices, one of the two pure/near-pure external-matching forms above.

This is sharper than the general exact-boundary estimate `q<=18` for mixed
selectors because it uses the location of the unique polarity common
neighbor.  It does not decide whether either residual external-matching form
exists.  In particular, the first form is the external-matching
conflict-coloring target already isolated in
`COMPENSATED_SURGERY_SCALING_AUDIT.md`.

## Formalization status

`Erdos85PolarityEven.lean` already supplies the source graph, cardinality,
regularity, C4-freeness, and the projective incidence facts behind the mixed
pair bound.  The repository does not yet package the affine chart equivalence
with `K^2\{0}` or a tight compensated-surgery structure expressing (1)-(3).
Those interfaces would be substantially larger than this calibration result,
so this audit records the exact reduction without adding a Lean wrapper.
