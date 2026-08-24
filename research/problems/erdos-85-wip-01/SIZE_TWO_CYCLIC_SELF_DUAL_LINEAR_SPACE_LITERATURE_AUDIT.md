# Self-dual partial-linear-space literature audit

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## Proposed translation

Fix the empty fibre `T`.  Use its `q` cells as points and, for every outside
target cell `w`, use

```text
L_w = N(w) intersect T
```

as a block.  The full cap on `T` says that two points occur together in at
most one `L_w`, so this is a partial linear space (a linear hypergraph).
The empty-fibre collision theorem gives

```text
sum_w binom(|L_w|,2) >= q.
```

Because the ambient adjacency is symmetric, it is tempting to call this a
self-dual partial linear space and apply Fisher or de Bruijn--Erdos, with the
owner-cycle endpoint as the polygon equality case.

## The induced incidence structure is not self-dual

Reciprocity maps an incidence

```text
x in L_w    (equivalently x adjacent to w)
```

to the same ambient edge read backwards.  It sends the block label `w` to
the ambient point `w`, which lies outside `T`; it does **not** send it to one
of the `q` points of the induced structure.  The parameters already expose
the mismatch:

```text
points:       q,
block labels: q(q-3).
```

Zero and singleton blocks may be discarded, but their number is not fixed
and there is no resulting bijection between points and nontrivial blocks.
Closing under the polarity restores the entire `q(q-2)`-cell configuration,
not a self-dual geometry on the owner graph.

Thus the extra hypothesis needed by a dual Fisher argument is exactly the
missing global-merger theorem in another form: one would first have to select
a polarity-stable set of collision blocks of size `q` (or otherwise close
the owner cycle under reversal) while retaining pair labels.  Generic
duality does not make this selection.

## Why the classical inequalities do not apply

Fisher's inequality is useful for a pairwise balanced design because every
pair of points is covered (or because the incidence Gram has a prescribed
positive off-diagonal part).  The de Bruijn--Erdos finite-linear-space
theorem likewise assumes that every two points determine a line.  Here the
cap supplies the opposite half:

```text
every point pair is covered at most once.
```

The banked lower bound covers only at least `q` of the `binom(q,2)` pairs.
A polygon on the q points, with one two-point block per cycle edge and the
remaining incidences in singleton blocks, meets this endpoint.  This is the
same valid cycle incidence realization recorded in the block-Gram audit.
Neither Fisher nor de Bruijn--Erdos excludes it.

Uniform-block partial-geometry and semipartial-geometry theorems also require
intersection numbers absent here.  The earlier repository audit
`NONBIP_CONNECTED_SELFPOLAR_TRANSLATION.md` identifies the exact analogous
promotion gaps for the full configuration: constancy of defect codegrees and
a two-valued cubic entry law.  It also records fixed-point-free self-polar
semipartial examples, so polarity alone is not an absolute-point terminal.
The present induced collision hypergraph has still less uniformity: its block
sizes `|L_w|` vary and may be zero.

The survey of symmetric configurations cited in that audit (Davydov--Faina--
Giulietti--Marcugini--Pambianco, arXiv:1203.0709) gives many parameter-valid
self-dual configurations but no theorem forcing a sparse induced group to be
closed under the polarity.  The Debroey--Thas polarity bounds cited there
assume semipartial intersection laws and therefore also start after the
missing promotion step.

## Matrix form of the failed Fisher step

Let `A` be the incidence matrix from `T` to outside cells.  The cap says

```text
offdiag(A A^T) is a zero-one matrix B.
```

Fisher's standard rank proof needs a Gram matrix whose off-diagonal entries
are fixed and positive.  Here `B` is an arbitrary simple owner graph subject
to `|E(B)| >= q`.  The allowed endpoint `B=C_q` makes

```text
A A^T = (q-2)I + C_q
```

positive definite for `q>=8`, so the rank argument is satisfied with strict
room rather than contradicted.  Applying the same rank argument to `A^T A`
only changes which sparse column pairs are compared; it does not turn the
rectangular induced incidence into a symmetric design.

## Verdict

The direct dual Fisher / de Bruijn--Erdos route is **cut before its equality
classification**.  The collision hypergraph is linear but neither a finite
linear space nor self-dual on its induced point set.  Classical hypotheses
would have to be supplied by a new polarity-stable closure theorem, and that
closure is essentially the live global-merger problem.

A geometry revival must retain the full ambient polarity and prove a
code-specific closure of the q-edge owner cycle under reversal.  Calling the
induced hypergraph self-dual, or applying a scalar incidence-rank inequality,
silently assumes that missing step.
