# NONBIP-CONNECTED punctured double-cover probe (q=4)

## Proposal

Try to realize the rooted Sachs residue through perfect matchings of the
bipartite double cover of the ambient graph after deleting both lifts of the
root.  The count is

```text
permanent(A with row and column x deleted).
```

An Arf/Kasteleyn refinement would have to extract a root-independent 2-adic
residue from this count.

## Exhaustive calibration sample

The exact subset-DP probe
`nonbip_connected_punctured_double_cover_q4.py` was run on 256 labelled q=4
models, hence 4096 rooted samples:

```text
python3 research/problems/erdos-85-wip-01/nonbip_connected_punctured_double_cover_q4.py \
  --models 256 --modulus 65536
```

Output:

```text
triangle degree 1: permanent = 3928
triangle degree 2: permanent = 4120
```

Thus the raw permanent is not root-independent, even though the desired Sachs
residue is uniform on the same corpus.  Modulo 256 the two values are 88 and
24; both vanish modulo 8.  The apparent raw mod-8 invariant is therefore only
divisibility and carries no rooted information.

There is an exact q=4 affine calibration:

```text
permanent(A_xhat) - 192 * t_x = 3736.
```

This is reproducible across all 4096 samples, but at q=4 the corpus has only
the two saturated rooted profiles.  No square-order or C4-free argument is
known that produces the coefficient 192 at general q.  General
permanent--determinant congruences for symmetric zero-diagonal matrices explain
only very low 2-adic precision; they do not force this correction.  The
published "graph permanent" vertex-deletion invariance for even-regular graphs
uses a repeated signed incidence matrix, not this adjacency permanent, so it
does not apply here.

## Verdict

The **raw** punctured-double-cover matching/Arf proposal is cut: its count
distinguishes triangle degree rather than the uniform target.  The
triangle-corrected q=4 equality is retained as calibration, not promoted to a
mechanism.  Reopening it requires a precise q-generic congruence for
`permanent(A_xhat)` with a derived correction term; further q=4 matching
enumeration would only measure saturation.
