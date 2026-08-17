# A-REG: the owner-coordinate algebra

Status: exact derivation from the proved component quotient and owner-graph
interfaces, 2026-08-17. This note targets the sole remaining binary
square-order gap after `squareOrder_regular_of_even` closed A-NONREG.

## 1. Setup

Let `G` be q-regular and C4-free on `q²` vertices, with q even, and let `D`
be its second-order defect graph. Write the connected components of `D` as
`c`, with

```text
|c| = q m_c,             sum_c m_c = q.
```

Let `A` be the adjacency matrix of `G`, let `P_c` be the diagonal projector
onto `c`, and let `O_c` be the owner graph for coordinate `c`. The proved
entrywise Gram formula is

```text
M_c := O_c + m_c I = A P_c A.
```

Each `O_c` is `m_c(q-1)`-regular, and the owner graphs edge-partition the
complement of `D`.

## 2. Cross-product identity

For distinct components `c != d`, the matrices satisfy

```text
M_c M_d = m_c m_d J.                         (OWNER-CROSS)
```

Indeed,

```text
M_c M_d = A P_c A² P_d A.
```

Insert the square-order identity

```text
A² = (q-1)I + J - D.
```

The `I` term vanishes because `P_c P_d=0`. The `D` term vanishes because `D`
has no edges between distinct connected components, hence `P_c D P_d=0`.
For the remaining term, `P_c J P_d = 1_c 1_d^T`, while the uniform component
quotient gives

```text
A 1_c = m_c 1,             A 1_d = m_d 1.
```

Thus the product is `m_c m_d J`.

Expanded in owner adjacency matrices, this is

```text
O_c O_d + m_d O_c + m_c O_d + m_c m_d I = m_c m_d J.   (1)
```

In particular all `O_c` commute pairwise. They also commute with `D`, since
`A`, `D`, and every component projector `P_c` commute in the required order.
The regular A-REG core therefore carries a simultaneous symmetric matrix
algebra, not merely an edge coloring.

## 3. Simultaneous spectral form

On the hyperplane `1^perp`, `J=0`, so OWNER-CROSS becomes

```text
(O_c + m_c I)(O_d + m_d I) = 0               (c != d).  (2)
```

Choose a simultaneous real eigenvector `v` in `1^perp`, and write `lambda_c`
for its `O_c`-eigenvalue. Then

```text
(lambda_c + m_c)(lambda_d + m_d) = 0          (c != d).  (3)
```

Hence at most one coordinate can have `lambda_c != -m_c`. This is the exact
spectral sparsity missing from the component-size partition alone.

Since the owner graphs partition the complement of `D`,

```text
sum_c O_c = J - I - D.
```

If `delta` is the simultaneous `D`-eigenvalue, then on `1^perp`

```text
sum_c lambda_c = -1-delta.
```

For a vector exceptional only in coordinate `e`, this gives

```text
delta = q - m_e - 1 - lambda_e.               (4)
```

The vectors with no exceptional coordinate have `lambda_c=-m_c` for all c
and therefore `delta=q-1`; these include the `(number of components)-1`
dimensional space of component-constant vectors orthogonal to `1`.

## 4. Exact moments and rank pressure

Because `O_c` is a loopless `m_c(q-1)`-regular graph on `q²` vertices,

```text
tr(M_c)   = m_c q²,
tr(M_c²)  = q² [m_c(q-1) + m_c²].
```

The all-ones eigenvalue of `M_c` is `m_c q`. Removing it leaves

```text
tr(M_c | 1^perp)    = m_c q(q-1),
tr(M_c² | 1^perp)   = m_c q²(q-1).             (5)
```

Moreover `M_c=A P_c A` is positive semidefinite. If `r_c` is its rank on
`1^perp`, Cauchy applied to its positive eigenvalues gives

```text
r_c >= m_c(q-1).                              (6)
```

By (2), the positive ranges of the different `M_c` on `1^perp` are mutually
orthogonal. Summing (6) yields

```text
sum_c r_c >= q(q-1).
```

Thus at least `q²-q` dimensions of `1^perp` are consumed by mutually
orthogonal owner-coordinate ranges; at most `q-1` dimensions remain in their
common kernel. Equality in (6) would force every positive nontrivial
eigenvalue of `M_c` to equal `q`.

## 5. Precise next statements

The immediate Lean target is OWNER-CROSS, followed by pairwise commutation.
Both are uniform structural theorems and use no finite certificate.

The remaining mathematical terminal can now be stated narrowly:

**GAP A-REG-OWNER-SPECTRUM.** Show that no family of simple regular owner
graphs with positive parts `m_c>=2`, `sum m_c=q=2^k`, can satisfy (1), the
owner edge partition, and the component-selector intersection laws.

Promising consumers are:

1. strengthen (6) to equality using the rank of `A P_c A` and the known
   `q m_c`-dimensional component coordinate;
2. use integrality/algebraic conjugacy of the exceptional spectra in (3)-(4);
3. combine the forced large multiplicity of eigenvalue `-m_c` in each `O_c`
   with trace-cube/triangle counts;
4. reduce the `m_c=2` case by inserting the already proved cycle quotient and
   selector-disjointness representation into (1).

This is now the highest-level open node in Track A.
