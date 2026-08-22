# A-REG selector-cycle parity audit

Status: divergence-round candidate reduced to an existing interface,
22 August 2026.

For a vertex set `S` (in particular, the vertices of a cycle in a defect
component), define in every target component `c`

```text
z_c(S) = XOR_{x in S} 1_{N_A(x) intersect c}.
```

Concatenating the component blocks gives

```text
(z_c(S))_c = A^T 1_S = A 1_S   over F_2,             (1)
```

because the component supports partition the vertex set and `A` is
symmetric.  Hence the proposed selector-cycle holonomy map is exactly the
adjacency operator restricted to the span of cycle-vertex indicators.  Its
kernel contains no information beyond `ker_F2(A)`.

The banked q=4 fixed-point-free control realizes the reduction sharply.  Its
unique nontrivial `T=A intersect D` cycle is the eight-vertex support of one
whole defect component, and its indicator satisfies

```text
A 1_cycle = 0  over F_2.
```

This is the familiar component-constant adjacency-kernel vector, not a new
holonomy obstruction.

In the connected case, a lower bound on the kernel of (1) would merely be a
lower bound on the mod-two adjacency radical.  The radical/tree/Smith audit
already reaches the exact endpoint: the radical has even dimension at least
two, embeds in the mod-two Laplacian kernel, and only strengthens the lower
bound on `v_2(tau(D))` / the determinant Smith data.  Those data admit the
known controls and do not force rational singularity.

Therefore the XOR selector-cycle map is closed as a distinct mechanism.  A
genuine placement invariant must retain integer multiplicities or the actual
pairing/reuse of selector centers; reducing placements modulo two recovers
only the existing adjacency radical.
