# NONBIP-CONNECTED Pfaffian/Plucker audit

Status: algebraic scope cut under `A-REG-NONBIP`, 26 August 2026.

## Proposed invariant

Over `F_2`, a loopless symmetric matrix is alternating.  Round 71 proposed
using its submaximal Pfaffians and their Grassmann--Plucker relations, then
substituting

```text
A^2 = I + J + D  (mod 2)
```

to constrain odd-cycle placements in a connected deficiency graph.

At the proposed mod-2 level this does not refine the existing kernel route.

## Corank dichotomy

Let `A` be alternating of even order `n`, and write

```text
p_ij = Pf(A with rows and columns i,j deleted).
```

Because every row sum of the binary A-REG matrix is zero, `1` belongs to
`ker A`, and alternating rank is even.  Hence `corank A >= 2`.

- If `corank A > 2`, every `(n-2)`-minor has rank below `n-2`, so all
  `p_ij` vanish.  The proposed Plucker package is zero.
- If `corank A = 2`, the Pfaffian adjoint is a nonzero decomposable bivector
  spanning `wedge^2 ker A`.  Since `1` is one kernel vector, choose a second
  vector `w`; after one scalar normalization,

  ```text
  p_ij = 1_i w_j - 1_j w_i = w_i + w_j  (over F_2).
  ```

  The Grassmann--Plucker quadrics are then exactly the tautological
  decomposability relations for `1 wedge w`.  They contain no information
  beyond `Aw=0`.

Squaring the kernel equation gives only

```text
0 = A^2 w = (I + J + D) w,
```

which is the already-audited binary adjacency-kernel shore equation.  The
campaign has exact connected graph controls showing that this equation does
not make `w` component-constant; mod-2 nullity alone was already cut.

The standard Pfaffian expansion and congruence identities supporting this
dichotomy can be found, for example, in Ishikawa and Wakayama's review,
<https://doi.org/10.1016/j.aim.2019.07.006>.

## Exact q=4 calibration

`nonbip_connected_pfaffian_plucker_kernel_control.py` computes all 120
submaximal Pfaffians of the exact fixed-point-free q=4 incidence control.
It verifies

```text
corank_F2(A) = 2,
p_ij = w_i + w_j,
|supp(w)| = 8,
```

where `w` is precisely the indicator of one of the two deficiency
components.  It also checks every four-index Plucker relation directly.
Thus even on a faithful self-polar C4-free incidence structure, the entire
mod-2 cofactor array is just the known kernel shore in different notation.

## Scope cut

The round-71 mod-2 Pfaffian/Plucker proposal is cut.  A genuinely stronger
Pfaffian route would have to retain integral signed Pfaffians or additional
0/1 placement data not determined by the kernel plane.  Merely applying
the characteristic-two cofactor and Plucker identities cannot advance
`NONBIP-CONNECTED` beyond the existing nullity interface.
