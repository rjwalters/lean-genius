# NONBIP-MIXED even exterior-carrier audit

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED`, the even-weight
two-component siblings `[6,2]` and `[4,4]` at `q=8`.

Status: exact norm/Bockstein identity; scalar mod-4 route cut.

## Setup

Use the block notation of
`NONBIP_MIXED_EXTERIOR_SELF_INDEX_TRANSPORT_AUDIT.md`.  Thus `C,F` have
orders `qm,qn`, respectively,

```text
B = A_G[C,F],
```

and `B` has row sum `n` and column sum `m`.  Let `Q` be the vertex set of an
induced odd cycle of length `ell` in `D_C`, put `x=1_Q` over the integers,
and set

```text
y = B^T x.
```

Every coordinate `y_f` is the number of `G`-neighbors of `f` on the cycle,
so `0 <= y_f <= m` and

```text
sum_f y_f = n ell.                                      (1)
```

## The norm is exactly an owner-edge census

The cross-incidence Gram block is

```text
B B^T = n I + O_F[C,C],                                 (2)
```

where `O_F` is the owner graph of component `F`.  Therefore

```text
||y||^2 = x^T B B^T x
        = n ell + 2 e_F(Q),                              (3)
```

with `e_F(Q)` the number of `F`-owned edges induced by the cycle vertices.
Equivalently, the first integral Bockstein after removing the forced total
is not a new invariant:

```text
(||y||^2 - sum_f y_f) / 2
  = sum_f choose(y_f,2)
  = e_F(Q).                                               (4)
```

Thus for even `n`, reducing the norm modulo four gives only the parity of an
existing owner-edge count:

```text
||y||^2 = n ell + 2 e_F(Q)                 (mod 4).       (5)
```

There is no parity contribution from the odd cycle beyond `n ell`.

The diagonal component equation supplies the complementary tautology.  If
`H_C=A_G[C,C]`, then

```text
H_C^2 + B B^T = (q-1)I + J - D_C,
```

and, because `x^T D_C x=2 ell`,

```text
||H_C x||^2 = ell^2 + (m-3)ell - 2e_F(Q).                (6)
```

Subtracting `sum H_Cx=m ell` and dividing by two says only

```text
sum_c choose((H_Cx)_c,2)
  = ell(ell-3)/2 - e_F(Q),                               (7)
```

the number of complementary chords owned by `C`.  Equations (4) and (7)
partition the `ell(ell-3)/2` non-cycle pairs of an induced cycle by their
unique owner color; they create no residue.

## Faithful `q=4`, `[2,2]` calibration

Direct enumeration of `sixteenRegular` gives eight induced 5-cycles in each
defect component.  For every one of the sixteen oriented component/cycle
choices, the exterior carrier has sorted coordinate profile

```text
(1,1,1,1,1,1,2,2).
```

Hence `sum y=10`, `||y||^2=14=6 (mod 8)`, and

```text
(14-10)/2 = 2 = e_F(Q).
```

The known exception therefore satisfies the norm identity sharply; neither
mod four nor mod eight produces a contradiction.

## Arithmetic flexibility at the order-64 even strata

Even before imposing the transported boundary equation, the forced total,
coordinate bound, and norm Bockstein permit both owner-edge parities.
For `ell=5`, explicit sorted carrier profiles are:

```text
[6,2], C weight 6, exterior n=2, |F|=16, y_f<=6:
  even e_F:  0^6, 1^10
  odd  e_F:  0^7, 1^8, 2

[6,2], C weight 2, exterior n=6, |F|=48, y_f<=2:
  even e_F:  0^18, 1^30
  odd  e_F:  0^19, 1^28, 2

[4,4], exterior n=4, |F|=32, y_f<=4:
  even e_F:  0^12, 1^20
  odd  e_F:  0^13, 1^18, 2.
```

In every row the two profiles have the same forced total `n ell`; inserting
one coordinate of value two changes the Bockstein parity.  These are scalar
profiles, not block-matrix models, so they do not refute a consumer of the
full simultaneous transport equations.  They do prove that no conclusion
about `e_F(Q) mod 2` follows from carrier weight, coordinate bounds, and
`||B^T x||^2` alone.

## Disposition

The proposed mod-4/8 norm route reduces exactly to owner-edge parity and is
cut at that interface.  This agrees with the earlier instruction to stop if
the Bockstein contains no information beyond the owner census.

The even-weight strata require a genuinely vector-valued second layer: use
the exact equation `D_F y=B^T D_Cx` (or its integral lift) together with
`H_Fy+B^TH_Cx=1`, rather than another scalar moment of `y`.  In particular,
the odd-total shortcut available for `[5,3]` has no even-weight analogue in
the first norm or first Bockstein.
