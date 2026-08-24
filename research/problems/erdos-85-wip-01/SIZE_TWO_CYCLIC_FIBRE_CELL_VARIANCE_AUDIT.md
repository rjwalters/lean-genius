# Size-two cyclic fibre-to-cell variance audit

## State space

Let `D` be the `q-2` allowed difference fibres and let `K` be the symmetric
cell adjacency matrix.  For a source fibre `t in D` and target cell
`v=(y,u)`, define

```text
n_t(y,u) = number of neighbours of (y,u) whose source lies in fibre t.
```

Equivalently, `n_t(y,u)` is the column sum at `y` of block `A_tu`.

## Exact mean-one laws

Summing the exact target-row hit equation over all `q` source bases `x` in a
fixed fibre `t` gives

```text
sum_(u in D) n_t(y,u) = q-2                         (row)
```

for every target base row `y`: exactly the two sources
`x=y-t` and `x=y-t-1` omit that row.

Likewise, summing the absolute-column hit equation gives

```text
sum_(u in D) n_t(c-u,u) = q-2                       (column)
```

for every absolute target column `c`.  Reciprocity and global degree
`q-2` give the transverse law

```text
sum_(t in D) n_t(y,u) = q-2                         (target cell).
```

Finally `sum_v n_t(v)=q(q-2)` for every source fibre.  Thus the integer array
`n_t(v)` has mean exactly one in each of these labelled partitions and in
the full array.

## Exact variance/collision identity

Put

```text
V = sum_(t,v) (n_t(v)-1)^2.
```

The total number of entries and their total sum are both `q(q-2)^2`, so

```text
V = 2 sum_(t,v) choose(n_t(v),2).                   (1)
```

For fixed `t`, double-counting a target cell together with two sources in
fibre `t` yields

```text
sum_v choose(n_t(v),2)
  = sum_(unordered x,z in fibre t) commonTargets(x,z).
```

The full same-fibre cap bounds every summand on the right by one.  Therefore

```text
0 <= V <= 2(q-2) choose(q,2) = q(q-1)(q-2).         (2)
```

This is an integer, pair-rooted formulation of exactly the information the
cap contributes.  Unlike scalar `tr(K^4)`, it discards all uncontrolled
cross-source-fibre pairs while retaining every fibre/base label.

## Rigid zero-variance branch

If `V=0`, then `n_t(v)=1` for every `t,v`.  Hence every block `A_tu` has
every column sum equal to one.  Applying the same statement to `A_ut` and
using `A_ut=A_tu^T` shows that every row sum of `A_tu` is also one.  Thus:

```text
every A_tu is a permutation matrix;
A_ut=A_tu^T=A_tu^{-1};
every diagonal A_tt is a symmetric loopless permutation,
so A_tt is a perfect matching / fixed-point-free involution.
```

For a source `(x,t)`, the `q-2` block permutations then select exactly one
target in every allowed fibre.  Their target bases cover every row except
`x+t,x+t+1`, while their absolute target columns cover every column except
`x,x-1`.  The zero-variance branch is therefore a self-dual family of
two-hole permutation arrays, not merely an arbitrary collection of
matchings.  This is the correct rigid object for a Hall--Paige or determinant
parity attack.

Full internal support is compatible with this branch: it only asserts
`n_t(x,t)>=1` on the diagonal entries, which become exactly one when `V=0`.

## Zero variance is impossible at the target orders

The rigid permutation family has an elementary labelled sum obstruction.
Fix a source cell `(x,t)`.  For each allowed target fibre `u in D`, let
`y_u` be the unique target base selected by block `A_tu`.  The exact target-
row law says

```text
{y_u : u in D} = Z/q \ {x+t, x+t+1},
```

while the exact absolute-column law says

```text
{y_u+u : u in D} = Z/q \ {x, x-1}.
```

These are equalities of multisets because both sides have `q-2` elements and
the hit multiplicities are exactly one.  Let `Sigma` be the sum of all
elements of `Z/q`.  Summing the two displays in `Z/q` and subtracting gives

```text
sum_(u in D) u
  = (Sigma - x - (x-1))
      - (Sigma - (x+t) - (x+t+1))
  = 2(t+1).                                            (3)
```

The left side is independent of `t`.  Therefore any two allowed fibres
`t,s in D` satisfy

```text
2(t-s)=0 in Z/q.                                       (4)
```

When `q` is even, the kernel of multiplication by two on `Z/q` has exactly
two elements, `0` and `q/2`.  Equation (4) confines all allowed differences
to one antipodal pair, so `|D|<=2`.  But `|D|=q-2`; hence the zero-variance
family is impossible for every even `q>=6`, in particular every binary
target `q=2^k`, `k>=3`.

This proof does not use the value of `sum_(u in D)u`, the hole parameter
`a`, or the cap after zero variance has been reached.  It uses both labelled
affine hit partitions essentially.  It also explains why a scalar or
unlabelled permutation-array bound missed the terminal.

## Missing amplification

Equations (1)--(2) do not contradict a positive `V`.  Integrality alone gives
only `V>=2` after the first deviation, while the cap permits variance of
order `q^3`.  The mean-one row/column laws balance zeros against positive
excess but do not make that excess multiply.

Consequently the no-empty terminal has a sharper remaining target:

1. the `V=0` self-dual two-hole permutation family is excluded by (3)--(4);
   and
2. it remains to prove a **variance amplification** theorem saying any
   nonzero deviation,
   under reciprocity and the two simultaneous affine partitions, exceeds the
   cap upper bound in (2), or else reduces to the rigid family by a
   cap-preserving switch.

The second statement is not currently proved and is the first missing link.
Formalizing (1)--(2) alone would be adjacent infrastructure, so this audit
records the target without opening a Lean lane.
