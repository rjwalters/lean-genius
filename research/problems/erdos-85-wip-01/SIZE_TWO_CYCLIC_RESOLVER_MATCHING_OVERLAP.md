# Size-two cyclic resolver-matching overlap

## Per-base matching

In a cyclic reciprocal code, remove the two internal-edge difference fibers
`0,-1` from the `q-2` allowed fibers.  There remain

```text
n=q-4
```

non-edge fibers.  At each base coordinate `x`, the relative-row-zero route
defines

```text
rho_x(t) = targetDifference(x,t,0).
```

The Lean module `Erdos85SizeTwoCyclicResolverInvolution` proves directly from
reciprocity that `rho_x(rho_x(t))=t`; graph looplessness proves
`rho_x(t)!=t`.  Thus every `rho_x` is a perfect matching on the same set of
`n` fibers.

## Unavoidable matching-edge collisions

For an unordered non-edge-fiber pair `e`, let `m(e)` be the number of bases
whose resolver matching contains `e`.  The `q` perfect matchings have total
edge-incidence mass

```text
sum_e m(e) = qn/2.
```

There are only `C(n,2)=n(n-1)/2` possible edges.  Since
`C(m,2)>=m-1` whenever `m>0`,

```text
sum_e C(m(e),2)
  >= sum_(m(e)>0) (m(e)-1)
  >= qn/2 - C(n,2)
   = 5n/2
   = 5(q-4)/2.
```

This is a uniform row-labelled collision lower bound forced solely by the
five-extra-matchings gap

```text
q-(n-1)=5.
```

It is invisible in the earlier orbit-multiplicity census because that census
forgot which endpoint-color resolver matching produced an incidence.

## What a repeated resolver pair does and does not force

Suppose the same pair `{t,s}` belongs to `rho_x` and `rho_(x+d)`.  The four
exterior cells

```text
(x,t), (x,s), (x+d,t), (x+d,s)
```

contain the two row-resolver edges on the two bases.  Repetition alone is
legal: these are two disjoint edges, not a 4-cycle.

There are two possible cross diagonals.  In routing coordinates they are

```text
targetDifference(x,t,d)       = s,
targetDifference(x+d,t,-d)    = s,
```

with the corresponding target-column equalities understood.  Reciprocity
pairs each diagonal with its reverse.  If both diagonals occur, the four
cells form a 4-cycle.  Equivalently, the same-difference agreement bound at
fiber `t` allows at most one of the two aligned rows `d` and `0`/`-d` to
produce the shared resolver targets.  But neither the row-hit law nor bare
reciprocity currently forces either diagonal to occur.

Thus the new collision lower bound is genuine but not terminal.  A closing
lemma of the following kind would consume it:

> **Resolver-overlap diagonal lemma (open).** Every repeated resolver edge
> across two bases forces at least one cross diagonal, and the resulting
> forced diagonals cannot be assigned injectively under the same-difference
> agreement bounds.

The first clause is not implied by any banked local equation; it is the
precise location gap.  Any proof must use column-resolver data or a second
row-correlated invariant.  Counting repeated matchings without such a
location bridge stops at `5(q-4)/2` and does not recover the missing factor
of `q` in `BinarySizeTwoCyclicPackingBound`.
