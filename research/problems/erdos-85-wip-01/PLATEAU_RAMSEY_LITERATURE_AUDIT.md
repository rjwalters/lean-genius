# Plateau-to-boundary: Ramsey literature audit

Status: bounded outside pass for Goal #7, 25 August 2026.  The classical
star--quadrilateral results stop exactly one vertex short of the plateau
claim; no theorem found closes the gap.

## Translation

Let a hypothetical plateau witness have minimum degree `d` and order

```text
m = d(d-1) + 3 + e,       0 <= e <= d-4.
```

Put `q=d-1`.  Then

```text
m = q^2 + q + 3 + e.
```

Its complement has maximum degree at most `m-1-d`, hence contains no star
with

```text
n = m-d = q^2 + 2 + e
```

leaves.  Thus existence of the plateau witness is exactly the lower-bound
assertion

```text
R(C4,K_{1,n}) > m.                                      (P)
```

This is the useful dictionary for importing star--quadrilateral Ramsey
results into Goal #7.

## The one-vertex wall

Parsons' general bound is

```text
R(C4,K_{1,n}) <= n + ceil(sqrt(n)) + 1.
```

Throughout the displayed plateau band,

```text
n = q^2+2+e,     ceil(sqrt(n)) = q+1,
```

so Parsons gives

```text
R(C4,K_{1,n}) <= q^2+q+4+e = m+1.                       (Q)
```

Consequently the standard theorem misses the contradiction to `(P)` by
exactly one vertex, uniformly in `e`.  This is not a loose asymptotic
comparison: it identifies the plateau band with the unresolved equality
side of the sharp general Ramsey bound.

The exceptional Parsons improvement occurs at `n=q^2+1`:

```text
R(C4,K_{1,q^2+1}) = q^2+q+2
```

for prime-power `q`.  In plateau coordinates this is `e=-1`, the order just
below the Goal #7 interval.  The surveyed exact families for
`n=q^2-t` likewise lie on the lower side of the square and do not include
`n=q^2+2+e`.

Therefore citing the classical exact values does not prove even the `e=0`
plateau case.  What would suffice is the one-unit strengthening

```text
R(C4,K_{1,q^2+2+e}) <= q^2+q+3+e                       (R)
```

on the required `q,e`; but `(R)` is the plateau nonexistence statement in
Ramsey notation, not an available black box.

## Why polarity stability does not immediately bridge it

Writing `N=q^2+q+1`, the plateau witness has `N+2+e` vertices and minimum
degree `q+1`.  The He--Ma--Yang stability theorem applies instead to
`C4`-free graphs on exactly `N` vertices whose edge count lies in a narrow
window below the polarity extremum.  Deleting `2+e` vertices from a
minimum-degree witness gives no suitable upper control on the deleted
degrees, and even an average-degree deletion loses order `(2+e)q` edges,
outside the published near-extremal window already at `e=0`.  No direct
localization theorem from that paper supplies the missing one-unit Ramsey
improvement.

## Disposition

The literature pass is negative but sharp:

* near-Moore/girth-five excess theory is inapplicable because plateau
  witnesses may contain triangles;
* polarity stability is at the adjacent order and requires substantially
  tighter edge control;
* star--quadrilateral Ramsey theory translates exactly, but its general
  upper bound is `m+1` where Goal #7 needs `m`.

Accordingly the next mechanism must use plateau-specific information beyond
minimum degree and `C4`-freeness (for example the `hnext` non-extension
hypothesis or a controlled deletion/surgery).  Repackaging Parsons' bound or
the known prime-power exact values cannot close Goal #7.
