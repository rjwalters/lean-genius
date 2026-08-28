# NONBIP-CONNECTED Baer prime-walk audit

Date: 2026-08-27. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **new exact residue, no terminal consumer**.

## Why this audit was opened

The classical fixed-point theorem for a polarity of a finite projective
plane has a short graph proof using prime-length closed walks.  If the
polarity were fixed-point-free, cyclic rotation partitions the closed walks
of prime length `p` into orbits of size `p`; the projective-plane square
identity gives a conflicting residue when `p` divides the plane order.

Our self-polar square configuration has the corrected identity

```text
A^2 = (q-1)I + J - D,                                  (1)
```

so the same argument does not immediately contradict fixed-point-freeness.
This audit records exactly what replaces the projective-plane contradiction.
The calculation is useful because it is global and entrywise at once: its
correction term counts mixed ambient/defect walks, rather than another shore
cut or spectrum-only scalar.

## Exact prime-walk residue

Assume that `A` is a symmetric zero-one matrix with zero diagonal, constant
row sum `q`, and (1), where `D` is the `(q-1)`-regular defect adjacency
matrix.  Let `p` be an odd prime divisor of `q-1`, and put
`r=(p-1)/2`.  Work modulo `p`.

The matrices `A`, `D`, and `J` commute.  Moreover

```text
JD = DJ = (q-1)J = 0,
J^2 = q^2 J = J.                                      (2)
```

Consequently the mixed binomial terms vanish and

```text
A^p = A(A^2)^r
    = A(J-D)^r
    = AJ + (-1)^r A D^r.                              (3)
```

For every integer matrix, cyclic rotation of index words gives
`tr(A^p) = tr(A) (mod p)`: all nonconstant closed walks occur in orbits of
size `p`, and the constant words contribute the diagonal entries.  Here both
traces are zero.  On the other hand `AJ=qJ`, so

```text
tr(AJ) = q * tr(J) = q^3 = 1 (mod p).
```

Taking traces in (3) therefore forces

```text
tr(A D^r) = (-1)^(r+1) (mod p).                       (4)
```

Thus the missing defect term does not merely spoil Baer's proof: it must
carry one prescribed nonzero residue.

## Calibration and first cases

For `p=3`, equation (4) is

```text
tr(AD) = 1 (mod 3).
```

Since `tr(AD)=2|E(A) intersect E(D)|=2|T|`, the fixed-free `q=4`
control with `T=C8` gives `16=1 (mod 3)`, exactly as required.  This explains
arithmetically how the control evades the classical projective-plane proof.

For binary `q=2^k` with `k>=3`, `q-1` always has a prime divisor at least
five (if all prime divisors were three, `2^k-1` would be a power of three,
which occurs here only at `k=2`).  Hence the binary range always supplies a
genuinely higher mixed moment:

```text
p=5  -> tr(A D^2) = -1 (mod 5),
p=7  -> tr(A D^3) =  1 (mod 7),
...
```

A primitive prime divisor of `2^k-1`, when available, makes the choice
explicitly sensitive to `k`.  It is not uniform without an exception:
Zsigmondy's exceptional exponent `k=6` has no primitive prime divisor, so a
proof must not assume one for every `k>=3`.  The weaker `p>=5` choice has no
such gap.

## Graph-facing meaning

`tr(A D^r)` counts oriented closed mixed walks consisting of one ambient
`A`-edge followed by an `r`-step defect walk back to its start.  For the
first new case,

```text
tr(A D^2)
  = 2 * sum_{xy in E(A)} |N_D(x) intersect N_D(y)|.   (5)
```

This first case already has a stronger C4-sensitive reduction in Lean.
Write `D=C+T`, where `C` is the antipodal graph (nonpairs with no common
ambient neighbor) and `T` is the graph of ambient edges lying in no
triangle.  The theorem

```text
trace_adj_mul_secondOrderDefect_sq_eq_antipodal_sq
```

in `Erdos85DefectSecondMixedMoment.lean` proves

```text
tr(A D^2) = tr(A C^2)
          = 2 * sum_z e_A(N_C(z)).                      (6)
```

Indeed the three other color words `ACT`, `ATC`, and `ATT` vanish: an
ambient edge cannot close a triangle with an antipodal edge and a
triangle-free edge, nor with two triangle-free edges.  Thus when `p=5`,
the prime-walk residue is the exact antipodal-service congruence

```text
2 * sum_z e_A(N_C(z)) = -1 (mod 5).                    (7)
```

This is the first genuinely independent consumer interface.  Re-expanding
`D` or recomputing the fifth moment cannot contradict (7); one needs a new
restriction on the ambient edges induced inside antipodal neighborhoods.

Equation (4) therefore asks a location question in the same spirit as the
canonical transport `K`: defect-walk endpoints must land on ambient edges
with a prescribed nonzero prime residue.  Unlike determinant or ordinary
trace data, it retains the actual overlap of the two relations.

## Bounded verdict

The exact calculation does **not** yet close `NONBIP-CONNECTED`.  None of the
banked connectedness, C4-free, Eulerian-transport, or dyadic-shore theorems
forces the left side of (4) to vanish modulo `p`.  For `p>=7` it is a higher
mixed walk count with no current local capacity bound; for `p=5`, (5) is
concrete, reduces further to the antipodal service count (6), but applies
only when `4 | k`.  The earlier `H7_R_MOD5_CONSUMER_AUDIT.md` independently
warns against treating this residue as a mask- or moment-only obstruction:
its next input also had to be a genuinely C4-sensitive restriction on the
same overlap statistic.

Therefore no Lean wrapper should be opened yet: (4) follows formally from
the same square identity until a graph-facing consumer proves an incompatible
residue or valuation.  The surviving research question is precise:

> Does connectedness of `D`, together with C4-freeness and the canonical
> cross-neighborhood matching law (21), force
> `tr(A D^((p-1)/2)) = 0 (mod p)` for some prime `p | q-1`, or otherwise
> constrain its edgewise summands enough to contradict (4)?

This is a new candidate interface, not a claimed advance on the status of
the root node.
