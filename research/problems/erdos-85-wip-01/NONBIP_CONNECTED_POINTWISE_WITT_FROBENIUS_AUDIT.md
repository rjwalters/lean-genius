# NONBIP-CONNECTED pointwise Witt/Frobenius audit

## Proposal

For a root x, let `r_x` be row x of `A^3`.  Its first two power-sum
("ghost") coordinates are

```text
sum_y r_x(y) = q^3,
sum_y r_x(y)^2 = (A^6)_{xx}.
```

The distinguished entry is `r_x(x)=2t_x`.  The divergence-79 proposal asked
whether integrality or enhanced 2-adic divisibility of the length-two Witt
coordinate could force `t_x mod 4` or its A-neighbor mass.

## Exact sixth-walk expansion

Put `c=q-1`, `n=q^2`, and use

```text
A^2 = c I + J - D.
```

Since D is c-regular,

```text
(cI-D)J = J(cI-D) = 0,
J^3 = n^2 J.
```

Therefore

```text
A^6 = ((cI-D)+J)^3 = (cI-D)^3 + J^3.
```

On the diagonal, `D_xx=0` and `(D^2)_xx=c`, so

```text
(A^6)_xx
  = c^3 + 3c(D^2)_xx - (D^3)_xx + n^2
  = (q-1)^2(q+2) + q^4 - (D^3)_xx.
```

Thus the second ghost coordinate contains no isolated ambient triangle term.
Its only rooted variation is `-(D^3)_xx`, twice the number of triangles of the
defect graph through x.  Along a defect edge,

```text
(A^6)_xx-(A^6)_yy = -((D^3)_xx-(D^3)_yy).
```

Connectedness of D does not make D walk-regular or its triangle diagonal
constant; the campaign already records that strong/rank-three children are
not available.

## No enhanced Witt divisibility

For an arbitrary integer vector r,

```text
(sum r_i)^2 - sum r_i^2 = 2 sum_{i<j} r_i r_j.
```

The factor two is universal, but divisibility of `sum r_i` by a high power of
two imposes no stronger valuation on the right side.  For example the vector
`(1,-1,0,...)` has sum zero and sum of squares two.  Hence `sum r_x=q^3`
does not make the second Witt coordinate vanish modulo 4 or 8.  Any stronger
claim must use additional entrywise information about row `A^3`; the square
relation alone supplies exactly the defect-triangle term above.

## Verdict

The pointwise Frobenius/Witt route is **cut**.  It trades the desired ambient
triangle diagonal for the equally uncontrolled defect-triangle diagonal and
has only the universal factor-two integrality.  Ordinary sixth moments erase
the rooted variation after summation, while the pointwise identity retains it
as `diag(D^3)`; neither yields the two sharp terminal congruences.
