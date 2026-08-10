# Stage-1 service spectrum

For every corrected `(4,4,4,4)` Stage-1 witness, the graph
`A = D ∪ S` on the 16 orphan `C12` blocks has the same spectrum.  This is
not an experimental invariance: it follows from a four-column Gram matrix in
each Fourier character of `Z/12`.

Write `tau[o,e]` for the link phase from orphan block `o` to used component
`e`.  At a twelfth root of unity `z`, let `v_e` be the 16-vector whose
`o`-entry is `z^tau[o,e]` when `o` links to `e`, and zero otherwise.  The
Fourier block of the service graph is

```
S_z = sum_e v_e v_e* - 3 I.
```

Indeed, its off-diagonal `(o,p)` entry is the sum of
`z^(tau[o,e]-tau[p,e])` over shared used components, exactly the service
shifts, while the subtracted diagonal removes the three self-incidences.
Adding the orphan-cycle defect graph gives

```
A_z = (z + z^-1 - 3) I + V V*,   V = [v_0 v_1 v_2 v_3].
```

The Stage-1 pair-profile law says that, for each distinct used-component
pair `e,f`, the eight co-linked orphans have phase differences
`tau[o,e]-tau[o,f]` equal to the eight residues not divisible by three,
once each.  Consequently the `4 × 4` Gram matrix `V*V` has diagonal 12 and
constant off-diagonal

```
C(z) = sum_{0 <= r < 12, 3 does not divide r} z^r.
```

Its eigenvalues are `12-C(z)` with multiplicity three and `12+3C(z)` with
multiplicity one.  The remaining twelve eigenvalues of `V V*` are zero.
For `z^12=1`,

```
C(1) = 8,
C(z) = -4  if z != 1 and z^3 = 1,
C(z) = 0   otherwise.
```

Combining the twelve characters yields the exact, phase-independent
spectrum

```
35^1, 12^6, 10^8, 9^8, (9+sqrt(3))^8, (9-sqrt(3))^8,
7^4, 3^3, (-1)^12, (-2)^24, (-3)^24, (-4)^26, (-5)^12,
(-3+sqrt(3))^24, (-3-sqrt(3))^24.
```

For an H-lift, the common-neighbor equations give
`H^2 = 12 I + J - A`.  Hence the spectrum of `H^2` is fixed as well: 169
on the all-ones line and, on its orthogonal complement,
`12 - lambda(A)`.  The rational H-eigenvalue sign imbalances

```
a = mult_H(4) - mult_H(-4),
b = mult_H(3) - mult_H(-3)
```

are forced by `tr(H)=0` and `tr(H^3)=6*328=1968` to `a=-4`, `b=1`.
This is consistent, so the first and third moments alone are not the final
contradiction, but all further analytic work may start from this fixed
factorization rather than quantify over the service phases.
