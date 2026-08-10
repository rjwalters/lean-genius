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

## Cube-root kernel and the omitted-type quotient

At either nontrivial cube root `z`, the four Fourier columns `f_e` satisfy
`sum_e f_e = 0` and span the three-dimensional `A`-eigenspace at 12.
Since `H` is symmetric and `H^2` vanishes there, `H f_e = 0`.  For every
vertex and used component `e`, its H-neighbors in blocks linked to `e`
therefore split equally among the three colors `x+tau[o,e] mod 3`.

Let `r_e(v)` count H-neighbors of `v` in the 48 vertices whose blocks omit
`e`.  Since H has degree 13, the kernel balance says

```
r_e(v) = 1 mod 3,        sum_e r_e(v) = 13.
```

The possible unordered profiles are initially
`[10,1,1,1]`, `[7,4,1,1]`, and `[4,4,4,1]`.  They are separated by an
exact cherry count.  Inside one omitted-type class there are 48 defect
edges and `6*3*12 = 216` service edges.  Thus exactly

```
binom(48,2) - 264 = 864
```

pairs have one H-common-neighbor, and
`sum_v binom(r_e(v),2) = 864`.  Summing over the four types gives 3456.
The three profiles contribute respectively 45, 27, and 18 to the local
four-type cherry sum; because `3456 = 192*18`, equality forces
`[4,4,4,1]` at every vertex.  For each `e`, exactly 48 vertices have
`r_e(v)=1`; call that sparse fiber `X_e`.

Write `O_e` for the omitted-type classes and identify a class with its
indicator vector.  The profile law is

```
H O_e = 4*1 - 3*X_e.
```

The service construction also gives `A O_e = 8*1 + 3*O_e`.  Applying
`H^2 = 12I+J-A` to `O_e` then gives the dual identity

```
H X_e = 4*1 - 3*O_e.
```

Both balanced four-partitions therefore have the same three-dimensional
contrast space, namely the entire `H^2=9` eigenspace.  Equality of the
indicator spaces implies `X_e = O_{pi(e)}` for a permutation `pi`.
Symmetry of H makes `pi` an involution.  The fixed H-sign split at squared
eigenvalue 9 is `(+3)^2,(-3)^1`, so on contrasts `-3 P_pi` has precisely
those signs.  Hence `pi` is a product of two disjoint transpositions.

After relabeling the four types, `pi=(0 1)(2 3)` and H has the exact
equitable quotient

```
Q = 4 J_4 - 3 P_pi.
```

In particular, every vertex has one neighbor in its paired omitted class
and four neighbors in each of the other three classes.  The edges between
each paired pair of 48-vertex classes form a perfect matching.
