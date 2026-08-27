# NONBIP-CONNECTED rooted Jacobi audit (q=4)

## Question

Can a vertex-deleted determinant or resolvent force the rooted congruence

`e_A(R_x) - C5_x + 3 t_x = 2 (mod 4)`

without assuming the missing congruence in another form?

## Bounded probe

`nonbip_connected_rooted_jacobi_q4_probe.py` enumerates 256 labelled
4-regular C4-free graphs on 16 vertices with one root neighbourhood fixed.  It
computes the leading and trailing coefficients of the principal-deletion
characteristic polynomials for `A`, `A+I`, `A-I`, and `4I-D`, modulo 16.

Command:

```text
python3 research/problems/erdos-85-wip-01/nonbip_connected_rooted_jacobi_q4_probe.py \
  --models 256 --width 7 --window head
```

Across all 4096 rooted samples, the leading coefficient residues for
`det(zI-A_{\hat x})` are

```text
[1, 0, 4, {2,4}, 12, 4, 6]  (mod 16),
```

where the fourth entry distinguishes triangle degrees 1 and 2, while the
fifth-walk entry is uniformly 4.  The corresponding `A+I` and `A-I`
coefficients distinguish the two rooted profiles even more strongly.
The tested coefficients for `4I-D` are root-independent modulo 16, but they
contain only even-walk/defect data and do not constrain the required odd
rooted walk.

## Algebraic audit

Write

```text
det(zI-A) = sum_j a_j z^(n-j),
(zI-A)^(-1)_{xx} = sum_k (A^k)_{xx} z^(-k-1).
```

Jacobi gives

```text
det(zI-A_{\hat x}) = det(zI-A) (zI-A)^(-1)_{xx}.
```

Hence its fifth leading coefficient is

```text
b_5(x) = a_5 + a_3 (A^2)_{xx} + a_2 (A^3)_{xx} + (A^5)_{xx},
```

because `a_1=(A)_{xx}=0`.  Regularity fixes `(A^2)_{xx}=q`, while
`(A^3)_{xx}=2t_x`.  At `n=q^2` with `8 | q`, the `a_2(A^3)_{xx}` term
vanishes modulo the relevant 2-power.  Thus root-independence of `b_5(x)` is
precisely an odd rooted-walk constraint; Sachs expansion of the same
coefficient recovers the already-known `E_x`, `C5_x`, and `t_x` combination.

The principal-deletion Jacobi identity therefore **repackages** the target; it
does not supply an independent reason for the coefficient to be constant.
The q=4 constancy is calibration/saturation evidence only.  Any continuation
of this route needs a genuinely new 2-adic theorem about vertex-deleted
coefficients (not determinant squareness, Matrix-Tree, or Jacobi itself).

## Verdict

The naive rooted Jacobi/resolvent route is cut.  Its computational signature is
real and exactly located at the fifth coefficient, but the proposed mechanism
is circular.  A two-root Dodgson identity would only help if it independently
forces equality of these fifth coefficients across a defect edge; that is the
next distinct question, not a consequence established here.

## Two-root Dodgson follow-up

Let `P = det(zI-A)`, let `P_x` and `P_{xy}` be the one- and two-vertex
principal deletions, and let `C_{xy}` be the signed off-diagonal cofactor.
Desnanot--Jacobi says

```text
P_x P_y - P P_{xy} = C_{xy}^2.
```

After division by `P^2`, this is exactly the complementary-minor identity

```text
R_xx R_yy - P_{xy}/P = R_xy^2,
```

for `R=(zI-A)^{-1}`.  It is an identity, not an additional constraint.  More
importantly for propagation, every term is symmetric under `x <-> y`:
coefficient comparison sees sums/products of the rooted coefficients, never
`b_5(x)-b_5(y)` with a sign.  On a defect edge, `(A^2)_{xy}=0` merely removes
one early coefficient of the off-diagonal resolvent; it does not break this
symmetry or determine the remaining `R_xy` walk coefficients.

Thus raw Dodgson/Pluecker expansion cannot independently prove
`b_5(x)=b_5(y)`.  Such a proof would need an extra input that already controls
the pair-specific off-diagonal cofactor (or the discriminant of the unordered
pair).  The determinant identity itself supplies neither.  Consequently the
two-root variant is also cut as a standalone mechanism; attaching a genuinely
new coherent/Hadamard constraint would be a different proposal.
