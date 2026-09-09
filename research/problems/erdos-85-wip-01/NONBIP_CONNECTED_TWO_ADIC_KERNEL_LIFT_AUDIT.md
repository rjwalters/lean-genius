# NONBIP-CONNECTED 2-adic kernel-lift audit

## Proposed mechanism

Divergence round 73 proposed lifting the constant vector through the congruences

```text
A x_m = 0 (mod 2^m),        x_k = 1 (mod 2^k),        q = 2^k.
```

If compatible primitive lifts existed for every `m`, compactness over the
2-adic integers would give a nonzero 2-adic kernel vector.  An integer matrix
with such a vector has zero determinant, hence the desired rational
singularity.  The hoped-for new step was that symmetry and unique C4 owners
would make every Hensel obstruction vanish.

## Exact lifting condition

Write `A x_m = 2^m r_m`.  A lift
`x_{m+1}=x_m+2^m y` exists exactly when

```text
A y = -r_m (mod 2).
```

Because `A mod 2` is symmetric, this is equivalent to orthogonality of `r_m`
to the **entire** binary kernel of `A`, not just to the constant vector.  Thus
the proposed step immediately encounters the previously cut uncontrolled
mod-2 kernel shore.  Divisibility `q=2^k` initializes the process but supplies
no new factor of two at later, arbitrarily high stages.

## Faithful control

`nonbip_connected_two_adic_kernel_lift_control.py` uses an exact symmetric,
loopless, 4-regular, C4-free matrix on 16 vertices emitted by the repository's
faithful q=4 incidence search.  It independently verifies the degrees and
common-neighbor cap.  The matrix is already rationally singular of rank 15,
with primitive kernel generator

```text
(1,-1,1,1,-1,-1,1,-1,-1,1,1,1,-1,-1,-1,1).
```

Nevertheless the particular constant branch does not lift indefinitely.
Exact enumeration of the four-element binary kernel at each Hensel stage gives

```text
modulus       4   8   16   32   64
lift states   1   4   16   64    0
```

The branch dies at modulus 64 even though `A` is singular.  Equivalently, its
actual primitive kernel is constant modulo two but is not constant modulo
four.  This is a sharper falsifier than a nonsingular generic control: the
desired conclusion already holds, yet the proposed sufficient mechanism
still fails.

## Verdict

The displayed constant-vector lifting branch fails on the faithful
`q=4` control even though the desired rational singularity holds there.
Thus this sufficient lifting mechanism is stronger than singularity.
Because `q=4` is outside the remaining branch `k>=3`, the example does not
rule out a lifting theorem with those additional hypotheses. Increasing
`k` initializes more powers of two; the exact lift equation still requires
control of the full binary kernel at every later stage. The current audit
supplies no such induction. A proposed successor must explain how the
additional hypotheses control every residual, rather than infer that from
the initial divisibility or merely restate the lift equation.
