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

**Cut.**  Constant-vector Hensel lifting is strictly stronger than proving
`A` singular and is false on a faithful self-indexed C4-free control.  The
special hypothesis `k >= 3` cannot repair an infinite induction merely by
providing one additional initial factor of two; each subsequent obstruction
again pairs against the full uncontrolled binary kernel.  Do not formalize a
recursive lifting theorem or run a q=8 search.  A viable 2-adic successor would
need a new theorem controlling the complete kernel and every residual, not an
owner-parity restatement of the lift equation.
