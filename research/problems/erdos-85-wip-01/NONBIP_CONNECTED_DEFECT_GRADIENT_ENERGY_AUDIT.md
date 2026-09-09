# NONBIP-CONNECTED defect-gradient energy audit

Date: 27 August 2026. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: exact energy identity; evaluation from the available traces is missing.

## Target and exact energy

Let `A` be the ambient adjacency matrix, `D` the second-order defect
adjacency matrix, and

```text
k_x = deg_{A intersection D}(x) = (AD)_{xx} = q - 2 t_x,
K   = diag(k).
```

At square order `D` is `(q-1)`-regular. Exact integer-valued constancy
of triangle degree along defect edges is equivalent to

```text
DK = KD.
```

Its squared Frobenius norm is twice the Dirichlet energy

```text
1/2 ||DK-KD||_F^2
  = sum_{{x,y} in E(D)} (k_x-k_y)^2
  = k^T L_D k
  = tr(K^2 D^2) - tr(K D K D)                         (E)
  = (q-1) sum_x k_x^2 - 2 sum_{{x,y} in E(D)} k_x k_y.
```

Because `k=q1-2t`, the same quantity is

```text
4 sum_{{x,y} in E(D)} (t_x-t_y)^2.
```

Thus (E) vanishes if and only if `t`, equivalently `k`, is constant on
every defect component.  Connectedness would then make it globally
constant. This is stronger than propagation only modulo four: a nonzero
difference divisible by four contributes positive energy in (E).

## Why the ordinary trace/moment ledger cannot evaluate (E)

The square-order identity

```text
A^2 = (q-1)I + J - D
```

reduces even powers of `A` to expressions in `D` and `J`. Because
`A,D,J` commute and `AJ=qJ`, an ordinary polynomial expression reduces to
`p(D) + A r(D) + cJ`. Odd-`A` terms retain the mixed traces
`tr(A r(D))`; these depend on square-root signs and are not determined by
the spectrum of `D` alone. This reduction does not supply a formula for
`K`: the operation

```text
K = diag(diag(AD)) = I HadamardProduct (AD)
```

is a Schur/diagonal extraction, not an operation supplied by ordinary
polynomial closure. In special configurations its result may nevertheless
belong to the ordinary algebra; no contrary universal assertion is needed
here.
Both terms in (E) retain new rooted information:

* `tr(K^2 D^2)=(q-1) sum k_x^2` needs the second moment of the diagonal of
  `AD`, not `tr((AD)^2)`;
* `tr(KDKD)=2 sum_{D-edge} k_x k_y` needs the defect-edge correlation of
  that diagonal.

The displayed polynomial reductions and `sum k_x = tr(AD)` do not
evaluate either rooted moment. In particular, the commutation `AD=DA`
does not by itself imply that the diagonal extraction of `AD` commutes
with `D`. The calculation above supplies an exact target for a further
identity, but does not prove that every possible trace or spectral
argument is incapable of evaluating it under the full graph hypotheses.
Any proposed evaluation must justify the passage from ordinary mixed
traces to these rooted quantities, rather than replace the latter by
`tr((AD)^2)` or an ordinary word with different indices.

## Relation to the stronger weighted-neighbor terminal

Vanishing of (E) only propagates `k`; it does **not** prove the stronger
identity

```text
A k = ((q^2-4)/3) 1,
```

which already gives a nonzero rational kernel vector and closes the
connected branch.  Uniform `k=r1` instead gives `Ak=qr1`, and no current
arithmetic fixes `r=(q^2-4)/(3q)`.  Therefore even a successful energy-zero
proof needs a second structural or arithmetic terminal.

## Verdict

The defect-gradient energy is an exact nonnegative invariant for exact
componentwise constancy. The available ordinary polynomial reductions
do not evaluate it; no energy-zero theorem is established. A reopening
needs a justified relation controlling the two rooted moments (or their
difference), together with the post-propagation terminal. This audit
does not exclude all future spectral arguments or reduce the modulo-four
propagation target to energy zero.
