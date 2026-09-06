# NONBIP-CONNECTED: the direct 2-adic terminal

## Scope

This audits candidate (xi) under
`A-REG-NONBIP -> NONBIP-CONNECTED [q]`, for `q = 2^k`, `k >= 3`.
It deliberately does not extend the separator tree.  The question is whether
reduction modulo two, rank, or Smith data already converts connectedness of
the second-order defect graph into a contradiction.

## What is already forced

Let `A` be the integral adjacency matrix of a loopless binary `q`-regular
C4-free graph on `q^2` vertices, and let `D` be its second-order defect graph.
The banked connected-owner identities give

```text
A^2 = L_D + J,
det(L_D + J) = det(A)^2,
det(L_D + J) = q^4 tau(D).
```

Consequently, if `D` is connected then

```text
det(A) != 0,
tau(D) is a square,
|det(A)| = q^2 sqrt(tau(D)),
v_2(det(A)) = 2k + v_2(tau(D))/2 >= 2k.
```

This is the exact load-bearing consequence of connectedness in the 2-adic
route.  It is stronger than merely reducing `A` modulo two.

## Why mod-two rank does not close the node

Because `q` is even, the all-ones vector lies in `ker(A mod 2)`.  Moreover
`A mod 2` is an alternating matrix: it is symmetric with zero diagonal in
characteristic two.  Its rank is therefore even.  Since `q^2` is even, its
nullity is even and hence at least two.  Equivalently, the characteristic
polynomial has an `x^2` factor modulo two; this is a special case of the
banked `adjMatrix_charpoly_isSquare_zmodTwo`.

For a nonsingular integral matrix, mod-two nullity counts the Smith invariant
factors divisible by two.  It gives only the lower bound

```text
nullity_F2(A) <= v_2(det(A)).
```

It gives no upper bound on the exponents of those invariant factors.  Thus
even an exact computation of `nullity_F2(A)` cannot conflict with the lower
bound `v_2(det(A)) >= 2k`. Passing from `A` to `A^2 = L_D + J`
doubles the **total determinant valuation**, not necessarily the individual
Smith exponents. Matrix squaring is not compatible with independent
unimodular row and column changes used to obtain Smith normal form. Plain
F2 rank still gives only a lower bound, not the required terminal.

A graph-level check makes this distinction concrete. For the actual q=6
HoG H36 graph, the offline [verifier](verify_boza_h36_triangle_control.py)
computes F2 ranks 32 for A and 28 for A². Thus there are respectively 4
and 8 even Smith invariant factors. Doubling each individual exponent
would preserve that count, so it cannot describe A². This example is
nonsingular over Q: its defect D is connected and A²=L_D+J is positive
definite. It refutes the generic Smith-squaring claim even for an actual
regular C4-free square-order adjacency matrix. It does not test the
binary-degree upper-bound conjecture below; that conjecture remains open.

The banked generic tools in `Erdos85TwoAdicDeterminant.lean` have the same
orientation: mod-two kernels or even transformed rows prove additional
divisibility of a determinant.  NONBIP-CONNECTED already needs an upper
bound, so those lemmas cannot close it without a new bounded-exponent input.

## Shortest genuine terminal

The missing statement is a **uniform 2-adic upper bound**, using the
zero-one, C4-free, and square-order structure rather than rank alone:

> **AXIOM A-REG-2ADIC-UPPER.** If `k >= 3`, `q = 2^k`, and `A` is the
> adjacency matrix of a loopless binary `q`-regular C4-free graph on `q^2`
> vertices with `det(A) != 0`, then
> `v_2(|det(A)|) < 2k`.

This immediately contradicts the connected-defect lower bound above, so it
proves every such `A` singular and closes NONBIP-CONNECTED.  The strict
threshold `2k` is minimal for this argument: any proposed upper bound at or
above `2k` does not contradict connectedness.

An equivalent combinatorial target is the Sachs formulation:

> The signed sum of spanning elementary subgraphs of `A` is not divisible by
> `4^k` whenever it is nonzero.

This is not yet a theorem.  C4-freeness removes the four-cycle Sachs terms,
but cycles of lengths three and at least five remain; no banked involution or
valuation bound controls their perfect-matching cofactors.  Restating
`4^k not_dvd det(A)` as a wrapper would add no content.

## Verdict

**NO TERMINAL from mod-two rank/SNF as currently developed.**  The route has
one precise missing blade: `A-REG-2ADIC-UPPER`, or a Sachs involution proving
its equivalent nondivisibility statement.  Until such a bounded-exponent
argument is found, further kernel-dimension and determinant-divisibility
lemmas move in the wrong direction and should not be banked as progress
toward A-REG.
