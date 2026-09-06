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

The positive spanning-tree interpretation uses connectedness. The valuation lower bound
itself has a more elementary explanation that does not require C4-freeness
or a defect graph.

Indeed, let A be any symmetric integral matrix of order n with constant
row sum q. Let C be its leading (n-1)-square principal submatrix and let P
have columns `e_1,...,e_(n-1),1`. This is a unimodular matrix, and

```text
P^T A P = [ C       q 1 ]
          [ q 1^T  n q ],
det(A) = n q det(C) - q² 1^T adj(C) 1.
```

The block determinant identity holds even when C is singular. Thus whenever
q divides n, q² divides det(A). In particular n=q² gives this divisibility
without any graph assumptions. For nonzero determinant and q=2^k, it
already implies `v_2(det(A))>=2k`.

Consequently the proposed strict upper bound below cannot come from
regularity alone. Within the stated graph class it is equivalent to
excluding every nonsingular A, since any such A automatically violates
that upper bound. This observation does not refute the conjecture (the
class could be empty); it identifies where its entire unresolved content
lies. No additional determinant-divisibility wrapper is supplied here.

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

## Full quadratic-form invariants still need the zero diagonal

Date: 2026-09-06. The following exact control has binary q=8 and connected,
non-bipartite defect. It passes the entire rational quadratic-form test,
not just determinant-square or 2-adic tests. It has six loops, so it is
**not** a simple-graph counterexample to A-REG.

[Buratti--Stinson, *New Results on Modular Golomb Rulers, Optical
Orthogonal Codes and Related Structures*, arXiv:2007.01908v2,
Table 1, the row for v=57,64,68 and k=8](https://arxiv.org/pdf/2007.01908)
provides the modular Golomb ruler

    S = {0,4,5,17,19,25,28,35} in Z/64Z.

All 56 nonzero ordered differences are distinct. Define the symmetric
zero-one matrix `A[x,y]=1` exactly when `x+y` belongs to S modulo 64.
It has row sum 8, and its square has diagonal 8 and off-diagonal entries
at most 1. The missing differences are

    T = {22,26,27,32,37,38,42}.

Consequently `A²=7I+J-D`, where D is the Cayley graph on Z/64Z with
connection set T. D is simple and 7-regular. Its step-27 edges form a
Hamiltonian cycle, proving connectedness. The cycle
`0,27,54,12,38,0` has length five, proving non-bipartiteness.

The exact determinant is

    det(A) = 490601813190770188069153280 != 0.

Thus, for `M=7I+J-D=A²`, the rational invertible matrix `A^{-1}` gives

    (A^{-1})^T M A^{-1} = I_64.

M is positive definite and has the same determinant square class and
every local Hasse invariant as I_64. No calculation of separate Hilbert
symbols is needed: the displayed rational congruence proves all of them
simultaneously. This is stronger than a mere nonsymmetric Gram factor:
A itself is a symmetric zero-one square root with constant row sum.

The missing A-REG requirement is exact and visible. Its diagonal ones
occur at `0,2,14,32,34,46`, so `trace(A)=6`. Removing those loops gives
a simple C4-free graph with six vertices of degree 7 and 58 of degree 8,
not the required minimum-degree-8 witness. This control addresses only
the Gram quadratic-form test; it supplies no zero-trace square root and
does not refute the separate trace-escape condition.

The standard-library verifier
`verify_binary_q8_looped_gram_control.py` checks every difference, all matrix
entries of the square identity, the connectivity and odd-cycle certificates,
the six loops, and the determinant by fraction-free exact elimination.
It is a check of a published finite construction, not a graph search.

Therefore an arithmetic terminal based on rational congruence of
`(q-1)I+J-D` to the identity cannot exclude all connected non-bipartite
defects at binary-square parameters. Any successful refinement must retain
the zero-diagonal requirement, for example through its trace/Sachs data;
the full Gram Hasse invariants alone lose that information. This finite
control does not settle cofinal q, mixed defect, or A-REG, and is not a
Lean formalization.
