#!/usr/bin/env python3
"""Exact (rational-arithmetic) certification of the multinomial single-component
VARIANCE for binomial-theorem-oq-02-oq-01-oq-04.

State.  `multinomial_mean` (E[Xi] = n*pi, via the 1st derivative of the single-
variable MGF) merged into the registered parent `BinomialTheoremOQ02OQ01.lean`
(#24983).  `multinomial_cross_moment` (E[Xi*Xj] = n(n-1)*pi*pj, i != j) and
`multinomial_covariance` (Cov = -n*pi*pj) are verified in the sibling
`BinomialTheoremOQ02OQ01OQ03.lean` (0 sorry / 0 axiom).  The cross-moment lemma
carries the explicit hypothesis `hij : i != j`, so the DIAGONAL second moment
E[Xi^2] -- and therefore Var(Xi) -- is the one standard second moment NOT yet in
Lean.  This script pins the formula and the exact derivation route so the next
build window can transcribe it without re-deriving.

The route (mirrors `multinomial_cross_moment`, but single-variable):

  Single-variable MGF in the (1+a) parametrization:
      G(a) := sum_k P(k) * (1+a)^{k_i} = (1 + p_i*a)^n         [(1) MGF identity]

  (the i=j specialization of the cross-moment's bivariate MGF
   sum_k P(k)(1+a)^{k_i}(1+b)^{k_j} = (1 + p_i*a + p_j*b)^n at b=0).

  1st derivative at 0:   G'(0)  = sum_k P(k) * k_i           = E[Xi]          = n*p_i
                         G'(a)  = n*p_i*(1 + p_i*a)^{n-1}     => G'(0) = n*p_i
  2nd derivative at 0:   G''(0) = sum_k P(k) * k_i*(k_i-1)   = E[Xi(Xi-1)]    = n(n-1)*p_i^2
                         G''(a) = n(n-1)*p_i^2*(1+p_i*a)^{n-2} => G''(0)=n(n-1)p_i^2

  Then:
      E[Xi^2] = E[Xi(Xi-1)] + E[Xi] = n(n-1)p_i^2 + n*p_i
      Var(Xi) = E[Xi^2] - (E[Xi])^2 = n(n-1)p_i^2 + n*p_i - (n*p_i)^2
              = n*p_i - n*p_i^2 = n*p_i*(1 - p_i).          [(VAR)]

Lean bearers (all already used by the sibling proofs):
  * the MGF identity (1): same Finset.piAntidiag product/sum bookkeeping as
    `multinomial_cross_moment`'s `hmgf`, specialized to one variable
    (g_l = if l = i then 1+a else 1).
  * second-factorial-moment extraction: a `deriv_add_pow_two` analog of
    `multinomial_cross_moment`'s `deriv_add_pow` -- `HasDerivAt`/`iteratedDeriv`
    of `a |-> (1+a)^m` is `m*(m-1)` at 0 (compose `hasDerivAt_pow` twice, or use
    `deriv (deriv ...)`), matched to `sum_k P(k)*k_i*(k_i-1)` by
    `HasDerivAt.sum` + `HasDerivAt.unique`, exactly as the cross-moment proof
    matches the bivariate mixed partial.
  * `multinomial_mean` (parent file) for the E[Xi] term; `ring`/`field_simp` to
    assemble Var.

This is genuinely the i=j diagonal of the merged cross-moment machinery, so the
Lean proof is a single-variable copy of an already-verified 200-line proof, NOT
new mathematics -- but it is build-gated (finicky HasDerivAt bookkeeping) and
should be build-iterated, not blind-written onto the green registered file.

Run: python3 verify_variance.py    (pure stdlib; exact rationals). All asserts pass.
"""

from fractions import Fraction as Fr
from math import factorial


def multinom_coeff(ks):
    num = factorial(sum(ks))
    for k in ks:
        num //= factorial(k)
    return num


def compositions(n, m):
    """All length-m tuples of nonnegatives summing to n (the piAntidiag support)."""
    if m == 1:
        yield (n,)
        return
    for first in range(n + 1):
        for rest in compositions(n - first, m - 1):
            yield (first,) + rest


def moments_component0(p, n):
    """Return (E[Xi], E[Xi(Xi-1)], E[Xi^2], Var(Xi)) for i = 0, exact."""
    m = len(p)
    EXi = Fr(0)
    FM2 = Fr(0)   # falling factorial moment E[Xi(Xi-1)]
    EXi2 = Fr(0)
    for ks in compositions(n, m):
        P = Fr(multinom_coeff(ks))
        for idx in range(m):
            P *= p[idx] ** ks[idx]
        ki = ks[0]
        EXi += ki * P
        FM2 += ki * (ki - 1) * P
        EXi2 += ki * ki * P
    return EXi, FM2, EXi2, EXi2 - EXi * EXi


def main():
    cases = []
    cases += [([Fr(1, 3), Fr(1, 3), Fr(1, 3)], n) for n in range(0, 8)]
    cases += [([Fr(1, 2), Fr(1, 3), Fr(1, 6)], n) for n in range(0, 7)]
    cases += [([Fr(2, 5), Fr(3, 5)], n) for n in range(0, 9)]
    cases += [([Fr(1, 4), Fr(1, 4), Fr(1, 4), Fr(1, 4)], n) for n in range(0, 6)]

    for p, n in cases:
        EXi, FM2, EXi2, Var = moments_component0(p, n)
        pi = p[0]
        assert EXi == n * pi, f"E[Xi] != n*pi at (p={p},n={n}): {EXi} vs {n*pi}"
        assert FM2 == n * (n - 1) * pi * pi, \
            f"E[Xi(Xi-1)] != n(n-1)pi^2 at (p={p},n={n}): {FM2}"
        assert EXi2 == n * (n - 1) * pi * pi + n * pi, \
            f"E[Xi^2] decomposition fails at (p={p},n={n}): {EXi2}"
        assert Var == n * pi * (1 - pi), \
            f"Var(Xi) != n*pi*(1-pi) at (p={p},n={n}): {Var} vs {n*pi*(1-pi)}"

    print(f"VERIFIED (exact rationals) on {len(cases)} (p, n) cases:")
    print("  (mean)  E[Xi]        = n*pi              [merged: multinomial_mean]")
    print("  (FM2)   E[Xi(Xi-1)]  = n(n-1)*pi^2        [single-var MGF 2nd deriv, TODO Lean]")
    print("  (E2)    E[Xi^2]      = n(n-1)*pi^2 + n*pi")
    print("  (VAR)   Var(Xi)      = n*pi*(1 - pi)       [the remaining diagonal moment]")
    print("\nALL ASSERTS PASSED.  Var(Xi) is the i=j diagonal of the merged")
    print("multinomial_cross_moment machinery (which assumes i != j); the Lean target")
    print("is the single-variable copy E[Xi(Xi-1)] = n(n-1)pi^2, then assemble with")
    print("multinomial_mean.  Build-gated -- build-iterate, do not blind-write.")


if __name__ == "__main__":
    main()
