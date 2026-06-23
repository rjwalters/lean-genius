#!/usr/bin/env python3
"""
Durable verifier for inclusion-exclusion-oq-01-oq-03:
classical (divisor) Mobius inversion
    f(n) = sum_{d | n} g(d)      <==>     g(n) = sum_{d | n} mu(d) * f(n/d).

This is the number-theoretic form of inclusion-exclusion.  Python stdlib only;
exhaustive over n in 1..N for random integer-valued g (seeded), ALL PASS expected.

Checks:
  (A) FORWARD->INVERSE.  Given arbitrary g, define f(n) = sum_{d|n} g(d).  Then
      sum_{d|n} mu(d) * f(n/d) == g(n)  for all n.
  (B) INVERSE->FORWARD.  Given arbitrary f, define g(n) = sum_{d|n} mu(d) f(n/d).
      Then sum_{d|n} g(d) == f(n)  for all n.
  (C) mu sanity: mu(1)=1; mu(n)=0 iff n not squarefree; |mu(n)|=1 iff squarefree;
      and the defining convolution sum_{d|n} mu(d) == [n==1].
  (D) Anchor: g = Euler phi recovers f(n)=n (since sum_{d|n} phi(d)=n), and
      inverting f(n)=n gives back phi -- i.e. phi(n) = sum_{d|n} mu(d) * (n/d).
"""

from math import gcd


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def factorize(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def mobius(n):
    if n == 1:
        return 1
    f = factorize(n)
    if any(e >= 2 for e in f.values()):
        return 0
    return (-1) ** len(f)


def euler_phi(n):
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def check(N=400, seed=20260615):
    import random
    rng = random.Random(seed)
    all_pass = True

    # random g
    g = {n: rng.randint(-50, 50) for n in range(1, N + 1)}
    f = {n: sum(g[d] for d in divisors(n)) for n in range(1, N + 1)}

    # (A) forward -> inverse
    okA = all(sum(mobius(d) * f[n // d] for d in divisors(n)) == g[n]
              for n in range(1, N + 1))
    all_pass &= okA
    print(f"(A) g(n) == sum_(d|n) mu(d) f(n/d)  for n<=N={N}: {'PASS' if okA else 'FAIL'}")

    # (B) inverse -> forward (start from arbitrary f2)
    f2 = {n: rng.randint(-50, 50) for n in range(1, N + 1)}
    g2 = {n: sum(mobius(d) * f2[n // d] for d in divisors(n)) for n in range(1, N + 1)}
    okB = all(sum(g2[d] for d in divisors(n)) == f2[n] for n in range(1, N + 1))
    all_pass &= okB
    print(f"(B) f(n) == sum_(d|n) g(d)          for n<=N={N}: {'PASS' if okB else 'FAIL'}")

    # (C) mu sanity + defining convolution
    okC1 = mobius(1) == 1
    okC2 = all((mobius(n) == 0) == (any(e >= 2 for e in factorize(n).values()))
               for n in range(2, N + 1))
    okC3 = all(sum(mobius(d) for d in divisors(n)) == (1 if n == 1 else 0)
               for n in range(1, N + 1))
    okC = okC1 and okC2 and okC3
    all_pass &= okC
    print(f"(C) mu sanity + sum_(d|n) mu(d)==[n==1]: {'PASS' if okC else 'FAIL'}")

    # (D) anchor with Euler phi
    phi = {n: euler_phi(n) for n in range(1, N + 1)}
    f_phi = {n: sum(phi[d] for d in divisors(n)) for n in range(1, N + 1)}
    okD1 = all(f_phi[n] == n for n in range(1, N + 1))           # sum_{d|n} phi(d) = n
    okD2 = all(sum(mobius(d) * (n // d) for d in divisors(n)) == phi[n]
               for n in range(1, N + 1))                          # phi(n)=sum mu(d)(n/d)
    okD = okD1 and okD2
    all_pass &= okD
    print(f"(D) phi anchor: sum_(d|n) phi(d)=n and phi=mu*id: {'PASS' if okD else 'FAIL'}")

    print()
    print("OVERALL:", "ALL PASS" if all_pass else "SOME FAILED")
    return 0 if all_pass else 1


if __name__ == "__main__":
    raise SystemExit(check())
