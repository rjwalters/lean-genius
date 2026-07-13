#!/usr/bin/env python3
"""
Durable verifier for euler-totient-oq-01-oq-03:
"Verified RSA with the Carmichael function lambda(n) instead of Euler's phi(n)."

Parent gallery entry `euler-totient-oq-01` already formalizes
    lambda(n) = Monoid.exponent (ZMod n)^x      (Carmichael's function)
with a^lambda(n) = 1 for units a, and lambda(n) | phi(n).

This script checks the three facts an RSA-with-lambda formalization rests on
(Python stdlib only; exhaustive over all residues, ALL PASS expected):

  (A) RSA CORRECTNESS (lambda form).  For n = p*q with p != q prime and any
      exponent pair with  e*d ≡ 1 (mod lambda(n)),  e coprime to lambda(n):
          m^(e*d) ≡ m   (mod n)   for ALL m in 0..n-1   (not just units).
      Here lambda(n) = lcm(p-1, q-1).

  (B) lambda BEATS phi.  lambda(n) | phi(n) and is typically strictly smaller,
      so the lambda-based private exponent d is no larger (often much smaller)
      than the phi-based one, while giving the SAME decryption map.

  (C) SQUAREFREE IS NECESSARY for the all-m statement.  The clean fixed point
          a^(lambda(n)+1) = a   for ALL a
      holds for squarefree n but can FAIL for non-squarefree n (e.g. n = p^2,
      for a divisible by p).  RSA moduli n = p*q are squarefree, so (A) is safe;
      this check documents why the hypothesis cannot be dropped.

The mathematical content (for the Lean ORIENT): by CRT it suffices to prove the
per-prime fixed point  a^(1 + k*lambda(n)) ≡ a (mod p)  for each prime p | n.
For a ≡ 0 both sides vanish; for a a unit, (p-1) | lambda(n) and Fermat give
a^(p-1) ≡ 1, hence a^(1+k*lambda(n)) ≡ a.  The p|a case is exactly where a
*repeated* prime factor would break the argument (a^j stays ≡ 0 mod p but need
not return to a mod p^2), which is why squarefree is required.
"""

from math import gcd


def lcm(a, b):
    return a * b // gcd(a, b)


def euler_phi_pq(p, q):
    return (p - 1) * (q - 1)


def carmichael_pq(p, q):
    return lcm(p - 1, q - 1)


def modinv(e, m):
    # e^{-1} mod m via extended Euclid; assumes gcd(e,m)=1
    g, x = e % m, 1
    # use pow for Python 3.8+: pow(e, -1, m)
    return pow(e, -1, m)


def small_primes(lo, hi):
    out = []
    for n in range(lo, hi + 1):
        if n < 2:
            continue
        if all(n % d for d in range(2, int(n ** 0.5) + 1)):
            out.append(n)
    return out


def check_A_and_B(verbose=True):
    primes = small_primes(3, 40)
    all_pass = True
    pairs = [(p, q) for i, p in enumerate(primes) for q in primes[i + 1:]]
    tested = 0
    lam_lt_phi = 0
    for (p, q) in pairs:
        n = p * q
        if n > 2000:
            continue
        phi = euler_phi_pq(p, q)
        lam = carmichael_pq(p, q)
        if lam < phi:
            lam_lt_phi += 1
        # pick the smallest valid public exponent e coprime to lambda(n), e>1
        e = 2
        while gcd(e, lam) != 1:
            e += 1
        d_lam = pow(e, -1, lam)            # lambda-based private exponent
        d_phi = pow(e, -1, phi)            # phi-based private exponent (classical)
        # (A) correctness for ALL m with the lambda exponent
        okA = all(pow(m, e * d_lam, n) == m % n for m in range(n))
        # the phi exponent also works (classical), and both maps agree on all m
        same_map = all(pow(m, e * d_lam, n) == pow(m, e * d_phi, n) for m in range(n))
        tested += 1
        if not (okA and same_map):
            all_pass = False
            if verbose:
                print(f"  FAIL n={n}=({p}*{q}) e={e} d_lam={d_lam} d_phi={d_phi} "
                      f"okA={okA} same_map={same_map}")
    if verbose:
        print(f"(A) RSA-lambda correctness for ALL m over {tested} moduli n=p*q (n<=2000): "
              f"{'ALL PASS' if all_pass else 'FAIL'}")
        print(f"(B) lambda(n) < phi(n) strictly in {lam_lt_phi}/{tested} of the tested moduli "
              f"(lambda | phi always); lambda gives the same decryption with a no-larger exponent.")
    return all_pass


def check_C(verbose=True):
    """Squarefree necessity: a^(lambda(n)+1) = a for all a holds for squarefree n,
    can fail for n = p^2."""
    ok = True
    # group exponent of (Z/nZ)^x is only the units' order; the *all-a* fixed point
    # is the relevant RSA statement. Use the universal exponent L(n) = exponent of
    # the unit group; for the all-a fixed point we need a^(L+1)=a for ALL a.
    def unit_group_exponent(n):
        # exponent of (Z/nZ)^x  = lcm of element orders of units
        L = 1
        for a in range(1, n):
            if gcd(a, n) == 1:
                # order of a mod n
                o, x = 1, a % n
                while x != 1:
                    x = (x * a) % n
                    o += 1
                L = lcm(L, o)
        return L

    # squarefree examples: a^(L+1)=a for ALL a
    for n in [15, 21, 33, 35, 105]:  # products of distinct primes
        L = unit_group_exponent(n)
        good = all(pow(a, L + 1, n) == a % n for a in range(n))
        if verbose:
            print(f"  squarefree n={n}: L={L}, a^(L+1)=a for all a? {good}")
        ok &= good

    # non-squarefree counterexample: n = p^2
    for n in [9, 25, 49]:
        L = unit_group_exponent(n)
        bad_as = [a for a in range(n) if pow(a, L + 1, n) != a % n]
        if verbose:
            print(f"  non-squarefree n={n}=p^2: L={L}, a with a^(L+1)!=a: {bad_as} "
                  f"-> all-a fixed point {'HOLDS' if not bad_as else 'FAILS (squarefree needed)'}")
        # we EXPECT failure here; verifier passes iff the failure set is nonempty
        ok &= (len(bad_as) > 0)
    if verbose:
        print(f"(C) squarefree necessity demonstrated: {'PASS' if ok else 'FAIL'}")
    return ok


def main():
    print("=" * 72)
    print("RSA with Carmichael lambda(n) -- correctness checks")
    print("=" * 72)
    a = check_A_and_B()
    print()
    c = check_C()
    print()
    print("=" * 72)
    ok = a and c
    print("OVERALL:", "ALL PASS" if ok else "SOME FAILED")
    print("=" * 72)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
