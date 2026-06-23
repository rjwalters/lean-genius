# Lehmer's GCD for ℤ

**Slug**: `binary-gcd-oq-02-oq-02`
**Tier**: B (significance 6, tractability 6)
**Parent**: `binary-gcd-oq-02` ("can the binary GCD be extended to ℤ?", resolved by `BinaryGcdOQ02.binaryGcdInt`)

## Statement (informal)

Extend the Lehmer GCD algorithm — originally defined on ℕ in
`Proofs/BinaryGcdOQ03OQ01.lean` as `LehmerGcdOQ01.lehmerGcd` — to the
integers ℤ via the same `natAbs` reduction used in
`BinaryGcdOQ02.binaryGcdInt`, and prove correctness against `Int.gcd`.

## Statement (formal)

Provide

```
def lehmerGcdInt (a b : ℤ) : ℕ := LehmerGcdOQ01.lehmerGcd a.natAbs b.natAbs
```

and prove

```
theorem lehmerGcdInt_eq_intGcd (a b : ℤ) :
    lehmerGcdInt a b = Int.gcd a b
```

together with the standard properties (sign invariance, commutativity,
universal property w.r.t. common divisors, self-application, zero cases).

## Why it matters

The Lehmer algorithm — not binary GCD — is the routine actually used in
production bignum libraries (GMP, OpenSSL, JDK BigInteger). Formalizing the
ℤ extension proves that the production specification (run Lehmer on |a|, |b|)
agrees with the abstract `Int.gcd`. The binary-GCD analogue
(`BinaryGcdOQ02.binaryGcdInt_eq_intGcd`) is purely formal; this one is the
production-relevant version.

## Scope boundary

The "leading-digit quotient estimate" — the substantive content of Lehmer's
1938 paper — is formalized separately in `BinaryGcdOQ03OQ02*` and is
**orthogonal** to the ℤ extension. The `natAbs` reduction works regardless
of whether the underlying ℕ algorithm uses leading-digit estimation or
naive Euclidean descent. This entry deliberately does *not* touch that
optimization.

The bignum aspect ("does the proof scale to multi-precision integers?") is
inherited "for free" from Lean's `Nat` (which the kernel realizes via GMP).

## References

- Lehmer, D.H. (1938). *Euclid's Algorithm for Large Numbers.* Amer. Math. Monthly.
- Knuth TAOCP §4.5.2 (Algorithm L, integer extension via |·|).
- Mathlib: `Int.gcd` = `m.natAbs.gcd n.natAbs`.
- Companion gallery entry: `binary-gcd-oq-02` (`BinaryGcdOQ02.lean`, parallel pattern).
