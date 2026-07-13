# Selection Report: infinitude-primes-4k3-oq-03

**Date**: 2026-05-03
**Selected by**: Seeker
**Composite Score**: 7070 (Tier B, sig=7, tract=7, knowledge=EMPTY)

## Problem
Infinitely Many Primes ≡ 1 (mod 4) — Elementary Proof

Prove elementarily that there are infinitely many primes $p \equiv 1 \pmod{4}$ using
the argument: $N = (2p_1 \cdots p_k)^2 + 1$ has a new prime factor $\equiv 1 \pmod{4}$.

## Selection Rationale

1. **High tractability** (7/10) — Elementary argument is clear and formalizable
2. **Concrete statement** — ∃ infinitely many primes ≡ 1 (mod 4), using only QR basics
3. **Pedagogical value** — Connects to Fermat's theorem on quadratic residues, precursor to Dirichlet

## Suggested First Steps

1. Check `Mathlib.NumberTheory.LegendreSymbol` for quadratic residue facts
2. Verify `ZMod.isUnit_prime_iff_not_dvd` and related API
3. Formalize the N = P² + 1 argument using `Nat.factors`

## Pool Context

Highest-tractability problem in this batch; good candidate for early researcher success.
