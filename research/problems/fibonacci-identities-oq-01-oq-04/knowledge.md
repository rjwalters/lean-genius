# Knowledge Base: fibonacci-identities-oq-01-oq-04

Gelin–Cesàro identity: `F(n−2)·F(n−1)·F(n+1)·F(n+2) = F(n)⁴ − 1` for `n ≥ 2`.

## Problem Summary

A quartic Fibonacci product identity, one degree above the quadratic
Cassini/Catalan/d'Ocagne relations. **SOLVED** — 0 sorries, 0 axioms (Mathlib
foundational only), verified in `Proofs/FibonacciIdentitiesOQ01OQ04.lean`.

## Key Insight

The identity is *not* proved by its own induction — it is a **product of two
Catalan slices**. Grouping the four flanking terms as outer × inner:

* Outer pair (Catalan `r=2`, `F(2)=1`): `F(m)·F(m+4) = F(m+2)² − (−1)ᵐ`.
* Inner pair (Catalan `r=1`, `F(1)=1`): `F(m+1)·F(m+3) = F(m+2)² + (−1)ᵐ`.

The `r=2` and `r=1` base points differ by one, so their signs are opposite —
exactly what a **difference of squares** needs:
`(F(m+2)² − (−1)ᵐ)(F(m+2)² + (−1)ᵐ) = F(m+2)⁴ − ((−1)ᵐ)² = F(m+2)⁴ − 1`.
The entire "−1" is the single fact `((−1)ᵐ)² = 1` (`Even.neg_one_pow` on `m+m`).

## Sessions

### Session 2026-07-05 (Session 1) — SOLVED

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms)

**What I Did**
- Reduced Gelin–Cesàro to Catalan's identity `fib_catalan_gap` from the sibling
  entry `fibonacci-identities-oq-01-oq-02-oq-01`.
- Proved the subtraction-free engine `fib_gelin_cesaro_gap` and the named form
  `fib_gelin_cesaro` (n ≥ 2) via a re-index `n = 2 + m` (omega).
- Full gallery integration (meta.json, annotations.json, index.ts).

**Gotcha**: `pow_succ` is greedy — a bare `rw [pow_succ]` rewrote `F(m+2)^2`
(as `^(1+1)`) instead of the intended `(−1)^(m+1)`. Fixed by a targeted local
lemma `hs : (−1)^(m+1) = −((−1)^m)` and `rw [hs]`.

**Files**
- `proofs/Proofs/FibonacciIdentitiesOQ01OQ04.lean` (127 lines, 5 theorems)
- `src/data/proofs/fibonacci-identities-oq-01-oq-04/{meta,annotations,index}`

**Next Steps** (follow-ups, optional)
- Generalise: is `F(n−k)·…·F(n+k)` always a polynomial in `F(n)` with constant
  term `±1`, iterating the difference-of-squares pattern?
- Lucas-number analogue via the Lucas Catalan identity.
