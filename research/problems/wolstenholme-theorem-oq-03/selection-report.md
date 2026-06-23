# Selection Report: wolstenholme-theorem-oq-03

**Selected**: 2026-04-05
**Seeker run**: SELECT mode
**Composite score**: 66 (tied top with buffons-needle-oq-01-oq-04)

## Problem

**ID**: `wolstenholme-theorem-oq-03`
**Title**: Prove connection between Wolstenholme and FLT for irregular primes
**Tier**: B | **Significance**: 6/10 | **Tractability**: 6/10
**Knowledge tier**: EMPTY (0 knowledge items)

## Selection Rationale

1. **EMPTY knowledge tier** — highest priority class; no prior research in workspace
2. **Tied highest composite score** (66) among all 15 available problems; tiebreak favors
   this problem over `buffons-needle-oq-01-oq-04` for domain diversity — recent seeker
   selections covered calculus/analysis, number theory/analysis, combinatorics (x2). The
   Wolstenholme–FLT connection is in algebraic/p-adic number theory, distinct from those.
3. **Infrastructure exists**: `proofs/Proofs/WolstenholmeTheorem.lean` and
   `src/data/proofs/wolstenholme-theorem/` are in the gallery (axiomatized, 2 axioms).
   The OQ-03 direction builds directly on the existing theorem statements and definitions.
4. **Tractability is real**: The Wolstenholme–FLT connection (second case of FLT for
   Wolstenholme/Wieferich primes) is a classical number theory result with specific,
   provable lemmas in Lean. Not open — the connection is known.

## Rejection Summary

- **Candidates considered**: 15 available
- **WEAK-tier rejections** (score ~-922 to -933): all 10 problems with existing selection
  reports ranked far below EMPTY-tier problems
- **Lower EMPTY-tier rejections**:
  - `erdos-ko-rado-oq-04` (score 57) — combinatorics domain penalty (2 recent selections)
  - `brouwer-fixed-point-oq-04-oq-04` (score 56) — lower significance+tractability
  - `szemeredi-theorem-oq-01` (score 48) — very low tractability (4/10); Kelley-Meka
    direction requires frontier combinatorics, unlikely to yield Lean proofs autonomously
- **Tiebreak**: `buffons-needle-oq-01-oq-04` (score 66) rejected in favor of this problem
  due to domain diversity (buffons is geometric probability, but the base buffons-needle
  is already a verified Mathlib-backed proof; the OQ-04 generalization risks shallow
  extension rather than theory-level new content)
- **Confidence**: medium (two tied candidates; domain diversity tiebreaker applied)

## The Mathematical Connection

The Wolstenholme–FLT connection comes in two parts:

**1. Second case of FLT (Fermat quotient angle):**
If p is an odd prime and x^p + y^p = z^p with p ∤ xyz, then:
- Wieferich (1909): 2^(p-1) ≡ 1 (mod p²) — i.e., p is a Wieferich prime
- Wolstenholme primes (C(2p-1,p-1) ≡ 1 mod p⁴) are a special class related to this

**2. Irregular primes and FLT:**
An irregular prime p satisfies p | B_k for some Bernoulli number B_k with 0 < k < p-1.
Kummer proved FLT for regular primes (1850). The Wolstenholme theorem involves harmonic
sums H_{p-1} ≡ 0 (mod p²), which connects to Bernoulli numbers via:
H_{p-1} ≡ -B_{p-1}/1 via Fermat quotients

**Research direction**: Formalize the implication:
- If p is a Wolstenholme prime, then p satisfies the Fermat quotient condition
- State the connection to FLT's second case conditions
- Lean target: formal statements linking `WolstenholmeStatement` to Fermat quotient
  divisibility conditions

## Related Gallery Proofs

- `wolstenholme-theorem`: Base theorem (axiomatized); provides `WolstenholmeStatement`,
  `BabbageTheorem`, `centralBinomial`, Fermat quotient definitions
- `wolstenholme-theorem-oq-02`: Sub-problem already in gallery
- `bertrands-postulate-oq-03`: Prime gap analysis (number theory infrastructure)
- `prime-gap-bounds-oq-03`: Chebyshev functions — adjacent available problem

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/WolstenholmeTheorem.lean` and
   `proofs/Proofs/WolstenholmeTheoremOQ02.lean` to map existing definitions and axioms.
   Identify which Mathlib modules cover Bernoulli numbers and Fermat quotients.
2. **ORIENT**: Survey Mathlib for `Fermat`, `Wieferich`, `Bernoulli`, `IrregularPrime`
   — determine what infrastructure exists for the second case of FLT.
3. **DECIDE**: Formalize the Fermat quotient characterization of Wolstenholme primes as
   a theorem + sorry, then attempt to prove the implication toward FLT second case via
   the Bernoulli–harmonic number connection.

## Pool Summary

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 1222 |
| Completed | 545 |
| Graduated | 3 |
| Blocked | 2 |
| **Total** | **1787** |

## Pool Health

- **Pool depth**: adequate (15 available > threshold of 5)
- **Recommendation**: Pool healthy; next refresh when available drops below 5
- **Next refresh recommended**: when available < 5
