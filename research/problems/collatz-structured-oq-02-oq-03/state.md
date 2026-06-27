# Research State: collatz-structured-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T00:53:03-07:00
**Iteration**: 2

## Current Focus
Pinned the open question with a precise Lean statement of Tao (2019) and proved
the elementary, axiom-free part of the almost-all picture.

## Active Approach
Sibling pattern (cf. CollatzStructuredOQ02OQ02): state the deep result as a single
documented axiom, prove the elementary core independently.

## Attempt Count
- Total attempts: 3
- Approaches tried: statement + explicit families; n≡1 mod 4 family; colMin bridge

## Blockers
Full proof of Tao (2019) is BLOCKED: requires 3-adic transport/concentration
estimates + Fourier input absent from Mathlib (>> 1000 lines).

## Next Action
Density past 3/4 is BLOCKED by elementary means (n≡3 mod 4 climbs; no fixed-step
closed-form drop). Possible future milestone: formalize the Terras/Korec
natural-density stopping-time result toward Tao's logarithmic-density bound.

## Deliverable (this session)
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` — 0 sorries, 1 deep axiom (tao_2019),
16 axiom-free theorems. Added the Part II↔III bridge `attainsBelow_colMin_lt`
(AttainsBelow n → colMin n < n), orbit positivity (`collatz_pos`,
`collatz_iterate_pos`, `colMin_pos`), the exact `colMin (2^k) = 1`, and the
3/4-family corollary `even_or_mod_four_one_colMin_lt`. Verified offline EXIT 0;
new lemmas axiom-free. Gallery: `src/data/proofs/collatz-structured-oq-02-oq-03/`.
