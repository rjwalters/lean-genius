# Knowledge: sophie-germain-oq-03

## Established Facts

- A Cunningham chain of the first kind p₀,p₁,… (pᵢ₊₁ = 2pᵢ+1) has closed form pᵢ = 2ⁱ·(a+1) − 1
  with a = p₀ (cunninghamTerm; recurrence verified by cunninghamTerm_succ).
- **Main bound**: if a = p₀ is an odd prime (a > 2), the chain has length ≤ a − 1
  (cunningham_length_le_pred). Proof: the term at index a − 1 is ≡ 0 (mod a) by Fermat's little
  theorem (2^(a-1) ≡ 1, a+1 ≡ 1) yet exceeds a, hence composite.
- The bound is sharp: maximal chain from 5 is 5,11,23,47 (length 4 = 5−1; 95 = 5·19 blocks);
  from 3 is 3,7 (length 2 = 3−1).
- a = 2 is genuinely excluded (chain 2,5,11,23,47 has length 5 > 1); Fermat's step needs a ∤ 2.

## Open Questions Within This Problem

- Sharpen a − 1 to ord_a(2) (multiplicative order of 2 mod a)?
- Analogous bound for second-kind chains (pᵢ₊₁ = 2pᵢ − 1)?

## Failed Approaches

(None — the closed-form + Fermat route worked directly.)

## Promising Leads

- The order-of-2 refinement is the natural next step; Mathlib has orderOf in (ZMod a)ˣ.

## Lean

- proofs/Proofs/SophieGermainOQ03.lean — verified, 0 axioms, 11 theorems, 2 defs, 189 lines.
- Gallery: src/data/proofs/sophie-germain-oq-03/{meta,annotations}.json
