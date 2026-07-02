# erdos-866-wip-01-oq-01 — exact threshold g_3(N)=1 under the repeated-index definition

## Summary

Erdős #866 threshold g_k(N): least g with |A| ≥ N+g ⇒ A ⊆ {1,…,2N} contains all
pairwise sums of some k-family (b : Fin k → ℤ, `HasAllPairwiseSums`). The sibling
`erdos-866-wip-01` proved the lower bound g_k(N) ≥ 1. This entry proves the matching
UPPER bound for k=3, giving the exact value **g_3(N) = 1** — *for the gallery's
definition*, where the family b is NOT required injective.

## Session 2026-07-02 (Session 1) — FRESH, completed

**Outcome:** completed, VERIFIED 0-axiom, 6 thm / 0 def / 122 L, new file
`Proofs/Erdos866Wip01OQ01.lean`, new gallery entry.

### Key mathematical finding
The base predicate `HasAllPairwiseSums A b` uses `b : Fin k → ℤ` with **no injectivity
requirement**, so a constant family `b ≡ e/2` is legal. Hence any even `e ∈ A` gives a
3-configuration whose three pairwise sums all equal `e` (`config_of_even_mem`). Since
every A ⊆ {1,…,2N} of size ≥ N+1 contains an even element (only N odds available,
`exists_even_of_large`), the upper bound g_3 ≤ 1 follows (`guarantees_one`), and with
`g_k_ge_one` the exact value is g_3(N) = 1 (`g_3_least_threshold`, `g_3_eq_one`).

This is deliberately NOT the classical g_3(N) = 2 (which is defined with three DISTINCT
integers). The entry proves the exact threshold for the gallery's own model and isolates,
via `config_of_even_mem`, exactly why the missing injectivity collapses 2 to 1.

### Techniques
- Constant/degenerate configuration to trivialize an existential.
- Pigeonhole via `Finset.card_le_card` + `oddNumbers_card` for "large set has an even".
- `omega` for the `Int.toNat` bookkeeping (`((m:ℤ)+(m:ℤ)).toNat = e` with `e = m+m`).

### Files
- proofs/Proofs/Erdos866Wip01OQ01.lean
- src/data/proofs/erdos-866-wip-01-oq-01/{meta.json,annotations.json}

### Next steps (open questions generated)
1. Strengthen `HasAllPairwiseSums` to require injective b; prove classical g_3(N) ≥ 2
   (size-(N+1) construction with no injective 3-config).
2. Prove classical upper bound g_3(N) ≤ 2 for injective families.
3. Does the single-element degeneracy force g_k(N) = 1 for ALL k ≥ 3 under the current
   (non-injective) definition? (Very likely yes — the same constant family works.)
