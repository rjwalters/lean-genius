# Research State: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-02

## Current State
**Phase**: ACT (partial)
**Path**: full
**Since**: 2026-06-15 (researcher-2, S2→ACT-partial)
**Iteration**: 3

## Current Focus
Lean skeleton 3→2 sorries: discharged `besicovitch_sqrt_linearIndependent` (the
squarefree MAIN statement) as a genuine **derivation** from the degree theorem
`multiquadratic_subset_products_linearIndependent`, via the `d ↦ primeFactors d`
injection (`LinearIndependent.comp` + `Nat.prod_primeFactors_of_squarefree`). No new
sorry — it now depends only on the (still-open) degree theorem, not on its own
hand-waved signature argument. Remaining sorries: the induction heart
`sqrt_prime_not_mem_multiquadratic` (~250–450 LOC, BUILD-class) and the degree theorem
`multiquadratic_subset_products_linearIndependent` that consumes it.

## Active Approach
Quadratic-tower induction; heart formalized via the strengthened coprime-squarefree
non-membership hypothesis `H(m): ∀ squarefree d>1 coprime to {p₁..pₘ}, √d ∉ K_m`.

## Mathlib API pinned (verified vs master in sibling .lake)
- `LinearIndependent.comp (h) (f) (Injective f) : LinearIndependent R (v ∘ f)`
  (`LinearAlgebra/LinearIndependent/Defs.lean:206`).
- `Nat.prod_primeFactors_of_squarefree (Squarefree n) : ∏ p ∈ n.primeFactors, p = n`
  (`Data/Nat/Squarefree.lean:366`).
- `Nat.prime_of_mem_primeFactors`, `Finset.subset_biUnion_of_mem`,
  `Finset.mem_biUnion`, `Finset.mem_powerset`, `Nat.cast_prod` — all confirmed.
- **No** general multiquadratic non-membership lemma exists in Mathlib (the heart must
  be built by hand; ~250–450 LOC).

## Attempt Count
- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 2 (endpoint discharge by citation; Besicovitch reduction)

## Blockers
- Dual blackout (Docker `info` hangs; Aristotle `prove` 404) — the reduction is written
  but NOT machine-checked. Lemma-name risk points are pinned above.

## Next Action
When Docker is available:
1. Build `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ02.lean`; fix any drift in the reduction
   (risk: `ι` `let`-unfold in the `hcoe := rfl` step; `Function.comp_apply`/`Nat.cast_prod`).
2. Attack the heart `sqrt_prime_not_mem_multiquadratic` via the strengthened
   coprime-squarefree induction `H(m)` (squares-of-K_m characterization).
3. Once heart + degree theorem compile, fold into the gallery / register the file.
