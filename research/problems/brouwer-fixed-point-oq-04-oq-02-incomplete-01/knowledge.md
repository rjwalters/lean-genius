# Knowledge Base: brouwer-fixed-point-oq-04-oq-02-incomplete-01

## Key Facts

- Axiom to prove: `brouwer_product_simplex` — Brouwer FPT for `ProductSimplex G`
- `ProductSimplex G = ∏ᵢ Δᵢ` (product of probability simplices)
- Each `Δᵢ = { p : Fin (G.strategies i) → ℝ | (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 }`
- Parent proof file: `proofs/Proofs/BrouwerFixedPointOQ04OQ02.lean`
- Parent proof has 1 axiom (this one), 0 sorries, 15 theorems

## Proof Sketch

Embed `∏ᵢ Δᵢ` into `Fin (Σᵢ strategies i) → ℝ` via concatenation. The product
simplex maps to the standard simplex in this space under this homeomorphism.
Then apply Mathlib's Brouwer FPT for standard simplices or compact convex sets.

## Mathlib Search Results

[To be populated during OBSERVE phase]

## Dead Ends

[None yet]

## Open Questions

1. Does Mathlib have Brouwer FPT for general compact convex subsets of finite-dim spaces?
2. Is `ProductSimplex G` recognized as `Convex ℝ` by Mathlib?
3. Is `MixedProfile N G → ℝ` an instance of `NormedAddCommGroup` / `InnerProductSpace`?
4. Can we use `Fin.appendEquiv` for the concatenation embedding?
