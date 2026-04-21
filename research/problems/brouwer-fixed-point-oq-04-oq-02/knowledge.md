# Knowledge: brouwer-fixed-point-oq-04-oq-02

## Key Facts

### Nash Equilibrium Setup
- n-player game: each player i has finite strategy set Sᵢ
- Mixed strategy: probability distribution σᵢ ∈ Δ(Sᵢ) (probability simplex)
- Expected payoff: Uᵢ(σ) = Σ_{s ∈ ∏ Sⱼ} σ₁(s₁)·...·σₙ(sₙ)·uᵢ(s)
- Nash equilibrium: σ* s.t. Uᵢ(σᵢ*, σ₋ᵢ*) ≥ Uᵢ(τᵢ, σ₋ᵢ*) for all i, τᵢ

### Best Response Correspondence
- BRᵢ(σ₋ᵢ) = argmax_{τᵢ ∈ Δ(Sᵢ)} Uᵢ(τᵢ, σ₋ᵢ)
- Nonempty: Extreme value theorem (Δ(Sᵢ) compact, Uᵢ continuous)
- Convex: Uᵢ is linear in σᵢ, so argmax is convex (if not unique, it's a face of the simplex)
- UHC: Berge's maximum theorem (payoff continuous, domain compact-valued)

### Kakutani Application
- Domain: Δ = ∏ᵢ Δ(Sᵢ) — compact, convex (product of compact convex sets)
- Correspondence: BR(σ) = ∏ᵢ BRᵢ(σ₋ᵢ) — UHC, nonempty, convex values
- Fixed point: σ* ∈ BR(σ*) ⟺ Nash equilibrium

### Mathlib Status (to verify)
- `ProbabilityMassFunction`: Available — discrete distributions over `α : Type`
- `stdSimplex` or `Simplex`: convex analysis tools
- Extreme value theorem: `IsCompact.exists_isMaxOn`
- Berge's maximum theorem: likely NOT in Mathlib
- Game theory: likely very limited in Mathlib

## References
- Nash, J.F. (1950): "Equilibrium Points in n-Person Games"
- Nash, J.F. (1951): "Non-Cooperative Games"
- Kakutani, S. (1941): "A Generalization of Brouwer's Fixed Point Theorem"
- Parent proof: `proofs/Proofs/BrouwerFixedPointOQ04.lean`
