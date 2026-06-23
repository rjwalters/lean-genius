# Problem: Nash Equilibrium Existence via Kakutani Fixed Point

**Slug**: brouwer-fixed-point-oq-04-oq-02
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Plain Language

The gallery proof `BrouwerFixedPointOQ04.lean` formalizes the Kakutani Fixed Point
Theorem using an axiom `kakutani_fixed_point_axiom`. This open question asks:

**Can the Nash equilibrium existence theorem (Nash 1950) be fully formalized in
Lean 4 using the Kakutani axiom, by defining best-response correspondences and
proving their upper hemicontinuity (UHC)?**

Nash's theorem: In any finite n-player game where each player has a finite
strategy set, there exists a Nash equilibrium in mixed strategies.

### Formal Question

```lean
-- Finite n-player game: strategy sets S₁,...,Sₙ (finite)
-- Mixed strategy: probability distribution over Sᵢ
-- Payoff function: Δ(S₁) × ... × Δ(Sₙ) → ℝ (continuous bilinear extension)
-- Best response: BRᵢ(σ₋ᵢ) = argmax over σᵢ of expected payoff

-- Nash equilibrium: σ* s.t. σᵢ* ∈ BRᵢ(σ*₋ᵢ) for all i
theorem nash_equilibrium_exists (n : ℕ) (game : FiniteGame n) :
    ∃ σ : MixedStrategyProfile n game, IsNashEquilibrium game σ := by
  -- Apply Kakutani to best-response correspondence on mixed strategy simplex
  apply kakutani_implies_nash
  · show IsCompactConvex (MixedStrategyProfile n game)
  · show IsUHC (bestResponseCorrespondence game)
  · show ∀ σ, Nonempty (bestResponseCorrespondence game σ)
  · show ∀ σ, Convex (bestResponseCorrespondence game σ)
```

### Why This Matters

- One of the most significant applications of fixed-point theory in science
- Nash's work (1950) earned the Nobel Prize in Economics (1994)
- Completes the application theory established in `BrouwerFixedPointOQ04.lean`
- Demonstrates Lean 4's capability for formalization in economics/game theory
- High significance: connects topology, probability, and economics in one proof

## Known Results

### From Parent Proof (`BrouwerFixedPointOQ04.lean`)

The gallery establishes:
- `kakutani_fixed_point_axiom`: Kakutani FPT (axiomatized)
- `single_valued_reduction`: Kakutani for singletons = Brouwer (PROVED)
- `kakutani_1d_ivt`: 1D Kakutani via IVT (PROVED)
- Correspondence definitions: `Correspondence`, upper hemicontinuity
- Framework for Nash equilibrium existence (structured)

The `kakutani_fixed_point_axiom` states:
```lean
axiom kakutani_fixed_point_axiom {n : ℕ} (S : Set (Fin n → ℝ))
    (hS_compact : IsCompact S) (hS_convex : Convex S) (hS_nonempty : S.Nonempty)
    (F : (Fin n → ℝ) → Set (Fin n → ℝ))
    (hF_uhc : IsUpperHemicontinuous F S)
    (hF_nonempty : ∀ x ∈ S, (F x).Nonempty)
    (hF_convex : ∀ x ∈ S, Convex (F x))
    (hF_image : ∀ x ∈ S, F x ⊆ S) :
    ∃ x ∈ S, x ∈ F x
```

### Mathematical Facts

- Mixed strategy simplex Δ(Sᵢ) is compact and convex
- Product Δ = ∏ᵢ Δ(Sᵢ) is compact and convex (Tychonoff)
- Best response BRᵢ(σ₋ᵢ) = argmax of expected payoff: closed (upper hemi-continuous)
- Best response BRᵢ(σ₋ᵢ) is nonempty (extreme value theorem) and convex (linearity of expectation)
- Joint best response BR(σ) = ∏ᵢ BRᵢ(σ₋ᵢ) is UHC, nonempty, convex
- Fixed point of BR = Nash equilibrium

### Lean 4 / Mathlib Considerations

- `MvPolynomial` or `Finsupp`: for multilinear payoff extension
- `Mathlib.Topology.Algebra.Module.Convex`: convex sets and Carathéodory
- `Mathlib.Topology.Algebra.Order`: extreme value theorem
- `Mathlib.Probability.ProbabilityMassFunction`: probability distributions on finite types
- `ProbabilityMassFunction.support`: mixed strategies with Finsupp

## Suggested Approach

### Phase 1: OBSERVE
1. Read `BrouwerFixedPointOQ04.lean` fully — understand the Kakutani axiom format
2. Check if there's already any Nash equilibrium formalization in Mathlib
3. Look for `MixedStrategy` or `ProbabilityMassFunction` on finite types
4. Check extreme value theorem for compactness of argmax

### Phase 2: ORIENT
1. Define `FiniteGame`: strategy sets as `Fin n → Fin k` or `Fintype`
2. Define `MixedStrategy i`: probability distribution over `S i`
3. Show best-response is UHC: requires compactness + extreme value theorem
4. Identify which Mathlib lemmas handle the convexity of argmax

### Phase 3: DECIDE
1. If definitions work out: formalize full Nash equilibrium theorem
2. If best-response UHC is hard: state it as a lemma and focus on the Kakutani application
3. Simplify: 2-player zero-sum game first (classic Nash for matrix games)

### Phase 4: ACT
```lean
structure FiniteGame (n : ℕ) where
  strategyCount : Fin n → ℕ
  payoff : ∀ i, (∀ j, Fin (strategyCount j)) → ℝ

def MixedStrategyProfile (n : ℕ) (g : FiniteGame n) : Type :=
  ∀ i : Fin n, ProbabilityMassFunction (Fin (g.strategyCount i))

theorem nash_equilibrium_exists (n : ℕ) (g : FiniteGame n) :
    ∃ σ : MixedStrategyProfile n g, IsNashEquilibrium g σ := by
  apply kakutani_fixed_point_axiom
  -- 1. Mixed strategy simplex is compact convex
  -- 2. Best response is UHC with nonempty convex values
  ...
```

## Related Gallery Proofs

- `brouwer-fixed-point-oq-04`: Parent — Kakutani FPT formalization
- `brouwer-fixed-point`: Brouwer's Fixed Point Theorem (ultimate parent)
- `schauder-fixed-point`: Schauder FPT (related: infinite-dimensional analog)

## Quality Assessment

- **Tractability**: 5/10 — clear path, but best-response UHC needs care
- **Significance**: 8/10 — Nobel Prize-level application, high prestige
- **Domain**: Topology / game theory / economics
- **Risk**: Medium-high — mixed strategy formalization requires probability infrastructure
