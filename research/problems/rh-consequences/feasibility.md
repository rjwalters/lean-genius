# Feasibility Check: Riemann Hypothesis Consequences

**Date**: 2025-12-31
**Time spent**: ~15 minutes

## The Problem

Formalize theorems that are conditional on the Riemann Hypothesis:
- RH → Explicit prime counting bounds
- RH → Prime gap bounds
- RH → Mertens function bounds

## Step 1: Key Discovery

**RiemannHypothesis is already defined in Mathlib!**

```lean
-- Mathlib/NumberTheory/LSeries/RiemannZeta.lean:155-158
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2
```

Translation: All non-trivial zeros of ζ lie on the critical line Re(s) = 1/2.

## Step 2: Mathlib Search Results

| Component | In Mathlib? | Notes |
|-----------|-------------|-------|
| `RiemannHypothesis` definition | **YES** | Already formalized |
| Riemann zeta function ζ(s) | **YES** | Full complex definition |
| Completed zeta Λ(s) | **YES** | With Γ factors |
| Functional equation | **YES** | ζ(1-s) = ... |
| Trivial zeros | **YES** | ζ(-2n) = 0 proven |
| ζ(0) = -1/2 | **YES** | Proven |
| Prime Number Theorem | **NO** | Not formalized |
| Chebyshev functions θ, ψ | **NO** | Not defined |
| Prime counting asymptotics | **NO** | No li(x) ~ π(x) |
| Mertens function M(x) | **NO** | Not defined |
| L-functions (Dirichlet) | **YES** | Full infrastructure |

## Step 3: Classical RH Consequences

### What We'd Want to Prove

1. **Explicit Prime Counting** (von Koch 1901):
   RH → |π(x) - li(x)| = O(√x log x)
   **Problem**: π(x) asymptotic needs PNT first

2. **Prime Gaps** (Cramér):
   RH → p_{n+1} - p_n = O(√p_n log p_n)
   **Problem**: Needs prime gap theory

3. **Mertens Function**:
   RH → |M(x)| = O(√x) where M(x) = Σ_{n≤x} μ(n)
   **Problem**: M(x) not defined, would need Möbius sum

4. **Lindelöf on Critical Line**:
   RH → |ζ(1/2 + it)| = O(t^ε)
   **Problem**: Growth bounds need careful analysis

### What We Actually Can Do

1. **State consequences as formal propositions**
2. **Prove trivial lemmas** (e.g., if RH then trivial zeros unchanged)
3. **Define missing functions** (Mertens, Chebyshev)
4. **Document gaps between RH and consequences**

## Step 4: Milestone Tractability

| Milestone | Tractability | Notes |
|-----------|--------------|-------|
| State RH (already done!) | **10/10** | In Mathlib |
| Define Mertens function M(x) | **7/10** | Sum of μ(n) |
| State "RH → |M(x)| = O(√x)" | **6/10** | Need O notation for NT |
| Prove RH → trivial facts | **8/10** | Simple implications |
| Prove non-trivial RH consequence | **2/10** | Needs PNT infrastructure |
| Document RH consequences | **9/10** | Survey approach |

## Step 5: Decision

**Assessment**: SURVEY

**Rationale**:
1. RH is already formalized - that's the hard part for statements
2. Can define missing functions (Mertens, Chebyshev)
3. Can state classical consequences as formal propositions
4. Can prove trivial implications
5. Cannot prove substantial theorems without PNT

### What the SURVEY Will Produce

1. **Formal statement** of several RH consequences
2. **Definition** of Mertens function M(x)
3. **Definition** of Chebyshev functions θ(x), ψ(x)
4. **Trivial theorems** showing RH structure
5. **Documentation** of what's needed for full proofs

## Technical Approach

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta

-- Mertens function (sum of Möbius)
def MertensFunction (x : ℕ) : ℤ := ∑ n ∈ Finset.range (x + 1), (if n = 0 then 0 else μ n)

-- RH consequence statement (axiom for now)
axiom rh_implies_mertens_bound : RiemannHypothesis →
  ∃ C : ℝ, C > 0 ∧ ∀ x : ℕ, x ≥ 1 → |(MertensFunction x : ℝ)| ≤ C * Real.sqrt x

-- Chebyshev θ function
noncomputable def chebyshevTheta (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log p
```

## References

- [Mathlib RiemannZeta.lean](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/RiemannZeta.lean)
- Edwards, "Riemann's Zeta Function" (1974)
- Titchmarsh, "The Theory of the Riemann Zeta-Function" (1986)

## Time Budget

~1 hour for SURVEY:
- 20 min: Define Mertens, Chebyshev functions
- 20 min: State RH consequences formally
- 20 min: Prove trivial implications and document
