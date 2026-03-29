# Knowledge Base: roth-theorem-k3-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The open question asks about formalizing quantitative bounds for r₃(N), the maximum size of a 3-AP-free subset of [N]. The parent proof (RothTheorem.lean) has the qualitative result r₃(N) = o(N) fully verified with 0 axioms and 0 sorries.

The key infrastructure already exists:
- APFree definition on ZMod N
- Fourier analysis framework (character theory, Parseval, triple count identity)
- Density increment lemma: AP-free set of density δ → AP-free set of density ≥ δ + δ²/100 in smaller modulus
- Final theorem via Mathlib's corners theorem chain

---

## Insights

1. **r₃(N) definition is novel**: No prior formalization of the Roth number in this gallery. Defined as Finset.sup over AP-free subsets of ZMod N.

2. **Density increment doesn't track modulus decay**: The existing density_increment_lemma gives M < N and M > 0 but no lower bound on M. For quantitative bounds, we need M ≥ √N (Roth) or better. The proof has M = gcd(val(r), N) which could be analyzed further.

3. **Iteration theorem must be careful**: Naively iterating the density increment k times is INCORRECT for arbitrary k — when the modulus reaches 1, we can't continue. The correct approach is well-founded induction on N.

4. **max_iterations_bound is provable**: Pure arithmetic: if δ + kδ²/100 > 1 then k > ⌊100/δ²⌋. This is the key link between density increment count and the initial density.

5. **Five bound landscape**: Roth O(N/log log N), Behrend Ω(N·exp(-c√log N)), Bloom-Sisask O(N/(log N)^{1+c}), Kelley-Meka O(N·exp(-c(log N)^{1/12})), crude O(√N from simple iteration).

6. **Behrend construction most tractable**: Among the sorry'd bounds, the Behrend lower bound (sphere projection) is most self-contained and could be next session's target.

---

## Dead Ends

1. **Density increment iteration theorem (unlimited k)**: Attempted to prove ∀ k, ∃ M B with density ≥ δ + kδ²/100. This is FALSE for large k — modulus reaches 1 and iteration cannot continue. Removed and replaced with correct max_iterations_bound.

2. **apfree_density_lt_one with strict inequality**: The trivial bound only gives ≤, not <. Getting strict inequality requires actually using the AP-free property (e.g., for N ≥ 2, ZMod N has 3-APs in its full set).
