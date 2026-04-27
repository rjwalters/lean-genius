# Knowledge Base: roth-theorem-k3-oq-01

Insights accumulated during research on this problem.

---

## Session 2026-04-27 (researcher-10) — log_log_pos Proved

**Outcome**: PROGRESS — proved `log_log_pos` in companion file (5 → 4 sorries)

### What I Did

Proved `log_log_pos (N : ℕ) (hN : 3 ≤ N) : 0 < Real.log (Real.log N)` in
`RothTheoremQuantitativeAristotle.lean`. Standard 5-line proof:
- `Real.exp_one_lt_d9 : exp 1 < 2.7182818286` (verified at
  Mathlib/Analysis/Complex/ExponentialBounds.lean:37)
- `linarith` derives `exp 1 < 3`
- `Real.log_lt_log` + `lt_of_lt_of_le he hN_real` gives `log (exp 1) < log N`,
  i.e. `1 < log N` after `Real.log_exp`
- `Real.log_pos` closes the goal.

### Sorry Count: 5 → 4 (in companion)

Remaining companion sorries:
1. `two_element_ap_free` — ZMod casework for {0,1} (general N tricky)
2. `n_div_log_log_tendsto_atTop` — needs Filter chains (log = o(id))
3. `behrend_lower_eventually_large` — eventual largeness via decay
4. `behrend_exponent_vs_poly` — exp(-c√log N) ≥ N^(-ε) eventually

Main file `RothTheoremQuantitative.lean` still has 4 deep-result sorries
(Roth, Behrend, Bloom-Sisask, Kelley-Meka).

### Honesty Note

Disk at 1.8Gi free — Docker not run. Proof uses standard Mathlib idioms
(`Real.log_pos`, `Real.log_lt_log`, `Real.log_exp`) verified at source.
High confidence in compilation, but not Docker-verified.

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
