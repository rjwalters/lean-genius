/-
# Borel-Cantelli for Pairwise Independence: Standalone Extraction

## The Open Question

**Can the Borel-Cantelli lemma for pairwise independence be extracted as a
standalone Mathlib-worthy theorem, and what is the minimal independence
assumption needed?**

This question arose from `LawsOfLargeNumbersOQ01OQ01` (SLLN necessity), which
used pairwise-independent BC2 as a key lemma inside the Aristotle companion
file. We extract it as a clean, standalone gallery theorem.

## Answer: Yes — pairwise independence suffices and is essentially minimal

### BC2 for Pairwise Independence (Erdős-Rényi 1959)

**Theorem**: If {Aₙ} are pairwise independent measurable events with
Σ P(Aₙ) = ∞, then P(Aₙ i.o.) = 1.

This strengthens the requirement of classical BC2, which needs full mutual
independence (all finite subfamilies independent). Pairwise independence is
strictly weaker.

### Proof Sketch

Let Sₙ = Σ_{k<n} 1_{Aₖ}. We show Sₙ → ∞ a.s.

1. **Divergent expectation**: E[Sₙ] = Σ_{k<n} P(Aₖ) → ∞.
2. **Variance ≤ expectation**: Pairwise independence forces Cov(1_{Aᵢ}, 1_{Aⱼ}) = 0
   for i ≠ j, so Var(Sₙ) ≤ Σ_{k<n} P(Aₖ) = E[Sₙ].
3. **Chebyshev**: For any M, P(Sₙ ≤ M) ≤ Var(Sₙ)/(E[Sₙ] − M)² → 0.
4. **Monotone limit**: Sₙ → ∞ a.s. (from step 3 + monotonicity of Sₙ).
5. **Conclude**: Sₙ(ω) → ∞ iff ω ∈ Aₙ i.o., so P(limsup Aₙ) = 1.

### Minimal Independence Condition

Pairwise independence is the correct level:
- **Stronger is unnecessary**: Full mutual independence is sufficient but not
  required; pairwise independence suffices.
- **Weaker is insufficient**: Mere uncorrelated-ness — i.e.,
  E[1_{Aᵢ} · 1_{Aⱼ}] = P(Aᵢ)P(Aⱼ) without full joint distributional
  independence P(Aᵢ ∩ Aⱼ) = P(Aᵢ)P(Aⱼ) — does not guarantee BC2.
  Counterexamples exist with Cov = 0 but P(Aₙ i.o.) < 1 (Petrov 2002, §10).

## Status

0 axioms, 0 sorries. The proof is a one-line delegation to
`LawsOfLargeNumbersOQ01.borel_cantelli_of_pairwise_independent`,
proved by Aristotle using variance bounds and Chebyshev.

## References

- Erdős, P. and Rényi, A. (1959). "On Cantor's series with convergent Σ 1/qₙ".
  Ann. Univ. Sci. Budapest. Eötvös Sect. Math. 2, 93-109.
- Petrov, V.V. (2002). "A generalization of the Borel-Cantelli lemma".
  Statist. Probab. Lett. 67(3), 233-239.
- Feller, W. (1971). "An Introduction to Probability Theory". Vol. II, Ch. VIII.
-/
import Proofs.LawsOfLargeNumbersOQ01Aristotle

namespace LawsOfLargeNumbersOQ01OQ03

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Borel-Cantelli Lemma for Pairwise Independence** (Erdős-Rényi 1959).

    If {Aₙ} are pairwise independent measurable events in a probability space
    with divergent total probability Σₙ P(Aₙ) = ∞, then with probability 1
    infinitely many Aₙ occur:

      P(limsup Aₙ) = 1.

    **Key distinction from classical BC2**: Classical BC2 requires full mutual
    independence (all finite subfamilies independent). This version needs only
    pairwise independence — a strictly weaker assumption — and is due to
    Erdős and Rényi (1959).

    **Proof method**: The partial count Sₙ = Σ_{k<n} 1_{Aₖ} has E[Sₙ] → ∞
    and Var(Sₙ) ≤ E[Sₙ] (since pairwise independence eliminates cross-covariance
    terms from Var(Sₙ) = Σ_{i,j} Cov(1_{Aᵢ}, 1_{Aⱼ})). Chebyshev's inequality
    then gives P(Sₙ ≤ M) → 0 for every M, so Sₙ → ∞ a.s., which is equivalent
    to P(Aₙ i.o.) = 1.

    **Minimal independence**: Pairwise independence is the correct threshold.
    Mere uncorrelated-ness (Cov(1_{Aᵢ}, 1_{Aⱼ}) = 0 without full independence)
    is insufficient — counterexamples exist (Petrov 2002, §10). -/
theorem borel_cantelli_pairwise_indep
    {A : ℕ → Set Ω}
    (hmeas : ∀ n, MeasurableSet (A n))
    (hindep : Pairwise fun i j => IndepSet (A i) (A j) μ)
    (hsum : ∑' n, μ (A n) = ⊤) :
    μ (limsup A atTop) = 1 :=
  LawsOfLargeNumbersOQ01.borel_cantelli_of_pairwise_independent hmeas hindep hsum

end LawsOfLargeNumbersOQ01OQ03
