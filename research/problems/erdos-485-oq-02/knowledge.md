# Knowledge Base: erdos-485-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The open question asks whether f(k) → ∞ (the minimum number of terms in P(x)²
for polynomials with k terms) can be proved COMBINATORIALLY via sumset bounds,
rather than algebraically via height theory (Schinzel-Zannier 2009).

The combinatorial approach: support(P²) relates to the sumset A + A where
A = support(P). If no coefficient cancellation occurs, |A + A| ≥ 2|A| - 1
gives termCount(P²) ≥ 2k - 1.

---

## Insights

1. **Sumset containment always holds**: support(P²) ⊆ support(P) + support(P).
   This is because coeff(P², n) = Σ_{a+b=n} c_a·c_b, and if nonzero, some
   pair (a,b) with a ∈ supp(P), b ∈ supp(P) must contribute.

2. **Positive-coefficient case is complete**: When all coefficients ≥ 0,
   no cancellation occurs. Every sumset element gets a positive coefficient
   in P². So support(P²) = A + A exactly, giving termCount(P²) ≥ 2k - 1.

3. **Cancellation barrier**: Mixed-sign coefficients can cancel. Example:
   P = 1 - x² - (1/2)x⁴. The x⁴ coefficient of P² equals
   c₀·c₄ + c₂·c₂ + c₄·c₀ = (-1/2) + 1 + (-1/2) = 0.
   So 4 ∈ A + A but 4 ∉ support(P²).

4. **The gap**: The combinatorial approach proves f_+(k) → ∞ (positive coefficients)
   but NOT f(k) → ∞ (general polynomials). Bridging this gap requires controlling
   cancellation — an algebraic, not purely combinatorial, phenomenon.

5. **Mathlib gap**: The sumset bound |A + A| ≥ 2|A| - 1 is not in Mathlib.
   Provable via the min/max chain argument but requires nontrivial Finset work.

---

## Dead Ends

- Direct application of |A + A| ≥ 2|A| - 1 to general polynomials fails
  because cancellation can eliminate arbitrarily many sumset elements.
- The trivial upper bound on cancellation positions (≤ k²) is too weak to help.

---

## Next Steps

- Prove `sumset_card_lower_bound` in Lean (the 1 sorry remaining)
- Explore whether Freiman-Ruzsa inverse sumset theorems help bound cancellation
- Consider: for random polynomials, how many cancellations occur on average?
