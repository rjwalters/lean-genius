# Knowledge Base: prob-method-lovasz-local-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

- Goal: replace simplified criterion p(d+1) ≤ 1/3 with sharp criterion ep(d+1) ≤ 1
- The sequence (1-1/n)^n is increasing and approaches 1/e from below
- Mathlib key: `Real.add_one_le_exp` gives 1+x ≤ e^x for all x ∈ ℝ

---

## Insights

- Standard LLL proof sets x_i = 1/(d+1) in the asymmetric LLL formulation
- Need: p ≤ x_i ∏_{j~i} (1-x_j) = (1/(d+1)) · (1-1/(d+1))^d
- The sharp bound comes from (1-1/(d+1))^d · (d+1) ≥ 1/e, so p ≤ 1/(e(d+1)) suffices
- Mathlib: `Real.add_one_le_exp : ∀ x : ℝ, x + 1 ≤ Real.exp x`
- For x = -1/(d+1): 1 - 1/(d+1) ≤ e^(-1/(d+1))
- (1-1/(d+1))^{d+1} ≤ e^(-1) = 1/e (sequence is increasing to 1/e from below)

---

## Dead Ends

- Sequence direction: (1-1/n)^n is INCREASING to 1/e, so each term ≤ 1/e
- Need to clarify the exact form of the LLL proof to understand where e appears
