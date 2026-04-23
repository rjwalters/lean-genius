# Knowledge Base: sqrt2-minpoly-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Generalize `Sqrt2Minpoly` (gallery: minpoly ℚ √2 = X² - 2) to show that for any
natural numbers n, k ≥ 2 satisfying the Eisenstein condition (a prime p | n with p^k ∤ n),
the minimal polynomial of n^(1/k) over ℚ is X^k - n.

Key ingredients:
- `Polynomial.irreducible_of_eisenstein_criterion` in Mathlib
- `minpoly.eq_of_irreducible_of_monic` to conclude minimality
- `Real.rpow` for n^(1/k) and `aeval` evaluation to zero

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
