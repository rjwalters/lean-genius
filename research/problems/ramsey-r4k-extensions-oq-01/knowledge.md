# Knowledge Base: ramsey-r4k-extensions-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

- Goal: prove R(4,k) ≥ ck²/log k using probabilistic lower bound argument
- Method: random 2-coloring of Kₙ with edge prob p, bound E[mono K₄ + blue Kₖ] < 1
- If expectation < 1, then by first moment method a good coloring exists

---

## Insights

- Probability setup: color each edge of Kₙ red with prob p = c'(log k/k)^{1/3}
- E[red K₄] = C(n,4) · p⁶ — binomial coeff times probability of 6 specific edges being red
- E[blue Kₖ] = C(n,k) · (1-p)^{C(k,2)}

- Alternative (Paley graph, deterministic):
  - For prime q ≡ 1 (mod 4), Paley graph on ℤ/qℤ: connect i,j iff i-j is a QR
  - Known: ω(Paley(q)) = O(√q log q) and α(Paley(q)) = O(√q log q)
  - So R(4,k) ≥ q for q ≈ ck²/log²k — weaker but deterministic

- Mathlib probability: `PMF`, `MeasureTheory.Measure.pi` for product measures

---

## Dead Ends

- Full probability model in Lean is complex; may need to work at a higher level of abstraction
- The Paley graph approach avoids measure theory but requires quadratic residue theory over finite fields
