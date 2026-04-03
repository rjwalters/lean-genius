# Knowledge Base: erdos-1155-oq-01-oq-01

Does f(n)/n^{3/2} converge? Determine the limit.

---

## Problem Understanding

Sub-question of Erdős #1155 OQ-01: If the triangle removal process on K_n terminates
with f(n) edges, does the ratio f(n)/n^{3/2} → L for some specific constant L > 0?

This is STRICTLY STRONGER than the parent Erdős Θ(n^{3/2}) conjecture:
- Erdős OQ-01: ∃ c₁, c₂ > 0: c₁·n^{3/2} ≤ f(n) ≤ c₂·n^{3/2} (bounded ratio)
- This OQ: f(n)/n^{3/2} → L (convergent ratio)

BFL (2015) established f(n) = n^{3/2 + o(1)}, showing the exponent is 3/2.
The o(1) means the ratio is between n^{-ε} and n^ε for all ε > 0 — this does NOT
prevent convergence, but also does not establish it.

---

## Session 2026-04-03 (Session 1) - Formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Surveyed the parent problem OQ-01 (Erdos1155OQ01.lean: 20 theorems, 0 sorries)
- Surveyed the sibling OQ-07 (K_r-removal generalization)
- Identified the mathematical content: convergence question is formally open
- Created `Erdos1155OQ01OQ01.lean` with 13 theorems, 0 sorries, 6 inherited axioms
- Created gallery entry `src/data/proofs/erdos-1155-oq-01-oq-01/`

### Key Findings
- The convergence question is genuinely open — no proof or disproof known
- The key hierarchy: convergenceConjecture ⟹ erdos_1155_conjecture ⟹ BFL
- Limit uniqueness follows from Hausdorff separation (proved via tendsto_nhds_unique)
- The limsup/liminf characterization gives a useful equivalent: convergence ↔ limsup = liminf = L
- The metric Cauchy criterion provides the classical ε-N formulation
- If convergence holds, L is determined by the BFL differential equations (but L is not known)
- The limit (if it exists) satisfies: for any δ > 0, (L-δ)·n^{3/2} ≤ f(n) ≤ (L+δ)·n^{3/2} eventually

### Mathematical Content

The file covers:
1. `convergenceConjecture` — ∃ L > 0, f(n)/n^{3/2} → L
2. `convergenceLimit_unique` — Hausdorff uniqueness
3. `convergence_implies_erdos_conjecture` — hierarchy
4. `convergence_implies_bfl` — full BFL hierarchy
5. `convergence_gives_sharp_asymptotics` — (L±δ)·n^{3/2} sandwich
6. `convergence_ratio_in_Ioo` — ε-interval membership
7. `convergence_absolute_deviation` — |r(n) - L| < ε
8. `convergence_implies_bounded_ratio` — L/2 ≤ r(n) ≤ 3L/2
9. `convergence_lower_bound` / `convergence_upper_bound` — one-sided bounds
10. `limsup_liminf_implies_convergence` — ε-characterization → Tendsto
11. `convergence_implies_limsup_eq_liminf` — Tendsto → ε-characterization
12. `convergenceConjecture_iff_metric` — ↔ classical ε-N criterion
13. `strict_hierarchy` — full summary
14. `convergence_implies_optimal_theta` — optimal constants

### Files Modified
- `proofs/Proofs/Erdos1155OQ01OQ01.lean` (created, ~230 lines)
- `src/data/proofs/erdos-1155-oq-01-oq-01/meta.json` (created)
- `src/data/proofs/erdos-1155-oq-01-oq-01/annotations.json` (created)
- `src/data/proofs/erdos-1155-oq-01-oq-01/index.ts` (created)

### Next Steps
- Verify build compiles cleanly
- Check if BFL differential equations can be axiomatized to give a candidate L
- Potential follow-up: axiomatize the specific conjectured value of L from BFL analysis

---

## Insights

- The convergence question is orthogonal to the Θ conjecture: even knowing c₁ ≤ f(n)/n^{3/2} ≤ c₂, the ratio could oscillate
- The precise limit L (if it exists) would come from the fixed point of the differential equations in BFL's proof
- The BFL proof uses the "differential equation method" for random processes; the limit corresponds to the long-time behavior of the ODE solution

## Dead Ends

- Cannot prove convergence from BFL alone (BFL is n^{3/2±ε}, not n^{3/2·(1+o(1))})
- Cannot determine the explicit value of L without new mathematical results
