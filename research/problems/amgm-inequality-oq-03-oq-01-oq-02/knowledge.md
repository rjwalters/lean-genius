# Knowledge Base: amgm-inequality-oq-03-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-06-24 (researcher-1) — COMPLETED

**Result**: `Real.rpow_mean_le_rpow_mean` — single self-contained theorem proving
M_p ≤ M_q for ALL nonzero real p ≤ q, stated on the raw `(∑ wᵢzᵢ^p)^(1/p)`
expression (matching `Real.arith_mean_le_rpow_mean`, the p=1 case). This fills the
explicit TODO in `Mathlib.Analysis.MeanInequalitiesPow`.

**Proof = sign trichotomy**:
- 0 < p ≤ q: Jensen on aᵢ=zᵢ^p with convex t↦t^(q/p).
- p ≤ q < 0: duality M_p(z)=M_{-p}(z⁻¹)⁻¹ reduces to the positive case on z⁻¹.
- p < 0 < q: sandwich M_p ≤ G ≤ M_q via the geometric mean G=∏zᵢ^wᵢ
  (G ≤ M_q is weighted AM-GM on zᵢ^q; M_p ≤ G is its dual).

**Key Mathlib lemmas**: rpow_arith_mean_le_arith_mean_rpow (Jensen),
geom_mean_le_arith_mean_weighted (AM-GM), finset_prod_rpow (∏(fᵢ^r)=(∏fᵢ)^r),
inv_rpow / rpow_neg / rpow_mul, one_div_le_one_div_of_le (inversion antitonicity).

**Verification**: `#print axioms Real.rpow_mean_le_rpow_mean` →
[propext, Classical.choice, Quot.sound]. 0 axioms, 0 sorries.

**Note vs parent**: parent (oq-03-oq-01) + sibling (oq-03-oq-02-oq-01) prove the same
math across two files using a custom `weightedPowerMean` def; the contribution here is
the consolidation into ONE theorem on bare expressions, ready to PR upstream.
