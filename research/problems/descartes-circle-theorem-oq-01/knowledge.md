# Knowledge Base: descartes-circle-theorem-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The **Descartes Circle Theorem**: for four mutually tangent circles with signed
curvatures `k₁,k₂,k₃,k₄` (curvature `= ±1/radius`, negative for the enclosing
circle),

  `(k₁+k₂+k₃+k₄)² = 2·(k₁²+k₂²+k₃²+k₄²)`.

This is distinct from Mathlib's *Descartes' Rule of Signs* (a polynomial-roots
result); the circle theorem is not a named Mathlib result.

---

## Insights

- The relation, read as a **quadratic in `k₄`**, is equivalent to the perfect-square
  condition `(k₄ − (k₁+k₂+k₃))² = 4·(k₁k₂+k₂k₃+k₃k₁)`. This single ring identity
  (`linear_combination -h`, both directions) is the whole algebraic content.
- Solving gives the two **Soddy circles**
  `k₄ = (k₁+k₂+k₃) ± 2·√(k₁k₂+k₂k₃+k₃k₁)`.
- The symmetric product `D = k₁k₂+k₂k₃+k₃k₁` is **automatically nonnegative** whenever
  the relation holds, since `4D = (k₄−S)² ≥ 0`. So `√D` is always well defined for any
  genuine Descartes tuple — no extra hypothesis needed in the forward direction.
- Factoring `(k₄−S)² − (2√D)² = (k₄−S−2√D)(k₄−S+2√D) = 0` via `Real.sq_sqrt` reduces the
  forward solution step to `mul_eq_zero`.
- **Vieta**: the two Soddy curvatures sum to `2(k₁+k₂+k₃)` and have product
  `(k₁+k₂+k₃)² − 4D`.

---

## Session 2026-06-16 (Session 1) - Algebraic core formalized

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms; build-verified)

### What I Did
- Sympy-verified the quadratic rewriting and both Soddy branches.
- Wrote `proofs/Proofs/DescartesCircleTheorem.lean`:
  - `descartesRel` (the curvature relation)
  - `descartesRel_iff_sq` (relation ↔ perfect square in `k₄`)
  - `descartes_symmProd_nonneg` (D ≥ 0 from the relation)
  - `descartes_soddy_forward` / `descartes_soddy_backward`
  - `descartes_circle` (headline iff)
  - `soddy_sum`, `soddy_prod` (Vieta relations)

### Scope / Honesty
This formalizes the **curvature arithmetic** of the theorem and the Soddy-circle
solution. It does **not** derive the relation from the planar tangency geometry
(centers in ℂ + tangency distance equations) — that derivation is a separate, larger
piece of work. Reported as the algebraic core, not the full geometric theorem.

### Next Steps
- (Optional follow-up OQ) Derive the curvature relation from explicit tangency:
  centers `zᵢ ∈ ℂ` with `|zᵢ−zⱼ| = |1/kᵢ + 1/kⱼ|`, leading to the
  complex Descartes theorem `(Σ kᵢzᵢ)² = 2 Σ (kᵢzᵢ)²` (Lagarias–Mallows–Wilks).

---

## Dead Ends

None — the algebraic route worked directly.
