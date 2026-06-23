# Knowledge Base: erdos-1007-oq-01-oq-01

Is minEdges monotone in d?

---

## Session 2026-03-24 (Session 1) - Full Structural Analysis

**Mode**: FRESH
**Outcome**: completed — 388 lines, 32 theorems, 0 axioms, 0 sorries

### What Was Done

Created `Erdos1007OQ01OQ01.lean` with a comprehensive structural analysis of the
monotonicity conjecture for minEdges(d).

**Key approach**: Introduced `MinEdgesConstraints` structure to abstract over any
candidate for the true minEdges function, avoiding dependence on placeholder values
for d ≥ 6 used in the parent file.

### Theorems Proved

1. **`knownMinEdges_monotone`**: The 6 known values (0,1,3,6,9,15) are monotone.
2. **`monotone_on_known`**: Any constrained function is monotone on [0,5].
3. **`monotone_iff_consecutive`**: Full monotonicity ↔ f(d) ≤ f(d+1) for all d.
4. **`monotone_reduces_to_large`**: Monotonicity reduces to d ≥ 5 (known values handle the rest).
5. **`deficiency_bound_implies_monotone`** (KEY): If δ(d) = C(d+1,2) - f(d) ≤ d for all d ≥ 1,
   then f is monotone. Proof: f(d₁) ≤ C(d₁+1,2) ≤ C(d₂,2) ≤ f(d₂) using Pascal's rule
   C(d+1,2) - d = C(d,2).
6. **`monotone_far_apart`**: Unconditional monotonicity when C(d₁+1,2) ≤ d₂.
7. **`critical_gap`**: f(5) ≤ f(6) iff f(6) ≥ 15.
8. **`optimal_implies_monotone'`**: Complete graph optimality → monotonicity (via deficiency bound).
9. **`half_quadratic_implies_monotone`**: f(d) ≥ C(d,2) for d ≥ 2 → monotonicity.
10. **`growth_bracket`**: d ≤ f(d) ≤ d(d+1)/2 for all d ≥ 1.

### Key Insights

- **Deficiency bound δ(d) ≤ d** is the simplest sufficient condition for monotonicity.
  It says C(d+1,2) overshoot is at most d. All known values satisfy this (δ(4)=1≤4).
- **Critical gap at d=5→6**: Need f(6) ≥ 15 but only know 6 ≤ f(6) ≤ 21.
- **Pascal's rule** C(d+1,2) - d = C(d,2) is the algebraic engine: it converts the
  deficiency bound into a lower bound that chains with the upper bound.
- **Half-quadratic sufficiency**: f(d) ≥ C(d,2) is much weaker than optimality but
  still implies monotonicity.

### Files Modified
- `proofs/Proofs/Erdos1007OQ01OQ01.lean` — new file (388 lines)
- `proofs/Proofs.lean` — added import
- `src/data/proofs/erdos-1007-oq-01-oq-01/` — gallery integration
- `src/data/research/problems/erdos-1007-oq-01-oq-01.json` — updated knowledge
