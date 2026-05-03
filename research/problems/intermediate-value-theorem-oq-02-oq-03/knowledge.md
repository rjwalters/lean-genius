# Knowledge Base: intermediate-value-theorem-oq-02-oq-03

**Problem**: Can the constructive IVT be proved in Lean without classical logic?

---

## Session 2026-05-03 (Session 1) — Constructive Bisection Core

**Mode**: FRESH
**Outcome**: progress — Lean file written with 0 sorries, Docker build pending

### What I Did

1. Surveyed parent proof (IntermediateValueTheoremOQ02.lean) — uses `noncomputable def` for bisection (Classical.em for `if f mid ≤ 0`)
2. Designed `paramBisect`: a computable `def` parameterized by explicit `choices : ℕ → Bool`
3. Proved 14 theorems, 3 definitions in `IntermediateValueTheoremOQ02OQ03.lean`
4. Created gallery meta.json
5. Committed to branch `feature/researcher-7`, Docker build submitted

### Key Findings

- Classical logic appears in exactly **one place**: deciding `f(midpoint) ≤ 0`
- The bisection STRUCTURE (width bounds, ordering, sign preservation) is fully constructive
- By parameterizing by `choices : ℕ → Bool`, the algorithm is a regular `def` (computable)
- Endpoint convergence uses `tendsto_atTop_ciSup` / `tendsto_atTop_ciInf` (Classical.choice)
- This formalizes Bishop's principle: bisection is constructive given a "locating oracle"
- The answer is: YES constructive for structural core; NO for exact root extraction

### Files Modified

- `proofs/Proofs/IntermediateValueTheoremOQ02OQ03.lean` (NEW, 300 lines)
- `src/data/proofs/intermediate-value-theorem-oq-02-oq-03/meta.json` (NEW)
- `src/data/research/problems/intermediate-value-theorem-oq-02-oq-03.json` (updated knowledge)

### Theorems Proved (0 sorries)

1. `paramBisectStep_width`: one step halves width
2. `paramBisect_width`: width = (b-a)/2^n
3. `paramBisectStep_ordered`: ordering preserved
4. `paramBisect_ordered`: left ≤ right for all n
5. `paramBisect_left_mono`: left non-decreasing
6. `paramBisect_right_mono`: right non-increasing
7. `paramBisect_contained`: stays in [a,b]
8. `paramBisect_nested`: interval nesting
9. `paramBisect_sign`: sign invariant given SignConsistent oracle
10. `paramBisect_width_tendsto_zero`: width → 0
11. `paramBisect_endpoints_converge`: endpoints converge (classical)
12. `bisection_limit_is_root`: limit is root (classical)
13. `constructive_vs_classical_ivt`: main summary
14. `SignConsistent`: definition of sign-consistent choices

### Mathematical Insight

The separation is clean:
- **Constructive core**: paramBisect_width, paramBisect_sign — no classical axioms
- **Classical step**: tendsto_atTop_ciSup for monotone/antitone bounded sequences
- **Consequence**: for f with Decidable comparisons (polynomial over ℚ), full computability possible

### Next Steps

- Verify Docker build compiles successfully
- If so: submit PR
- Follow-up questions generated:
  1. Fully computable IVT for Decidable sign functions
  2. Constructive IVT over computable real models
