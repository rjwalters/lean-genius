# Problem: abel-ruffini-oq-09
## Differential Galois theory and Liouville's theorem on integration

**Status**: in-progress (ACT phase)
**Tractability**: 5/10 (highest)
**Summary**: Proved polynomial Risch obstruction. 3 axioms for full theory. Gallery entry created.

---

## Session 2026-05-03 (Session 1) — Polynomial Obstruction Proved

**Mode**: FRESH
**Outcome**: progress — polynomial obstruction fully proved, gallery entry created

### What I Did

1. **Surveyed the problem**: Confirmed `liouville-theorem` covers the WRONG theorem (approximation/transcendence, 1844). The oq-09 problem is the integration theorem (1835) — differential algebra, not Diophantine approximation.

2. **Designed the approach**: The Risch ODE for ∫e^(-x²)dx is Q' - 2xQ = 1. The polynomial case is solvable by a clean degree-raising argument. The full theory requires axioms (differential Galois theory not in Mathlib).

3. **Created `proofs/Proofs/AbelRuffiniOQ09.lean`** (379 lines):
   - `DiffField` typeclass + 6 basic identities
   - 3 axioms: `liouville_integration_theorem`, `risch_exp_criterion_gaussian`, `gaussian_not_elementary`
   - **Key lemma**: `risch_ode_coeff_top` — coeff(p'-C(2)·X·p, natDeg+1) = -2·leadingCoeff(p)
   - **Main theorem**: `no_poly_risch_soln` — ∀p, p'-C(2)·X·p ≠ 1 (0 sorries)
   - Supporting theorems: degree-raising, pointwise form, elementary contrast (∫eˣ case)
   - Abel-Ruffini analogy documented

4. **Created gallery entry**: `src/data/proofs/abel-ruffini-oq-09/` (meta.json, annotations.json, index.ts, tacticStates.json)

5. **Fixed bugs during development**:
   - Wrong scalar notation `2 • (X * p)` → `Polynomial.C 2 * (Polynomial.X * p)` (type compatibility)
   - Removed false theorem `risch_monomial_obstruction` (counterexample: p=C(-1/2) satisfies L[p]=X)
   - Fixed `no_poly_risch_constant` p=0 case: used `Polynomial.C_eq_zero.mp` not `Polynomial.C_injective`
   - Fixed `risch_ode_coeff_top`: `push_cast` before `rw [h0]`, added `ring`

### Key Findings

- The degree-raising vs degree-preserving dichotomy (L₂ vs L₁) is the structural core
- `Polynomial.funext` works for converting pointwise to polynomial equality
- Mathlib has no Picard-Vessiot theory — gap is >1000 lines
- The polynomial → rational extension requires partial fraction pole analysis (axiomatized)

### Files Modified

- `proofs/Proofs/AbelRuffiniOQ09.lean` (created, 379 lines, 3 axioms, 0 sorries, 18 theorems)
- `src/data/proofs/abel-ruffini-oq-09/meta.json` (created)
- `src/data/proofs/abel-ruffini-oq-09/annotations.json` (created)
- `src/data/proofs/abel-ruffini-oq-09/index.ts` (created)
- `src/data/proofs/abel-ruffini-oq-09/tacticStates.json` (created)
- `src/data/research/problems/abel-ruffini-oq-09.json` (knowledge fields updated)

### Next Steps

1. **Reduce axiom count**: Extend polynomial obstruction to rational functions via partial fraction analysis. If Q = p/q solves Q' - 2xQ = 1, analyze pole orders at roots of q to show poles cannot cancel — reducing to polynomial case.
2. **Build DiffField instance for ℝ(x)**: Connect abstract typeclass to Mathlib's `RatFunc` with standard derivative.
3. **Prove L₁ surjectivity**: ∫p(x)eˣ elementary for all polynomials p, by induction on degree.
