# Budan's Theorem (descartes-rule-of-signs-oq-02)

## Problem Summary

Budan's theorem (1807) generalizes Descartes' Rule of Signs to count roots in
any interval (a,b], using the sign variation count V_p(x) of the derivative
evaluation sequence [p(x), p'(x), ..., p^(n)(x)].

**Main result**: #roots in (a,b] ≤ V_p(a) - V_p(b), with even parity gap.

## Session 2026-03-24 (Session 1) — Initial Formalization

**Mode**: FRESH
**Outcome**: progress (substantial infrastructure + key results)

### What I Did
- Created `proofs/Proofs/DescartesRuleOfSignsOQ02.lean` (418 lines)
- Defined iterated derivative (`iterDeriv`), Budan-Fourier sequence, sign changes
- Proved Rolle's theorem for polynomials (fully proved)
- Proved root isolation certificates (0-root, 1-root, 2-root) from axioms
- Proved n+1 roots → n derivative roots (fully proved)
- Set up Descartes recovery framework (from Budan a=0, b→∞)
- Created gallery entry with full metadata

### Key Findings
- `iterDeriv_eq_zero` beyond degree follows from `eq_C_of_natDegree_eq_zero`
- Root isolation certificates use parity elegantly: V(a)-V(b)=1 + parity → exactly 1 root
- `Fin.castSucc_lt_succ` is a proof term in current Lean, use `i.castSucc_lt_succ`
- Mathlib has no Budan-Fourier infrastructure at all — everything is original

### Files Modified
- `proofs/Proofs/DescartesRuleOfSignsOQ02.lean` (new, 418 lines)
- `src/data/proofs/descartes-rule-of-signs-oq-02/` (new gallery entry)
- `src/data/research/problems/descartes-rule-of-signs-oq-02.json`

### Stats
- 28 theorems, 9 definitions, 3 axioms, 7 sorries
- Key proved: rolle_polynomial, n_roots_derivative_roots, root isolation certificates
- Key axiomized: budan_upper_bound, budan_parity, budanCount_large

### Next Steps
- Prove `iterDeriv_eval_zero` (p^(k)(0) = k! * coeff k)
- Prove `rootsInInterval_split` (interval additivity)
- Prove `budanCount_le_natDegree` (sign changes ≤ degree)
- Submit remaining sorries to Aristotle
