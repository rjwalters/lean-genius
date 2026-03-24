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

## Session 2026-03-24 (Session 2) — Proving Infrastructure Sorries

**Mode**: REVISIT (continuing existing work)
**Outcome**: progress (3 sorries eliminated, 17 new theorems proved)

### What I Did
- Proved `iterDeriv_eval_zero`: p^(k)(0) = k! * coeff k, the key Taylor coefficient identity
  - Required general coefficient formula `iterDeriv_coeff` via descFactorial
  - Required custom `poly_eval_at_zero` (Mathlib's `eval_zero` is for zero polynomial, not evaluation at zero)
  - Required `iterDeriv_eq_iterate` connecting custom def to Function.iterate
- Proved `budanCount_le_natDegree`: V_p(x) ≤ degree of p
  - Built `countAdjacentDiffs_le` (combinatorial bound on sign changes in ±1 lists)
  - Built `signChangesInList_le_pred_length` (sign changes ≤ list length - 1)
- Proved `rootsInInterval_split`: interval additivity for root counts
  - Used Multiset.ext + count_filter + 4-way case split on real predicates
  - linarith handles contradictory cases
- Proved `iterDeriv_C_mul`: derivative commutes with constant multiplication

### Key Findings
- `Polynomial.eval_zero` in current Mathlib means `eval x (0 : R[X]) = 0`, NOT `p.eval 0 = p.coeff 0`
- Must prove `p.eval 0 = p.coeff 0` manually via `Finset.sum_eq_single_of_mem` and `zero_pow`
- `Nat.descFactorial_succ n k` returns `(n-k) * n.descFactorial k` (factor on LEFT), need `mul_comm` for ring
- `Function.iterate_succ'` is the correct direction: `f^[n+1] = f ∘ f^[n]` (not `f^[n] ∘ f`)
- omega cannot see through `let` bindings from `unfold` — need `calc` or explicit `rfl` rewrites

### Files Modified
- `proofs/Proofs/DescartesRuleOfSignsOQ02.lean` (418→502 lines, 28→45 theorems, 7→4 sorries)
- `src/data/proofs/descartes-rule-of-signs-oq-02/meta.json` (updated stats)
- `src/data/research/problems/descartes-rule-of-signs-oq-02.json` (updated knowledge)

### Stats
- 502 lines, 45 theorems, 9 definitions, 3 axioms, 4 sorries
- 3 sorries eliminated: iterDeriv_eval_zero, budanCount_le_natDegree, rootsInInterval_split
- 4 remaining: descartes_from_budan, budanCount_smul, budanCount_zero_eq_coeff_sign_changes, chainVariation_budanChain

### Next Steps
- Prove `descartes_from_budan`: bound positive roots using Multiset finiteness, then V(B)=0
- Prove `budanCount_smul`: need positive-scaling-preserves-sign-changes lemma
- Prove `budanCount_zero_eq_coeff_sign_changes`: use iterDeriv_eval_zero + positive scaling
- Prove `chainVariation_budanChain`: List.finRange ↔ List.range conversion
