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
- Prove `budanCount_smul`: need signChangesInList invariance under uniform nonzero scaling
- Prove `budanCount_zero_eq_coeff_sign_changes`: need signChangesInList invariance under element-wise positive scaling
- Both sorries reduce to the same core problem: proving signChangesInList is invariant when list elements are scaled by (positive) factors. Key blocker: List.filter with decide predicates on ℝ is hard to manipulate in Lean 4. Consider defining a recursive signList that avoids filter+map composition.

## Session 2026-03-24 (Session 3) — Proving 2 More Sorries (4→2)

**Mode**: REVISIT
**Outcome**: progress (2 sorries eliminated, 4→2 remaining)

### What I Did
- Proved `chainVariation_budanChain`: Budan chain's variation equals budanCount, via List.ext_getElem converting List.finRange ↔ List.range
- Proved `descartes_from_budan`: Descartes' rule as special case of Budan
  - Built `list_bounded` + `multiset_bounded`: every multiset of reals has an upper bound
  - Used `Multiset.filter_congr` to show filter (0 < ·) = filter (0 < · ∧ · ≤ B) when all positive roots ≤ B
  - Applied `budan_upper_bound` with V(B)=0 for large B
- Attempted `budanCount_smul` and `budanCount_zero_eq_coeff_sign_changes` — both need signChangesInList scaling invariance
  - Wrote `countAdjacentDiffs_neg`, `filter_sign_pos_mul`, `filter_sign_neg_mul` helpers
  - Hit blocker: List.filter in Lean 4 uses Bool predicates via decide, making filter_cons manipulation with noncomputable DecidableEq ℝ very difficult
  - Left as documented sorries with clear proof sketches

### Key Findings
- `Multiset.induction` has implicit args ⦃a⦄ {s} — cannot use `fun a _ ih =>` in lambda; must use list-based approach
- Pattern-matched variables from `| a :: t =>` not available in `by` blocks in recursive defs
- `List.filter_cons` in Lean 4 uses `Bool` predicates; `decide` on `(x : ℝ) ≠ 0` is noncomputable, making simp manipulation of filter results very difficult
- `Multiset.filter_congr` works well for showing predicate equivalence on filter

### Files Modified
- `proofs/Proofs/DescartesRuleOfSignsOQ02.lean` (502→552 lines, 4→2 sorries)
- `src/data/proofs/descartes-rule-of-signs-oq-02/meta.json` (updated stats)
- `src/data/research/problems/descartes-rule-of-signs-oq-02.json` (updated knowledge)

### Stats
- 552 lines, 36 theorems, 8 definitions, 3 axioms, 2 sorries
- 2 sorries eliminated: descartes_from_budan, chainVariation_budanChain
- 2 remaining: budanCount_zero_eq_coeff_sign_changes, budanCount_smul (both need sign scaling invariance)
