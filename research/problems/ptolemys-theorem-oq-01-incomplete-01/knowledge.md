# Knowledge Base: ptolemys-theorem-oq-01-incomplete-01

## Problem Understanding

Ptolemy Converse: For four distinct unit-circle points, Ptolemy equality implies CCW or CW cyclic order.

The proof uses:
1. Half-angle factorization: exp(iα) - exp(iβ) = 2I·sin((α-β)/2)·exp(i(α+β)/2)
2. Phase cancellation: E₂₃·E₁₄ = E₁₂·E₃₄ (since (θ₂+θ₃)/2 + (θ₁+θ₄)/2 = (θ₁+θ₂)/2 + (θ₃+θ₄)/2)
3. Sine ratio identity: t = sin((θ₂-θ₃)/2)·sin((θ₁-θ₄)/2) / (sin((θ₁-θ₂)/2)·sin((θ₃-θ₄)/2))
4. 8-case sign analysis: t > 0 forces exactly CCW or CW ordering

## Key Insights

- **hcx proof via mul_left_cancel₀**: Cancel the common factor `(2I)²·E₁₂E₃₄` from both sides
  using `mul_left_cancel₀`. The 3-step calc:
  1. Rewrite `E₁₂E₃₄` → `E₂₃E₁₄` using `hE.symm`, then ring to get LHS of ht_eq
  2. Apply `ht_eq` directly
  3. Ring to rearrange into `factor · (t · s₁₂ · s₃₄)` form

- **Phase cancellation key**: hE says `exp(i(θ₂+θ₃)/2) * exp(i(θ₁+θ₄)/2) = exp(i(θ₁+θ₂)/2) * exp(i(θ₃+θ₄)/2)` — follows immediately from `← Complex.exp_add; congr 1; push_cast; ring`

- **h2I_sq**: `(2 * Complex.I)^2 = -4` proved by `simp only [mul_pow, Complex.I_sq]; push_cast; ring`

- **norm_num handles (-4 : ℂ) ≠ 0** after rewriting with h2I_sq

## Session 2026-04-13 (Session 1) - Proved hcx; 0 sorries

**Mode**: FRESH (claimed from pool)
**Outcome**: completed

### What I Did
- Proved `hcx` (the sine ratio identity) in `t_eq_sine_ratio` private lemma
- Strategy: `mul_left_cancel₀` with common factor `(2I)²·E₁₂E₃₄`, 3-step calc using hE.symm + ht_eq + ring
- Updated meta.json: sorries 1→0, lineCount 466→487, status formalized→verified, badge partial→verified
- Updated candidate pool: status in-progress→completed
- Created knowledge.md

### Files Modified
- `proofs/Proofs/PtolemysTheoremOQ01Incomplete01.lean` (hcx sorry → proof, 466→487 lines)
- `src/data/proofs/ptolemys-theorem-oq-01-incomplete-01/meta.json` (sorries, lineCount, status, badge, assumptions)

### Final State
- 0 sorries, 0 axioms, 487 lines
- Fully verified: ptolemy_equality_implies_ccw_or_cw and ptolemy_equality_iff_ccw_or_cw
