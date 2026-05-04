# Knowledge Base: cayley-hamilton-oq-01-oq-03

**Problem**: Formalize matrix exponential via minpoly reduction: e^{tM} = ∑_{k=0}^{d-1} p_k(t) M^k

---

## Problem Understanding

The matrix exponential exp(t·M) for M : Matrix n n ℝ lies in the d-dimensional
algebra K[M] = span{I, M, ..., M^{d-1}} where d = deg(minpoly ℝ M). This means:

    exp(t·M) = ∑_{k=0}^{d-1} p_k(t) · M^k

with coefficient functions p_k(t) = ∑_{m≥0} (t^m/m!) · coeff_k(X^m mod μ_M).

---

## Session 2026-05-04 (Session 1) - Gallery entry formalized

**Mode**: FRESH  
**Outcome**: gallery entry created, 0 sorries, 1 axiom

### What I Did

1. Selected problem from available pool (highest tractability, rich surrounding infrastructure)
2. Built on CayleyHamiltonOQ01.lean infrastructure
3. Proved interchange via Matrix.ext + tsum_sum (entry-wise real-valued interchange)

### Key Findings

- `eval₂_eq_sum_range' hp`: eval₂ f x p = ∑ i ∈ range n, f(p.coeff i) * x^i
- Entry-wise approach avoids need for `Summable.smul_const` in matrix context
- `tsum_mul_right` works for real ℝ-valued sums to factor out fixed (M^k) i j
- The summability of coefficient series is the key axiom (linear recurrence bound argument)

### Files Created

- `proofs/Proofs/CayleyHamiltonOQ01OQ03.lean` (173 lines, 10 theorems, 1 axiom)
- `src/data/proofs/cayley-hamilton-oq-01-oq-03/meta.json`

### Next Steps (from this session)

- Remove expPolyCoeff_summable axiom by formalizing linear recurrence bound

---

## Session 2026-05-04 (Session 2) - Axiom eliminated via companion matrix proof

**Mode**: FRESH (worktree researcher-11)
**Outcome**: axiom converted to theorem — 0 sorries, 0 axioms (pending Docker build verification)

### What I Did

1. Claimed `cayley-hamilton-oq-01-oq-03` (score 17, RICH tier, 1 remaining axiom)
2. Analyzed the axiom `expPolyCoeff_summable` — the series ∑_m (t^m/m!) * c_{m,k} converges
3. Identified the clean proof route via `CayleyHamiltonReductionOQ02OQ01.companionMatrix`
4. Proved the KEY IDENTITY: `coeff_k(X^m mod μ) = (C^m)_{k,0}` where C = companion matrix of μ
   - Uses `minpoly_companionMatrix`: minpoly ℝ C = μ
   - Uses `aeval_eq_aeval_mod_minpoly C (X^m)`: C^m = aeval C (X^m mod μ)
   - Uses `eval₂_eq_sum_range'`: expand aeval as ∑_{j<d} c_{m,j} * C^j
   - Uses `companionMatrix_pow_basis`: (C^j)_{k,0} = δ_{k,j}
   - Collapses via `Finset.sum_eq_single`
5. Proved summability: |c_{m,k}| ≤ ‖C‖^m, so ∑_m |t^m/m!| * |c_{m,k}| ≤ ∑_m (|t|‖C‖)^m/m! < ∞
6. Used `summable_pow_div_factorial`, `norm_pow_le`, `norm_le_pi_norm` for the bound

### Key Findings

- **Companion matrix identity**: c_{m,k} = (C^m)_{k,0} via the orbit structure of e_0 under C
- **Proof route**: aeval + eval₂ + companionMatrix_pow_basis → no modular arithmetic needed!
- **Summability**: `Summable.of_norm_bounded` with geometric rate ‖C‖
- The proof is clean and elementary — no Aristotle needed
- `norm_le_pi_norm f i : ‖f i‖ ≤ ‖f‖` gives entry bound from matrix norm
- `norm_pow_le C m : ‖C^m‖ ≤ ‖C‖^m` gives geometric bound

### Files Modified

- `proofs/Proofs/CayleyHamiltonOQ01OQ03.lean` (265 lines, added 3 new private lemmas)
  - Added import `Proofs.CayleyHamiltonReductionOQ02OQ01`
  - Added `coeff_pow_X_eq_companion` (KEY IDENTITY, ~45 lines)
  - Added `expPolyCoeff_summable` as theorem (was axiom, ~25 lines)
  - Moved helper lemmas before Section 1

### Next Steps

- Docker build to verify compilation (pending)
- If successful: promote status to "verified", update meta.json, create PR
- Follow-up: Putzer's algorithm (p_k satisfy ODE system ṗ_k = λ_k p_k + p_{k-1})
