# Knowledge Base: cramers-rule-oq-02-oq-02
# LU Decomposition and QR Factorization vs Cramer's Rule

## Problem Summary

Extends the Cramer's Rule vs Gaussian elimination complexity comparison
(CramersRuleOQ02.lean) to LU decomposition and QR factorization.

**Models**:
- luMuls n = n³ (same as gaussMuls — LU ≡ Gaussian)
- qrMuls n = 2n³ (QR Householder ≈ 4n³/3, conservatively bounded by 2n³)

**Key threshold finding**: QR does NOT always beat Cramer for small n:
- n=1: QR=2, Cramer=2 (TIE)
- n=2: QR=16, Cramer=12 (QR worse!)
- n≥3: QR beats Cramer ✓

---

## Session 2026-05-06 (Session 1) — researcher-3

**Mode**: FRESH
**Outcome**: proof complete, PR pending

### What I Did
- Claimed problem cramers-rule-oq-02-oq-02
- Wrote CramersRuleOQ02OQ02.lean with 12 theorems (0 sorries, 0 axioms)
- Discovered QR beats Cramer only for n ≥ 3 (not n ≥ 1 as initially assumed)
- Key lemma: 2n³ < n²·n! for n ≥ 4 via chain 2n³ < n^4 = n²·n² < n²·n!
- Docker build running / pending confirmation

### Key Findings
- `Nat.pos_pow_of_pos` does not exist in Mathlib v4.26.0 — use `positivity` instead
- `Nat.mul_le_mul_right _ h` is the correct form for multiplication monotonicity
- QR 2n³ model is actually WORSE than Cramer at n=1,2; threshold is n≥3
- The asymptotic result (any K, eventually K-times better) works with threshold max(4, 2K)
- Importing `Proofs.CramersRuleOQ02` works and reuses `gauss_beats_cramer` etc.

### Files Modified
- `proofs/Proofs/CramersRuleOQ02OQ02.lean` (NEW, 169 lines)
- `src/data/proofs/cramers-rule-oq-02-oq-02/meta.json` (NEW)
- `src/data/proofs/cramers-rule-oq-02-oq-02/index.ts` (NEW)
- `src/data/proofs/cramers-rule-oq-02-oq-02/annotations.json` (NEW, empty)
- `src/data/proofs/cramers-rule-oq-02-oq-02/tacticStates.json` (NEW, empty)
- `src/data/proofs/listings.json` (updated, added new entry)

### Final Status
- PR #16280 created: https://github.com/rjwalters/lean-genius/pull/16280
- Docker build running (3rd attempt, dependencies downloading)
- Pool status: `completed`, lock released
- Additional Lean API note: `Nat.mul_le_mul_right _ h` requires `h : K * 2 ≤ n` (not `2 * K ≤ n`)
  due to multiplication order — use `have hK2n : K * 2 ≤ n := by linarith` to bridge
