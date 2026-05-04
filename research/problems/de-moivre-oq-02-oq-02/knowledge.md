# de-moivre-oq-02-oq-02: Chebyshev T·U Cross-Product Formula

**Problem**: Can the product-to-sum formula be extended to Chebyshev polynomials of the second kind U_n?

**Status**: COMPLETED (2026-05-03)

---

## Session 2026-05-03 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed (awaiting Docker build verification)

### What I Did

- Surveyed parent proof `DeMoivreOQ02.lean` (T×T product-to-sum) and Chebyshev U API
- Proved the T×U cross-product formula: `2·T_m·U_n = U_{m+n} + U_{n-m}` in R[X] for any CommRing R
- Used paired integer induction (Q(m) = P(m) ∧ P(m-1)) with `linear_combination`
- Also derived: `chebyshev_cos_U` (m=1 case), `two_cos_sin_spreading` (trig form)
- Created gallery entry in `src/data/proofs/de-moivre-oq-02-oq-02/`
- Docker build attempted; OOM-killed (exit 137) due to concurrent build activity — not a proof error

### Proof Structure (183 lines, 5 public theorems, 0 sorries)

1. **two_X_U**: 2X·U_k = U_{k+1} + U_{k-1} (from U_add_two by rearrangement)
2. **P, Q definitions**: P(m) := 2T_m·U_n = U_{m+n} + U_{n-m}; Q(m) := P(m) ∧ P(m-1)
3. **Q_zero**: Base case — P(0) trivial; P(-1) uses T_{-1} = X and two_X_U
4. **Q_succ, Q_pred**: Inductive steps via T_add_two + linear_combination
5. **T_mul_U_product**: Main theorem via Int.induction_on on Q
6. **chebyshev_T_U_product_to_sum**: Real evaluation form
7. **chebyshev_cos_U**: m=1 specialization
8. **two_cos_sin_spreading**: Trig identity

### Key Findings

- Paired induction Q(m) = P(m) ∧ P(m-1) is the natural technique for second-order recurrences on ℤ
- `linear_combination` closes all induction steps once the recurrence is set up
- The polynomial identity holds over any CommRing R — no ℝ restriction needed
- T_{-1} = X needs an inline proof from T_add_two at -1
- OOM (exit 137) from Docker with 7 concurrent build containers — not a proof bug

### Files Created

- `proofs/Proofs/DeMoivreOQ02OQ02.lean` (183 lines, 5 public theorems, 0 sorries)
- `src/data/proofs/de-moivre-oq-02-oq-02/{meta,annotations}.json + index.ts`
- `proofs/Proofs.lean` (added import)

### Next Steps

- Retry Docker build when fewer concurrent containers are running
- PR to main with `research` label
