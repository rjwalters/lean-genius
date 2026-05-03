# de-moivre-oq-02-oq-02: Chebyshev U Polynomial Product-to-Sum Formula

**Problem**: Can the product-to-sum formula be extended to Chebyshev polynomials of the second kind U_n?

**Status**: COMPLETED (2026-05-03)

---

## Session 2026-05-03 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Surveyed parent proof `DeMoivreOQ02.lean` (T_n product-to-sum via trig) and `DeMoivreOQ01.lean` (U_real_cos identity)
- Identified algebraic approach (not trigonometric) as the right strategy: U_m·U_n and the sum S(m,n) both satisfy the same Chebyshev recurrence in m
- Wrote complete proof in `proofs/Proofs/DeMoivreOQ02OQ02.lean` (165 lines, 0 sorries)
- Created gallery entry in `src/data/proofs/de-moivre-oq-02-oq-02/` with meta.json, annotations.json, index.ts
- Added `import Proofs.DeMoivreOQ02OQ02` to `proofs/Proofs.lean`
- Docker build submitted; pending completion

### Proof Structure

1. **U_two_X_mul**: 2X·U_n = U_{n+1} + U_{n-1} (from U_add_two by substituting n-1)
2. **term_expand**: 2X·U(A-2k) = U(A+1-2k) + U(A-1-2k) per summand
3. **S definition**: S(m,n) = ∑_{k=0}^m U_{m+n-2k}
4. **S_zero, S_one**: base cases matching U_0·U_n = U_n and U_1·U_n = 2X·U_n = S(1,n)
5. **S_recurrence**: S(m+2,n) = 2X·S(m+1,n) - S(m,n) via sum telescoping
6. **U_eq_S**: strong induction on m (Nat.strong_rec_on)
7. **U_product_le, U_product_formula**: public API
8. **U1_sq, U2_U1, U2_sq**: verified small cases

### Key Findings

- The algebraic approach (recurrence uniqueness) is cleaner than trigonometric for U_n: `U_real_cos` gives `sin((n+1)θ)/sin(θ)` which doesn't simplify products cleanly
- `linarith` works on `ℝ[X]` for rearranging linear equations (the module has a linear order structure)
- `sum_range_succ` + `sum_add_distrib` + `ring_nf; congr 1; push_cast; ring` is the standard pattern for polynomial sum manipulations in Mathlib
- `Nat.strong_rec_on` with `| ind m ih =>` and `match m with` gives clean two-step induction

### Files Created

- `proofs/Proofs/DeMoivreOQ02OQ02.lean` (165 lines, 8 theorems, 0 sorries)
- `src/data/proofs/de-moivre-oq-02-oq-02/meta.json`
- `src/data/proofs/de-moivre-oq-02-oq-02/annotations.json`
- `src/data/proofs/de-moivre-oq-02-oq-02/index.ts`
- `proofs/Proofs.lean` (added import)

### Next Steps

- Verify Docker build passes (no sorry or type errors)
- PR to main with `research` label
