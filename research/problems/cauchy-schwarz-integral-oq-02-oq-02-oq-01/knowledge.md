# Knowledge Base: cauchy-schwarz-integral-oq-02-oq-02-oq-01

**Problem**: ENNReal rpow division step for Hölder → Minkowski
**Phase**: COMPLETED

---

## Problem Understanding

The parent `CauchySchwarzIntegralOQ02OQ02.lean` proves the Young → Hölder → Minkowski chain
but uses `ENNReal.lintegral_Lp_add_le` as a black box for the final step:

  From: ∫(f+g)^p ≤ (‖f‖_p + ‖g‖_p)·(∫(f+g)^p)^{(p-1)/p}
  Get:  (∫(f+g)^p)^{1/p} ≤ ‖f‖_p + ‖g‖_p

OQ-01 asks: can this "rpow division" step be proved explicitly?

---

## Session 2026-04-02 (Session 1) - Full Proof

**Mode**: FRESH
**Outcome**: COMPLETE — 0 sorries, 0 axioms

### What I Did

Created `CauchySchwarzIntegralOQ02OQ02OQ01.lean` with:

1. **`ennreal_rpow_cancel`**: If X ≤ C·X^q with 0 ≤ q < 1 and X ≠ ⊤, then X^{1-q} ≤ C.
   - Case X = 0: `ENNReal.zero_rpow_of_pos (1-q > 0)` gives 0 ≤ C.
   - Case 0 < X < ⊤: factor X = X^{1-q}·X^q via `ENNReal.rpow_add (1-q) q hX0 hXfin`,
     then cancel X^q using `ENNReal.mul_le_mul_iff_left`.
   - X^q ≠ ⊤ follows from `simp [ENNReal.rpow_eq_top_iff, hX0, hXfin]`.
   - X^q > 0 from `ENNReal.rpow_pos hXpos hXfin`.

2. **`minkowski_cancellation_step`**: Applies with q = (p-1)/p using identity 1-(p-1)/p = 1/p.

### Key Findings

**Mathlib 4.26.0 lemma names** (required discovering via exact? and build testing):
- `ENNReal.zero_rpow_of_pos (hr : 0 < r) : (0 : ℝ≥0∞) ^ r = 0`
- `ENNReal.rpow_pos (hx : 0 < x) (hxt : x ≠ ⊤) : 0 < x ^ y` (both conditions needed)
- `ENNReal.rpow_add (p q : ℝ) (hx : x ≠ 0) (hx' : x ≠ ⊤)` — exponents are EXPLICIT first args
- `ENNReal.rpow_eq_top_iff : x^y = ⊤ ↔ (x=⊤ ∧ 0<y) ∨ (x=0 ∧ y<0)` — for finiteness
- `ENNReal.mul_le_mul_iff_left (h0 : a ≠ 0) (htop : a ≠ ⊤) : a*b ≤ a*c ↔ b ≤ c`
  (was `mul_le_mul_right`, then `mul_le_mul_iff_right`, now `mul_le_mul_iff_left`)

**API instability**: The Mathlib ENNReal multiplication lemma names changed several times;
used `exact?` in test files to discover the current correct names.

### Files Modified

- Created: `proofs/Proofs/CauchySchwarzIntegralOQ02OQ02OQ01.lean` (117 lines, 0 sorries)

---

## Insights

- The rpow division step is the core mathematical content: X = X^{1-q}·X^q, so cancel X^q.
- The proof naturally splits into X=0 (trivial) and 0<X<⊤ (algebraic) cases.
- `ENNReal.rpow_add` takes explicit exponent args in Mathlib 4.26.0 (signature changed).
- Finiteness of X^q (for 0<X<⊤) follows from `rpow_eq_top_iff` by eliminating both disjuncts.
- `ENNReal.rpow_pos` requires BOTH `0 < x` AND `x ≠ ⊤` to give `0 < x^y`.

## Dead Ends

- `ENNReal.rpow_pos_of_pos` — doesn't exist in 4.26.0 (replaced by `ENNReal.rpow_pos`)
- `ENNReal.rpow_lt_top_of_ne_top` — doesn't exist; use `rpow_eq_top_iff` approach
- `ENNReal.mul_le_mul_iff_right` — existed momentarily but renamed to `mul_le_mul_iff_left`
