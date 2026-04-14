# Knowledge: erdos-476 — Erdős-Heilbronn Conjecture

## Problem Summary

**COMPLETED** (2026-04-13): The Erdős-Heilbronn conjecture |A +̂ A| ≥ min(2|A| - 3, p) for A ⊆ 𝔽ₚ. The main bound is axiomatized (da Silva-Hamidoune 1994). All 4 supporting sorries proved.

---

## Session 2026-04-13 (Session 1) — Prove all 4 sorries

**Mode**: FRESH
**Outcome**: COMPLETED — 0 sorries (was 4), 2 axioms

### What I Did
- `restrictedSumsetR`: replaced `sorry` with `(A.powersetCard r).image (fun s => s.sum id)` — sums of r-element subsets.
- `card_two_case`: proved via `Finset.card_eq_two`, showed restricted sumset equals `{a+b}` by case analysis on all 4 pairs, closed by `Finset.card_singleton`.
- `erdos_476_summary` sorries: proved AP cardinality via injectivity of `i ↦ a + ↑i • d` using `mul_right_cancel₀` in the field ZMod p, `ZMod.val_cast_of_lt` to extract naturals from field equality. AP bound followed from `AP_restrictedSumset` axiom.

### Key Techniques
- `Finset.card_eq_two.mp h` extracts `a, b, hab : a ≠ b, rfl` from `A.card = 2`
- `ZMod.val_cast_of_lt (hi : i < p) : ZMod.val (↑i : ZMod p) = i` — value extraction
- `mul_right_cancel₀ hd heq : (↑i : ZMod p) = ↑j` from `nsmul_eq_mul` + field cancellation
- `Finset.card_image_of_injOn` for AP cardinality
- `A.card ≤ p` derived from `hsmall : 2 * A.card - 3 < p` and `h : 2 ≤ A.card` via omega

### Files Modified
- `proofs/Proofs/Erdos476Problem.lean`: 4 sorries → 0
- `src/data/proofs/erdos-476/meta.json`: sorries 4→0, lineCount 291→320
