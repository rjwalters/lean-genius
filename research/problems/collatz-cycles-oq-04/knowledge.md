# Knowledge Base: collatz-cycles-oq-04

**Problem**: Formalize the algebraic cycle product equation for Collatz cycles.

**Status**: ACT — Lean proof file created with main theorem proved.

---

## Session 2026-04-13 (Session 1) — Cycle Product Equation

**Mode**: FRESH  
**Outcome**: progress — main theorem proved, 2 sorrys remain

### What I Did

1. Surveyed parent proof `CollatzCycles.lean` — 256 lines, 0 sorries, verified.
2. Identified OQ-04 as: formalize `2^M = 3^j · (cycle structure terms)`, i.e., the cycle product equation `∏(3nᵢ+1) = 2^M · ∏nᵢ`.
3. Created `CollatzCyclesOQ04.lean` with:
   - `cyclicSucc` / `cyclicPred`: cyclic bijection infrastructure on `Fin j`
   - **`collatz_cycle_product_eq`**: PROVED — the main cycle product equation
   - **`collatz_one_odd_step`**: PROVED — n=1, m=2 is the unique 1-odd-step solution
   - `collatz_cycle_halving_constraint`: sorry (proof outlined via product equation)
   - `cycleForcingSum` + `collatz_cycle_additive_eq`: sorry (for Eliahou bounds)
4. Added to `proofs/Proofs.lean` and created gallery data.

### Key Findings

- The cycle product equation follows by: (1) replacing factors with step equations, (2) `prod_mul_distrib`, (3) `prod_pow_eq_pow_sum` for the exponential part, (4) `prod_nbij` with the cyclic bijection for index reordering.
- `Finset.prod_nbij` is the correct Mathlib4 API for bijective reindexing (confirmed by WilsonsTheoremOQ02.lean usage pattern).
- `Finset.prod_pow_eq_pow_sum` works directly (confirmed by AbelRuffiniOQ04OQ01.lean).
- The halving constraint 2^M > 3^j has a cleaner proof via the product equation than the case-by-case enumeration in CollatzCycles.lean.

### Files Modified

- `proofs/Proofs/CollatzCyclesOQ04.lean` — new proof file (172 lines, 2 sorries)
- `proofs/Proofs.lean` — added import
- `src/data/proofs/collatz-cycles-oq-04/meta.json` — gallery metadata
- `src/data/proofs/collatz-cycles-oq-04/annotations.json` — section annotations
- `research/registry.json` — phase OBSERVE → ACT

### Next Steps

1. Complete `collatz_cycle_halving_constraint`:
   - Prove `∏(3ns+1) > 3^j·∏ns` using `Finset.prod_lt_prod` (or induction on j)
   - Cancel `∏ns > 0` using `Nat.lt_of_mul_lt_mul_right`
2. Complete `collatz_cycle_additive_eq`:
   - Prove by induction on j, unrolling step equations
3. Use the additive equation to formalize Eliahou's lower bound (new problem)

---

## Problem Understanding

OQ-04 from `collatz-cycles` asks to formalize the connection between Collatz cycles
and the algebraic equation `2^M = 3^j · (product of cycle structure terms)`.

The cleanest formulation: for a cycle with j odd elements n₁,...,nⱼ and mᵢ halvings:
  ∏ᵢ (3nᵢ + 1) = 2^M · ∏ᵢ nᵢ   where M = Σmᵢ

---

## Insights

- The bijection i ↦ (i+1) mod j on Fin j is the key algebraic fact enabling the proof
- `prod_nbij` in Mathlib4 takes (function, membership, injectivity, surjectivity, value-agreement)
- The injectivity of cyclicSucc follows easily from omega on the modular arithmetic
- `Nat.eq_one_of_mul_eq_one_left/right` are useful for characterizing factorizations of 1

---

## Dead Ends

- Using `Finset.prod_bij'` (mutual-inverse API) — works in theory but harder to use than `prod_nbij`
- Using `Fintype.prod_equiv` — possible but requires more setup than `prod_nbij`
