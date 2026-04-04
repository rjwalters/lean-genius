# Knowledge: erdos-448-incomplete-01

**Problem**: Prove τ⁺(n) ≤ τ(n) rigorously from definitions (previously axiomatized in Erdos448Problem.lean)

## Summary

**Status: COMPLETED** — Proved `tauPlus_le_tau` rigorously in `Erdos448IncompleteOQ01.lean`.

## Session 2026-04-04 (Session 1) — COMPLETED

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Designed proof strategy: occupied intervals ⊆ image of divisors under Nat.log 2
2. Proved `log_eq_of_inDyadicInterval`: if 2^k ≤ d < 2^(k+1) and d > 0, then Nat.log 2 d = k
3. Proved `occupied_subset_image_log`: occupied intervals ⊆ image(log₂, divisors)
4. Main theorem: Finset.card_le_card + Finset.card_image_le gives τ⁺(n) ≤ τ(n)
5. Fixed pre-existing bugs in `Erdos448Problem.lean` (broken import, API changes)

### Key Findings

- **Core lemma**: `log_eq_of_inDyadicInterval` via contradiction using `Nat.pow_log_le_self` and `Nat.lt_pow_succ_log_self`
- **Proof structure**: occupied intervals ⊆ image(log₂) → cardinality bound → τ⁺(n) ≤ τ(n)
- **noncomputable tauPlus**: `native_decide` fails; use `decide` for ground-term proofs
- **File revert issue**: `Erdos448Problem.lean` was being reverted by a process between builds; must commit immediately after editing

### Bugs Fixed in Erdos448Problem.lean

- `Mathlib.Analysis.Asymptotics.Asymptotics` → `Mathlib.Analysis.SpecialFunctions.Log.Basic` (module renamed in Mathlib v4.26)
- `And.decidable` → `by unfold inDyadicInterval; infer_instance`
- `tau_prime`: `Nat.Prime.divisors` doesn't exist; rewrote with manual ext proof
- `tau_power_of_two`: `Finset.card_image_of_injective` approach broken; used `simp [Nat.divisors_prime_pow]`
- Isolated `/--` docstrings (not attached to declarations) → `/-` block comments

### Files Modified

- `proofs/Proofs/Erdos448IncompleteOQ01.lean` (created, 127 lines)
- `proofs/Proofs/Erdos448Problem.lean` (fixed 5 pre-existing bugs)
- `proofs/Proofs.lean` (added import)

### Follow-up Questions

**OQ-02**: Can τ⁺(n) = O(τ(n)^(1-ε)) for some ε > 0 for almost all n? (Erdős-Tenenbaum result: the ratio τ⁺(n)/τ(n) has a distribution function, so the bound is not that strong)
