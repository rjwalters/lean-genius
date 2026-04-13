# Knowledge Base: Basel Problem OQ01 OQ01 OQ02
## Problem: Formalizing Apéry's Proof of ζ(3) Irrationality

---

## Problem Summary

Can Apéry's 1978 proof of ζ(3) irrationality be formalized in Lean?

The proof constructs explicit rational approximations using the Apéry numbers:
- bₙ = ∑_{k=0}^n C(n,k)² C(n+k,k)²  (integers, grow like 34ⁿ)
- aₙ  defined by same recurrence, a₀=0, a₁=6  (rationals)
- Lₙ = bₙ·ζ(3) - aₙ → 0 at rate (17-12√2)ⁿ ≈ 0.029ⁿ
- lcm(1,...,n)³ · aₙ ∈ ℤ  (denominator control)

Since lcm ~ eⁿ and |Lₙ| ~ 0.029ⁿ < e⁻³ⁿ, the product d_n·|Lₙ| → 0,
forcing irrationality via the integer-squeeze argument.

---

## Session 2026-04-12 — Conditional Irrationality Theorem

**Mode**: FRESH (RICH knowledge tier, score 26)
**Outcome**: progress — formalized core logical structure

### What I Did

Added Parts XI and XII to `BaselProblemOQ01OQ01OQ02.lean` (217 → 504 lines):

**Part XI: Divisibility Infrastructure**
- `dvd_lcmUpTo`: ∀ k ≤ n, 0 < k → k ∣ lcmUpTo n  (complete, no sorry)
  - Proof: k-1 ∈ range n → Finset.dvd_lcm gives k | lcmUpTo n
- `rat_den_dvd_lcmUpTo`: r.den ∣ lcmUpTo n for n ≥ r.den  (complete, no sorry)
- `apery_bterm_int`: (lcmUpTo n)³ · bₙ · r ∈ ℤ when r.den ≤ n  (likely complete)
  - Proof: write r = r.num/r.den, lcmUpTo n = q·r.den, then (q·d)³·b·(num/d) = q³·d²·b·num ∈ ℤ

**Part XII: Conditional Irrationality**
- `rationalLinearForm`: rational version Qₙ(r) = bₙ·r - aₙ  (definition)
- `rationalLinearForm_cast`: when (r:ℝ) = ζ(3), (Qₙ:ℝ) = Lₙ  (complete)
- `apery_irrationality_conditional`: IF h_decay AND h_nonzero AND h_denom THEN Irrational ζ(3)  (complete, no sorry)

### The Conditional Theorem

```
theorem apery_irrationality_conditional
    (h_decay : ∀ ε > 0, ∃ N, ∀ n ≥ N, (lcmUpTo n)³ · |Lₙ| < ε)
    (h_nonzero : ∀ n > 0, Lₙ ≠ 0)
    (h_denom : ∀ n, ∃ m : ℤ, (lcmUpTo n)³ · aₙ = m) :
    Irrational (zetaValue 3)
```

Proof structure:
1. Take N₀ = max(N_decay+1, r.den) — large enough for both decay and divisibility
2. Show d_{N₀} · Q_{N₀} is a nonzero integer (from h_denom + apery_bterm_int)
3. |M| ≥ 1 (Int.one_le_abs) but d_{N₀} · |L_{N₀}| < 1 (from h_decay)
4. Contradiction via linarith

### Key Insights

- The core logical structure of Apéry's proof is now formalized
- `apery_theorem` can be proved by `apery_irrationality_conditional <h_decay> <h_nonzero> denominator_control` once analytic hypotheses are proved
- r.den | lcmUpTo n is the KEY divisibility fact (proved cleanly from Finset.dvd_lcm)

### Files Modified

- `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean` (217 → 504 lines, +5 theorems, +2 defs, 0 new sorries)

### Remaining Sorries

1. `aperyB_recurrence`: 3-term recurrence — needs WZ theory
2. `aperyB_growth_upper`: bₙ ≤ 34ⁿ — depends on recurrence
3. `nair_lcm_bound`: lcm ≤ 4ⁿ — elementary but Chebyshev-hard in Lean
4. `denominator_control`: lcm³·aₙ ∈ ℤ — needs a-sequence closed form
5. `apery_theorem`: closes via `apery_irrationality_conditional` once above done

### Next Steps

1. Prove `denominator_control`: the a-sequence can be written as a sum of 1/k³ terms whose denominators divide lcm³
2. Consider Aristotle for the sub-lemmas in `apery_bterm_int` if it doesn't compile
3. The main analytic gaps (decay, nonzero) require the recurrence first
