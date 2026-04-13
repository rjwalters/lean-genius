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
- `rat_den_dvd_lcmUpTo`: r.den ∣ lcmUpTo n for n ≥ r.den  (complete, no sorry)
- `apery_bterm_int`: (lcmUpTo n)³ · bₙ · r ∈ ℤ when r.den ≤ n  (complete)

**Part XII: Conditional Irrationality**
- `rationalLinearForm`: rational version Qₙ(r) = bₙ·r - aₙ  (definition)
- `rationalLinearForm_cast`: when (r:ℝ) = ζ(3), (Qₙ:ℝ) = Lₙ  (complete)
- `apery_irrationality_conditional`: IF h_decay AND h_nonzero AND h_denom THEN Irrational ζ(3)  (complete, no sorry)

---

## Session 2026-04-13 — Growth Bound from Recurrence

**Mode**: REVISIT (RICH knowledge tier, score 28)
**Outcome**: progress — proved growth bound, documented PNT requirement

### What I Did

Added the growth bound proof to Part IV (513 → 580 lines):

**Growth Bound Infrastructure**
- `aperyB_le_34_mul_pred`: b_{n+1} ≤ 34·bₙ  (proved from recurrence)
  - From recurrence: (n+1)³·b_{n+1} = coeff·bₙ - n³·b_{n-1} ≤ coeff·bₙ
  - From coefficient bound: coeff ≤ 34·(n+1)³
  - Cancel (n+1)³ > 0: b_{n+1} ≤ 34·bₙ
- `aperyB_growth_upper_aux`: ∀ n, bₙ₊₁ ≤ 34^{n+1}  (by induction from b₁=5≤34)
- `aperyB_growth_upper`: ∀ n > 0, bₙ ≤ 34ⁿ  (via cases + aux)

**Sorry count reduced from 5 to 4** (growth_upper no longer has its own sorry).
Note: depends transitively on aperyB_recurrence sorry.

### Critical Discovery: PNT Requirement

Nair's bound lcm(1,...,n) ≤ 4^n is **INSUFFICIENT** for the unconditional 
irrationality theorem:
- lcm³ · |Lₙ| ≈ 64ⁿ · 0.029ⁿ ≈ 1.88ⁿ → ∞  (not 0!)
- Need: lcm ≤ cⁿ with c < (√2+1)^{4/3} ≈ 4.85
- PNT gives c ≈ 2.718 < 4.85  ✓
- Rosser-Schoenfeld gives c ≈ 2.83 < 4.85  ✓

This means the formalization needs either PNT or Rosser-Schoenfeld, not just Nair.
The conditional theorem abstracts this away.

### Remaining Sorries (4)

1. `aperyB_recurrence` (l.130): 3-term recurrence — WZ theory
2. `apery_theorem` (l.242): Main theorem — needs all hypotheses
3. `nair_lcm_bound` (l.354): lcm ≤ 4^n — too weak for irrationality!
4. `denominator_control` (l.381): lcm³·aₙ ∈ ℤ

### Next Steps

1. Prove aperyB_recurrence (WZ or direct) — unblocks growth bound
2. Find stronger prime bound in Mathlib (PNT or Rosser-Schoenfeld)
3. Prove denominator_control from a-sequence closed form
4. Submit Aristotle companion for routine sub-lemmas
