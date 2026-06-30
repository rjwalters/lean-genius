# Research State: lovasz-local-lemma-oq-01

## Current State
**Phase**: ACT (new verified results landed; measure-theoretic core still open)
**Path**: full
**Since**: 2026-06-27
**Iteration**: 3

## This session (researcher-9, 2026-06-27)

Landed three new **verified, 0-axiom** theorems in
`Proofs/LovaszLocalLemma.lean` (Part XI), advancing roadmap items 2 and 3 from
the prior session. Verified via `lake env lean` against the main-repo Mathlib
`.olean` cache (Docker image build still broken — containerd meta.db I/O
error). `#print axioms` on all three: only `[propext, Classical.choice,
Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool`.

1. **`lllThreshold_succ_le (d) (hd : 1 ≤ d) : T(d+1) ≤ T(d)`** — threshold
   monotonicity. The symmetric LLL probability budget `T(d) = dᵈ/(d+1)^{d+1}`
   shrinks as dependency degree grows. *This is the flagship new result*; it
   subsumes the existing `lllThreshold_le_quarter` (iterate down to T(1)=1/4).
2. **`lllThreshold_antitone {c d} (1 ≤ c) (c ≤ d) : T(d) ≤ T(c)`** — chain form,
   by `Nat.le_induction` on the gap.
3. **`lllThreshold_mul_succ (d) (hd : 0 < d) : (d+1)·T(d) = (d/(d+1))ᵈ`** —
   bridge identity (roadmap item 2), immediate from `lllThreshold_eq_product`.

### Proof technique for monotonicity (reusable)
Cross-multiply `T(d+1) ≤ T(d)` (via `div_le_div_iff₀`) to the polynomial
target `(a+1)^{2d+2} ≤ aᵈ(a+2)^{d+2}` with `a = ↑d`. Factor both sides as
`((a+1)²)ᵈ·(a+1)²` and `(a(a+2))ᵈ·(a+2)²` (`pow_add`/`pow_mul`/`mul_pow`).
Apply the file's own `bernoulli_ineq` to `(1 - 1/(a+1)²)ᵈ ≥ 1 - d/(a+1)²`
(note `a(a+2) = (a+1)²-1`), clear the `d`-th power with `le_div_iff₀`, then
finish with the residual polynomial inequality `(a²+a+1)(a+2)² ≥ (a+1)⁴`
(difference `= a³+3a²+4a+3 ≥ 0`) via `nlinarith` plus a multiply-out by `(a+1)²`
(`le_of_mul_le_mul_right`).

## Still open (the genuine OQ-01 deliverable)

The measure-theoretic probability-space LLL remains unformalized: events as
measurable sets `Aᵢ : Set Ω` in a `ProbabilityMeasure`, real
dependency/independence (`ProbabilityTheory.iIndepSet`), and the conclusion
`μ (⋂ Aᵢᶜ) > 0`. Mathlib has the primitives but no LLL. This is the
multi-session research-grade target (Spencer/cluster-expansion or Moser–Tardos
entropy-compression over a real measure space).

## Next Action

Roadmap item 1: state the measure-theoretic symmetric LLL precisely as a
`Prop`/theorem statement (with `sorry`) in a *separate* file so the clean
`LovaszLocalLemma.lean` stays 0-sorry. Do NOT re-prove the rational surrogate.
The monotonicity/bridge increments are now done.
