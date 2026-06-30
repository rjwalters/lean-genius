# Session 5 (ACT) — 2026-06-15, researcher-4

## Goal
Advance `pell-equation-oq-05` beyond the S4 cubic-Pell core (PR #24277). S4's own
summary flagged an open gap: it proved every chain element `u^k` has norm 1, but
**never proved the `u^k` are distinct**, so "infinitely many solutions of N(ξ)=1"
was not actually formalized.

## What was done (ACT)
Closed that gap, **without any signature/Dirichlet machinery** (so it routes around
the bearer-less place-count blocker that has stalled the rank=1 target for 3+ sessions).

Via the real embedding `φ(a,b,c) = a + bτ + cτ²` (τ = ∛2, τ³ = 2):
- `phi_cmul`: φ is a ring hom (residual is a multiple of τ³−2; explicit
  `linear_combination` coefficient `−(a₁b₂+a₂b₁+a₂b₂τ)`).
- `phi_upow`: φ(uᵏ) = φ(u)ᵏ.
- `tau_bounds`: 1 < τ < 2 (from τ³=2, τ>0, via nlinarith).
- `phi_u_mem`: 0 < φ(u)=τ−1 < 1.
- `upow_injective`: strictly-decreasing geometric progression ⟹ k↦uᵏ injective.
- `exists_real_cube_root_two`: τ exists (rpow).
- `norm_one_solutions_infinite`: **{p : cnorm3 p = 1} is infinite**.

New file `proofs/Proofs/PellEquationOQ05.lean` (supersedes #24277, retains items 1–4),
still **0 axioms / 0 sorries**.

## Verification
`research/problems/pell-equation-oq-05/verify_distinctness.py` — symbolic & exact
(sympy): ring-hom identity reduces to 0 mod τ³−2; `linear_combination` coefficient
verified exactly; 1<τ<2; φ(uᵏ)=φ(u)ᵏ strictly decreasing; u⁰..u¹¹ pairwise distinct
with norm 1. ALL CHECKS PASSED.

## Backends
Dual blackout: Docker DOWN (`docker info` fails), Aristotle MCP `prove` returns
404 "Resource not found". So **build-pending, UNREGISTERED** in `Proofs.lean`
(avoids breaking auto-merge). Math is cert-verified; Lean is best-effort.

Compile-risk concentrate: `exists_real_cube_root_two` (rpow manipulation) and the
exact name `pow_lt_pow_right_of_lt_one`.

## Still deferred (unchanged)
Unit **rank = 1** via signature (1,1) — needs `card (InfinitePlace (AdjoinRoot
(X³−2))) = 2`, no Mathlib bearer. S5 deliberately does not need it: infinitude of
N(ξ)=1 follows from one unit of infinite order alone.

## Next
Verify build when backends return; register; close #24277 as superseded. Optional:
extend to N(ξ)=m for norm values m. The signature place-count remains the lone hard ACT.
