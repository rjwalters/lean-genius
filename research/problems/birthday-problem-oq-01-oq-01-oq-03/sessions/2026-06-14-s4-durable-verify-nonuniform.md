# S4 — Durable (Docker-free) verification of the non-uniform collision result

**Date**: 2026-06-14
**Agent**: researcher-3
**Mode**: DURABLE-VERIFY (build-free; new files only — path-disjoint from the
in-flight ACT-1 draft PR #23219, which edits `Proofs.lean`,
`BirthdayProblemOQ01OQ01OQ03.lean`, `state.md`, and the research JSON)

## Context

ACT-1 (PR #23219) wrote the Lean file with T1–T4 but is **blocked on the
2026-06-13/14 Docker outage**, so it is not machine-checked. The only remaining
math gap is **T3's converse** (the Cauchy–Schwarz equality case
`Σp² = 1/d ⟹ uniform`), explicitly deferred as "optional, fiddly." No durable
verification artifact existed for this slug. Docker is still down this session.

## What this session adds

`research/problems/birthday-problem-oq-01-oq-01-oq-03/verify_nonuniform.py` — a
deterministic, Docker-free check of every fact in the ACT plan:

- **(T0) identity** `E[X] = C(n,2)·Σp_k²` — proved **exactly** by full
  enumeration of the dⁿ outcomes (Fraction arithmetic) for 5 non-uniform cases
  (n≤5, d≤4). This is the model-level identity the parent rigor demands.
- **(T1) uniform recovery** `Σ(1/d)² = 1/d ⟹ E[X] = C(n,2)/d` (exact, d=1..39).
- **(T2) CS lower bound** `Σp_k² ≥ 1/d` over 5600 random distributions (d=2..29),
  uniform attaining equality — confirms uniform *minimises* collisions, so any
  non-uniformity (e.g. a biased hash) strictly *increases* expected collisions.
- **(T3) equality case** `Σp_k² = 1/d ⟺ uniform` — symbolically (sympy) for
  d=2..5 the unique simplex minimiser of Σp² is uniform.

## Key insight for a future T3 Lean port

The cleanest constructive route to the deferred T3 converse avoids the generic
CS-equality machinery entirely, via the **variance identity**

```
Σ_k p_k² − 1/d = Σ_k (p_k − 1/d)²        (valid whenever Σ p_k = 1)
```

(verified numerically to 2e-16). The cross term `−2/d·Σ(p_k−1/d)` vanishes
because `Σ p_k = 1`. Then `Σp² = 1/d ⟺ Σ(p_k−1/d)² = 0 ⟺ ∀k, p_k = 1/d`
(a sum of squares is zero iff every term is). In Lean this is a `Finset.sum`
expansion + `Finset.sum_eq_zero_iff_of_nonneg` + `sq_eq_zero_iff` — a short,
robust path that sidesteps porting the abstract `inner_mul_le_norm_mul_norm`
equality characterisation. Recommended for whoever discharges T3 after Docker
recovers.

## Why build-free / new-files-only

Grounds the in-flight T1–T4 (build-pending) and the deferred T3 without
recompiling Lean and **without editing any file PR #23219 touches**, so the two
PRs are mergeable in either order.

## Not attempted

No edit to the Lean file / `state.md` / research JSON (contended by #23219).
T3's Lean proof itself is left to a post-Docker ACT (route documented above).
