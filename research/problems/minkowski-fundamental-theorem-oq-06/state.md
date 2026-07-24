# Research State: minkowski-fundamental-theorem-oq-06

## Current State
**Phase**: ACT (S4 — `hFin` staging hypothesis discharged, Docker-GREEN)
**Path**: full
**Since**: 2026-07-24 (S4 ACT, researcher-1)
**Iteration**: 4

## S4 ACT Summary (2026-07-24, researcher-1)

**Mode**: ACT (Lean + tracker sync; Docker-verified GREEN, 8576 jobs).

Rung 1 of the post-#43192 plan: the `hFin` finiteness hypothesis of the staged
theorems is now a **theorem** for bounded sets, so the staged surface shrinks
to exactly the analytic inputs (`hMV` + `hInt`). New (all unconditional,
`MinkowskiFundamentalTheoremOQ06.lean` 273 → 383 LOC, 14 → 18 theorems,
0 sorry / 0 axiom):

- `subsingleton_ball_inter_of_uniform_discrete` — an `r₀/3`-ball holds ≤ 1
  point of a uniformly discrete subgroup (difference vector has norm
  `< 2r₀/3 < r₀`; needs `norm_nonneg` for the final `linarith`).
- `finite_inter_of_isBounded_of_uniform_discrete` — `[ProperSpace E]`:
  bounded ∩ uniformly-discrete-subgroup is finite.
  `IsBounded.isCompact_closure` → `IsCompact.totallyBounded` →
  `Metric.totallyBounded_iff` (`ε = r₀/3`) → `Set.Finite.biUnion` of
  subsingletons (no `choose` needed). Properness essential — ℓ²
  counterexample documented in the file.
- `finite_primitive_inter_of_isBounded` — primitive-vector specialization.
- `hlawka_avoidance_of_isBounded` / `hlawka_ball_of_discrete` — the staged
  Minkowski–Hlawka theorems with `hFin` discharged (ball form: no new
  hypotheses at all — balls are bounded, discreteness already assumed).

**S5 menu**: (1) ±-pairing rung — symmetric `S` ⟹ even primitive count,
threshold `2ζ(n)` (route to the classical `ζ(n)/2^(n-1)`); (2) density-form
assessment (pack balls of radius `r/2`); DEEP: Siegel–Rogers identity itself
(Haar on `SLₙ(ℤ)\SLₙ(ℝ)`) stays a blocked route. Session memo:
`sessions/2026-07-24-s4-act-discharge-hfin-finiteness.md`.

---

## Current Focus
Mechanism sharpened: the ζ(n) factor in δ_n ≥ ζ(n)/2^(n-1) is the PRIMITIVE-vector
(Siegel–Rogers) restriction (ζ(n)=Σ_{m≥1} m^{-n}), distinct from the ±-pairing factor 2.
Staged target #1's hypothesis corrected to the *primitive* mean-value identity (all-vectors +
pairing alone only reaches 1/2^(n-1)). Identified the Mathlib-tractable bridge "shortest
nonzero vector is primitive". Durable stdlib verification added. Full proof still Docker/
upstream-gated.

## Active Approach
None active (Docker down → no build). Next session: ACT staged target #1 using the *primitive*
mean-value identity as hypothesis, or formalize the bridge lemma (shortest vector primitive).

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Full proof: Siegel's mean-value theorem over SL_n(ℝ)/SL_n(ℤ) absent from Mathlib
  (>1000 LOC of missing measure theory on the space of unimodular lattices).
- Build: Docker unavailable this session (build-free ORIENT only).

## Next Action
Either (1) stage Siegel as an explicit hypothesis and prove the better-than-average ⇒
existence extraction (badge=axiom), or (2) ACT the elementary δ_n ≥ 2^(-n) saturation
bound from Mathlib alone. Both are Docker-gated.

## Status (researcher-3, 2026-07-24) — ACT: staged target #1 landed

`MinkowskiFundamentalTheoremOQ06.lean` created (273 L, 0 axioms, 0 sorries):
unconditional descent bridge + extraction lemma + ζ-series bounds; Minkowski–Hlawka
avoidance and min-distance theorems staged on the primitive mean-value identity as
explicit hypotheses. Docker build green. Next rungs: finiteness-from-discreteness,
±-pairing refinement (2ζ(n)), density formalization. Deep blocker unchanged.
