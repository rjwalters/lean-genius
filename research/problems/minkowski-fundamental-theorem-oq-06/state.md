# Research State: minkowski-fundamental-theorem-oq-06

## Current State
**Phase**: ACT (S7 — packing rung landed: `packingDensity` via `ZLattice.covolume`, disjoint balls, staged `hlawka_packing_symm`)
**Path**: full
**Since**: 2026-09-29 (S7 ACT, researcher-2)
**Iteration**: 6

## S7 ACT Summary (2026-09-29, researcher-2)

**Mode**: ACT (Docker-GREEN 8576 jobs; base = the S6.5 v4.31 repair branch, PR
#43780 superseded by this session's PR). File 619 → 732 LOC, 21 → 26 theorems
+ 1 def, 0 sorry / 0 axiom.

The classical packing formulation: `pairwiseDisjoint_balls_of_minDist`
(unconditional — min-dist ≥ r ⟹ radius-r/2 balls at subgroup points pairwise
disjoint, via `Metric.ball_disjoint_ball`), `packingDensity :=
vol(ball(r/2))/ZLattice.covolume L` with covolume-one/scaling/positivity
lemmas, and the staged headline `hlawka_packing_symm`: every
`0 < d < ζ(n)/2^(n-1)` is realized by a covolume-one lattice whose disjoint
balls achieve `packingDensity = d` — δₙ ≥ ζ(n)/2^(n-1) in standard form,
still on exactly `hMV`/`hInt`.

Lean bits: headline over `Submodule ℤ E` applying the AddSubgroup surface to
`.toAddSubgroup`; memberships transport by defeq (`Submodule.mem_toAddSubgroup`
does NOT name-resolve in pinned v4.31 — module-system exposure — but
`toAddSubgroup` is `@[reducible]`); `hcov : covolume = 1` avoids instance
families over Ω; only `packingDensity_pos` needs `[DiscreteTopology]
[IsZLattice ℝ L]`.

**S8 menu**: staging surface saturated through the packing form. DEEP blocker
only (Siegel–Rogers / Haar on SLₙ(ℤ)\SLₙ(ℝ) — registry, stand down).
Conceivable side rung: instantiate ℤⁿ via `ZSpan` as a concrete covolume-one
inhabitant of the staging surface — value-assess first.

## S5 ACT Summary (2026-07-24, researcher-3)

**Mode**: ACT (Lean; host-verified `lean` v4.31.0 full-file elaboration against
the pinned Mathlib oleans, 0 errors; `#print axioms` foundational only).

Rung 2 of the post-#43192 plan: the **±-pairing rung**. File 383 → 498 LOC,
18 → 21 theorems (+ `IsPrimitive.neg`, `neg_ne_self_of_ne_zero`,
`two_le_primCount_of_symm_of_mem`, `hlawka_avoidance_symm`,
`hlawka_ball_symm`), 0 sorry / 0 axiom.

Key simplification vs the menu: NO parity/evenness lemma and NO refined
mean-value identity needed. On a symmetric `S`, ONE primitive vector `v ∈ S`
forces TWO (`v`, `-v` distinct — no 2-torsion in a real vector space, and
negation preserves primitivity), so `primCount ≥ 2` pointwise wherever
avoidance fails; mean `= vol/ζ < 2` then contradicts. Same `hMV` hypothesis
as before, threshold doubled: `vol(S) < 2·ζ(n)` (avoidance),
`vol(ball r) < 2·ζ(n)` (min-distance). This is the classical route to
`δₙ ≥ ζ(n)/2^(n-1)`; the residual `2^(1-n)` is ball-volume scaling.

Lean bits: `Set.ncard_pair` + `Set.ncard_le_ncard` for the two-element lower
bound; `integral_mono (integrable_const 2)` + plain `simpa` (per the S1 memo
gotcha, `integral_const` needs plain simp) + `le_div_iff₀`; `smul_neg` closes
`IsPrimitive.neg`; `push Not` (push_neg deprecated at v4.31).

**S6 menu**: (1) density-form assessment (pack balls of radius `r/2`,
`vol(ball r) = r^n · vol(ball 1)` scaling — assess Mathlib bearer
`EuclideanSpace` ball-volume API first); (2) DEEP: Siegel–Rogers identity
(Haar on `SLₙ(ℤ)\SLₙ(ℝ)`) — registry blocker, stand down.

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
