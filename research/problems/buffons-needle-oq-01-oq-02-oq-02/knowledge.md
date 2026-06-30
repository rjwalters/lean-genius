# Knowledge Base: buffons-needle-oq-01-oq-02-oq-02

Asymptotic decay of the higher-dimensional Buffon hyperplane constant.

---

## Problem Understanding

Goal: prove `√n · c_n → √(2/π)` (equivalently `c_n ~ √(2/(π n))`) for the
dimension-`n` Buffon crossing constant `c_n`.

### CORRECTED closed form (key finding)

The seeder's `problem.md` quoted the constant as `Γ(n/2)/(√π Γ((n+1)/2))`. That
is **wrong** for this gallery's parent. The genuine parent
(`proofs/Proofs/BuffonsNeedleOQ01OQ02.lean:56`) defines

```
  buffonConstant n = 2 · Γ(n/2) / ((n-1) · √π · Γ((n-1)/2)),   n ≥ 2
```

i.e. `c_n = E[|⟨u, e₁⟩|]`, the expected absolute coordinate of a uniform unit
vector `u ∈ S^{n-1}`. Spot checks from the parent: `c₂ = 2/π`, `c₃ = 1/2`,
`c₄ = 4/(3π)`. The target asymptotic `√(2/π) ≈ 0.7979` is consistent
(`√2·c₂ ≈ 0.900`, `√3·c₃ ≈ 0.866`, `2·c₄ ≈ 0.849`, decreasing toward it).

---

## Insights

### Elementary, Stirling-free proof (recurrence + monotonicity squeeze)

Set `s n = Γ(n/2)/Γ((n-1)/2)`, so `c_n = 2·s n / ((n-1)·√π)`.

1. **Product recurrence** `(REC)`: `s n · s(n+1) = (n-1)/2`.
   Proof: `s n · s(n+1) = Γ((n+1)/2)/Γ((n-1)/2)` (the `Γ(n/2)` cancels) and
   `Γ((n+1)/2) = Γ((n-1)/2 + 1) = ((n-1)/2)·Γ((n-1)/2)` by `Real.Gamma_add_one`.

2. **Monotonicity**: `n ↦ s n` is increasing. Proof: `log s n =
   logΓ(n/2) − logΓ((n-1)/2)`; convexity of `log∘Γ`
   (`Real.convexOn_log_Gamma`) over the equally-spaced points
   `(n-1)/2 < n/2 < (n+1)/2` gives, via `ConvexOn.slope_mono_adjacent`,
   `logΓ(n/2) − logΓ((n-1)/2) ≤ logΓ((n+1)/2) − logΓ(n/2)`, i.e.
   `log s n ≤ log s(n+1)`, hence `s n ≤ s(n+1)` (`Real.log_le_log_iff`).

3. **Squeeze of the square** `(SQ)`: for `n ≥ 3`,
   `(n-2)/2 = s(n-1)·s n ≤ (s n)² ≤ s n·s(n+1) = (n-1)/2`
   (multiply the monotone inequalities by `s n > 0`, then apply `(REC)` at
   `n-1` and `n`). Therefore `(s n)²/n → 1/2`, i.e. `s n ~ √(n/2)`.

4. **Assemble**: `(√n·c_n)² = (4/π)·n(s n)²/(n-1)² → (4/π)(1/2) = 2/π`, and
   `√n·c_n ≥ 0`, so by continuity of `√`, `√n·c_n → √(2/π)`.

This route uses **no Stirling/Wallis machinery** — only the Gamma recurrence and
log-convexity, both in Mathlib. The `problem.md` only listed Stirling/Wallis/logΓ
routes; the recurrence-squeeze is cleaner and dodges even/odd uniformity issues
entirely (it is uniform in `n`).

### Why monotonicity is the only "real" analytic input

Everything else is algebra over the recurrence. Monotonicity is exactly
log-convexity applied to three equally-spaced abscissae — a one-line slope
comparison once `slope_mono_adjacent` is in hand.

---

## Built Items (this session — file `lean/BuffonConstantAsymptotic.lean`)

All proven (0 sorry) except the final routine packaging:

- `buffonConstant`, `s` — definitions matching the parent.
- `s_pos` — positivity of `s n` for `n ≥ 2`.
- `s_mul_s_succ` — the product recurrence `(REC)`. **proven**
- `s_le_s_succ` — monotonicity via `convexOn_log_Gamma` + `slope_mono_adjacent`. **proven**
- `s_sq_bounds` — the squared squeeze `(SQ)`. **proven**
- `buffonConstant_eq`, `sq_target_eq` — algebraic identities reducing the target
  square to `(4/π)·n(s n)²/(n-1)²`. **proven**
- `sqrt_mul_buffonConstant_tendsto` — main theorem; reduced to ONE isolated
  `sorry`: the rational squeeze `(s n)²/n → 1/2` plus `√`-continuity. Routine
  real analysis (Aristotle-suitable once the prover/Docker is unblocked).

Build status: UNREGISTERED companion (research `lean/` dir, not in gallery
build). Not compiled — Docker build + Aristotle both in blackout this session.
Name-checked against Mathlib v4.26.0 sibling checkout.

---

## Mathlib lemma chain (v4.26.0, all confirmed present)

- `Real.Gamma_add_one (hs : s ≠ 0) : Γ(s+1) = s·Γ s`  — Gamma/Basic.lean:423
- `Real.Gamma_pos_of_pos (hs : 0 < s) : 0 < Γ s`        — Gamma/Basic.lean:456
- `Real.convexOn_log_Gamma : ConvexOn ℝ (Ioi 0) (log∘Γ)` — Gamma/BohrMollerup.lean:115
- `ConvexOn.slope_mono_adjacent`                         — Convex/Slope.lean:28
- `slope_def_field`                                       — AffineSpace/Slope.lean:40
- `Real.log_div`, `Real.log_le_log_iff`                  — Log/Basic.lean:135,144
- `Real.sq_sqrt`, `Real.continuous_sqrt`                 — Data/Real/Sqrt.lean:163,123
- `tendsto_const_div_atTop_nhds_zero_nat`                — SpecificLimits/Basic.lean:51

No Mathlib gap: the only "missing" piece (a Gamma-ratio asymptotic
`Γ(x)/Γ(x+½) ~ x^{-1/2}`) is sidestepped by the recurrence-squeeze.

---

## Dead Ends / Notes

- The Stirling route (`Stirling.factorial_isEquivalent`) works but forces an
  even/odd split (half-integer Gamma → factorials only for one parity); the
  recurrence-squeeze avoids this. Not pursued.
- Direct Gamma-ratio asymptotic: Mathlib has **no** `Real.Gamma_div_Gamma`
  asymptotic lemma at v4.26. Would require building log-Gamma expansion (>300
  LOC). Avoided.

---

## Next Steps

1. Discharge the single `sorry` in `sqrt_mul_buffonConstant_tendsto`:
   - prove `Tendsto (fun n => (s n)^2 / n) atTop (𝓝 (1/2))` by squeezing
     between `1/2 - 1/n` and `1/2 - 1/(2n)` (use
     `tendsto_const_div_atTop_nhds_zero_nat` and
     `tendsto_of_tendsto_of_tendsto_of_le_of_le`);
   - multiply by `(n/(n-1))² → 1`; scale by `4/π`; then `√`-continuity on the
     nonnegative square via `Real.continuous_sqrt`.
2. Build under Docker once unblocked; register as a proper proof file
   (`proofs/Proofs/BuffonsNeedleOQ01OQ02OQ02.lean`) + gallery `meta.json`.
3. Optionally submit the rational-squeeze lemma to Aristotle when the prover is
   back online.

### Session 2026-06-15 (researcher-10) — status confirmation: file at 1 sorry, remaining step is backend-blocked

**Mode:** REVISIT (assessment, no code change). Dual blackout reconfirmed live this
session: `docker info` times out and the Aristotle MCP `prove` tool returned
`"Resource not found"` on a trivial `n+0=n` ping (backend unreachable). No build/Aristotle
available.

Verified `lean/BuffonConstantAsymptotic.lean` is exactly as the prior session left it: the
entire discrete core is proven with **0 sorry** — `s_mul_s_succ` (REC), `s_le_s_succ`
(monotonicity via `convexOn_log_Gamma.slope_mono_adjacent`), `s_sq_bounds` (SQ),
`buffonConstant_eq`, `sq_target_eq`. The **single remaining `sorry`** is the main theorem
`sqrt_mul_buffonConstant_tendsto`, i.e. the analytic packaging only:
`(s n)^2/n → 1/2` (squeeze of `s_sq_bounds`/n between `1/2-1/n` and `1/2-1/(2n)`) →
multiply by `(n/(n-1))^2 → 1` → scale by `4/π` via `sq_target_eq` → `√`-continuity on the
nonnegative square.

**Decision (no edit):** this is a single isolated, *closed* (non-open) real-analysis
sorry — the canonical case for Aristotle per-sorry `prove()`, NOT for blind hand-authoring
under a build blackout. Authoring ~60 lines of `Filter.Tendsto` + ℕ→ℝ cast glue
(`tendsto_of_tendsto_of_tendsto_of_le_of_le'`, `tendsto_one_div_atTop_nhds_zero_nat`,
`Tendsto.const_sub`/`const_mul`, `Tendsto.congr'` on `∀ᶠ n≥2`, `Real.sqrt_sq`,
`Real.continuous_sqrt`) with no compiler feedback would risk shipping a non-compiling file
— so deferred, consistent with the project's blind-authoring caution. The file is
**Aristotle-ready**: submit `sqrt_mul_buffonConstant_tendsto` (with the other lemmas as
context) the moment the prover/Docker returns; expected to close in one shot.

**Net:** no new math; confirmed the problem is purely **infrastructure-BLOCKED** on the
final routine step. Releasing as `progress` (still 1 sorry). No PR — no meaningful, safe,
verifiable code change is available under the blackout.

## Session 2026-06-15 (researcher-5) — ACT: hand-authored the final analytic sorry (build-pending)

**Mode:** ACT. Dual blackout reconfirmed live this session: `docker info` times out
(exit 124); the Aristotle `prove` MCP returned `"Resource not found"` on submission of the
sorry (backend unreachable). So Aristotle — the canonical tool for this closed analytic
sorry per the prior (researcher-10) session — was not available.

**Decision (departs from prior "defer, no PR"):** the prior sessions deferred the single
`sqrt_mul_buffonConstant_tendsto` sorry as Aristotle-bait, citing blind-authoring risk. But
`BuffonConstantAsymptotic.lean` is an **UNREGISTERED** research scratch file (not imported in
`Proofs.lean`, not in the gallery build) — a non-compiling tactic here has **zero blast
radius** (it breaks nothing on main). So hand-authoring the proof, clearly labelled
build-pending/unverified, strictly advances the open question from "bare sorry + prose
strategy" to "concrete proof candidate the next Docker/Aristotle session verifies in one
cheap pass," at no risk to the build.

**What I wrote (replacing the lone sorry; file 240 → ~363 LOC, sorry 1 → 0):**
- `s_sq_div_tendsto : (s n)^2/n → 1/2` — squeeze of `s_sq_bounds` divided by `n` between
  `((n-2)/2)/n = 1/2 - 1/n` and `((n-1)/2)/n = 1/2 - 1/(2n)`, both `→ 1/2`
  (`tendsto_one_div_atTop_nhds_zero_nat` + `const_mul` + `sub`, the bounding-sequence forms
  reached by `Tendsto.congr'` with `field_simp; ring`), squeezed via
  `tendsto_of_tendsto_of_tendsto_of_le_of_le'`; the two `≤` legs by `gcongr` on the shared
  `/n` denominator with `s_sq_bounds` as the numerator leaf.
- `ratio_tendsto_one : n/(n-1) → 1` — write `n/(n-1) = 1/(1 - 1/n)` (`congr'` + `field_simp`),
  limit by `Tendsto.div` of `1` over `1 - 1/n → 1`.
- `ratio_sq_tendsto_one : (n/(n-1))^2 → 1` — `.pow 2`.
- Main theorem: `(√n·c_n)^2 = (4/π)·((s n)^2/n)·(n/(n-1))^2 → (4/π)(1/2)(1) = 2/π` via
  `sq_target_eq` (the algebraic identity, already proven) + `Tendsto.mul`/`const_mul`;
  then `√` of the square recovers `√n·c_n` (it is `≥ 0`, `positivity` via `buffonConstant_eq`)
  using `Real.sqrt_sq` + `Real.continuous_sqrt.tendsto`.

**Honesty / build status:** NOT machine-checked (no compiler under blackout). The
mathematics is complete and correct; only the Lean tactic spelling is unverified. Likely
fragile points flagged in the file header for the next verifier: the exact names
`tendsto_one_div_atTop_nhds_zero_nat`, `Real.continuous_sqrt`, `Real.sqrt_sq`, and whether
`gcongr` discharges the `s_sq_bounds` leaf via `assumption`. The file is still UNREGISTERED;
registration + gallery `meta.json` remain the Docker-up next step (now unblocked once this
compiles, since 0 sorry).

**Files Modified:**
- `research/problems/buffons-needle-oq-01-oq-02-oq-02/lean/BuffonConstantAsymptotic.lean`
  (+3 helper lemmas, main theorem proof, header build-status note; sorry 1 → 0, build-pending)
- `research/problems/buffons-needle-oq-01-oq-02-oq-02/knowledge.md` (this entry)

## Session 2026-06-15 (researcher-3) — build-readiness: all flagged-fragile lemmas name-check PASS

No new math — the proof is already complete (0 sorry, 0 axiom). This session
raises build-confidence and corrects the stale state.md (which still claimed "one
sorry remains"; the file has none).

**Numerical validation of the asymptotic at scale** (lgamma, build-free): with
`c_n = 2·Γ(n/2)/((n−1)·√π·Γ((n−1)/2))`, `√n·c_n` → `√(2/π) = 0.79788456…`:
`n=10²` 0.79988 (rel.err 2.5e-3); `10³` 2.5e-4; `10⁴` 2.5e-5; `10⁵` 2.5e-6;
`10⁶` 2.5e-7. The error scales exactly as `0.25/n`, matching a
`√(2/(πn))·(1+O(1/n))` expansion. The product recurrence `s_n·s_{n+1}=(n−1)/2`
holds to machine precision (n=5→2, n=7→3, n=20→9.5).

**Mathlib name-check @ pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**
(raw.githubusercontent, all PRESENT with matching signatures — clears the file
header's "likely fragile" list):
- `Real.log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y`
  (`Analysis/SpecialFunctions/Log/Basic.lean:144`) — matches `.mp` usage.
- `ConvexOn.slope_mono_adjacent (hf) (hx) (hz) (hxy) (hyz)`
  (`Analysis/Convex/Slope.lean:28`) — matches the `convexOn_log_Gamma` application.
- `Real.convexOn_log_Gamma : ConvexOn ℝ (Ioi 0) (log ∘ Gamma)`
  (`Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:115`).
- `slope_def_field (f) (a) (b) : slope f a b = (f b − f a)/(b − a)`
  (`LinearAlgebra/AffineSpace/Slope.lean:40`).
- `tendsto_one_div_atTop_nhds_zero_nat`
  (`Analysis/SpecificLimits/Basic.lean:57`).
- `tendsto_of_tendsto_of_tendsto_of_le_of_le'` (the squeeze)
  (`Topology/Order/Basic.lean:217`).
`Real.continuous_sqrt`, `Real.sqrt_sq`, `Real.sq_sqrt`, `Real.Gamma_add_one`,
`Real.Gamma_pos_of_pos` are long-standing stable names.

**Conclusion.** Every load-bearing lemma resolves at the pin; the only residual
risk is compiler-level glue (e.g. `gcongr`/`positivity` discharge spelling),
which cannot be settled without a build. Recommendation for the next build-enabled
session: compile, fix any glue, then register (import in `Proofs.lean` + add the
gallery `meta.json`) and promote to verified. Do NOT re-derive — the math is done.

## Session 2026-06-15 (researcher-3, later) — VERIFIED + REGISTERED

Docker recovered (~12:00; builds run off the `lean-mathlib-cache` volume despite
the circular `.lake` host symlink). Built and the proof is now **machine-checked**:
`./proofs/scripts/docker-build.sh Proofs.BuffonConstantAsymptotic` → GREEN, 7743
jobs, 0 errors (Lean v4.26.0, Mathlib `2df2f01`). Registered in `proofs/Proofs.lean`;
gallery entry `src/data/proofs/buffons-needle-oq-01-oq-02-oq-02/meta.json` created
(status `verified`, badge `original`). 0 axioms, 0 sorries.

**Glue repairs needed (no math change), for the record:**
- `s_mul_s_succ`: `field_simp` left `Γ((n-1)/2)·Γ((n-1)/2)⁻¹` uncancelled — added
  `have hg : Γ((n-1)/2) ≠ 0` to context; `field_simp` then closes the goal outright
  (the trailing `ring` became "no goals" and was removed).
- `s_le_s_succ`: in this Mathlib `ConvexOn.slope_mono_adjacent` already returns the
  unfolded `(f b − f a)/(b − a)` form, so `rw [slope_def_field, slope_def_field] at
  key` found no `slope` pattern — the rewrite was deleted (the rest of the proof
  consumes the division form unchanged).
- Six `field_simp; ring` sites (`s_mul_s_succ`, `buffonConstant_eq`, both bounding
  sequences in `s_sq_div_tendsto`, `ratio_tendsto_one`, and `hsq` in the main
  theorem): `field_simp` now closes them, so each redundant `ring` was removed.
  Note `sq_target_eq` still genuinely needs its `ring` after `field_simp`.

Lesson: the S2 name-check was correct (all lemmas present); the only thing a
compiler caught was `field_simp` having grown stronger (closes goals it used to
leave for `ring`) and `slope_mono_adjacent`'s output shape. Both are classic
Mathlib-version-drift glue, invisible to name-checking.
