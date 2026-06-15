# Research State: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01

## Current State
**Phase**: ACT (build-pending)
**Path**: full
**Since**: 2026-06-15
**Iteration**: 6

## Session 5 — Strategy D ACT: Lean transcription (researcher-1, 2026-06-15)

**Goal**: Convert the 4-session ORIENT (Strategy D "paste-port-ready" since S4) into the
actual Lean file. Both backends still down (Docker `docker info` 20s timeout; Aristotle MCP
`prove` → "Resource not found"), so this ships **build-pending** — CI is the ground truth per
the project's established pattern. Continuing to defer would only re-confirm an already-stable
verdict, so the proportionate move is the transcription itself.

**What shipped**: new file `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean`
(registered in `Proofs.lean`), implementing the full integral-closure descent — **0 sorries,
0 axioms**:

| Theorem | Role |
|---|---|
| `isIntegral_sqrt_natCast` | `√(k:ℕ)` integral over ℤ (root of monic `X²−C k`; `monic_X_pow_sub_C` + `Real.sq_sqrt`) |
| `alpha_isIntegral` | α integral over ℤ via three `IsIntegral.add` |
| `sqrt_bounds` | generic bracket `lo<√x<hi` from `lo²<x<hi²` (`Real.sqrt_lt_sqrt`/`Real.sqrt_sq`) |
| `alpha_gt_eight`, `alpha_lt_nine` | `8<α<9` from the rational witnesses (1.41…2.65) |
| `irrational_…_plus_sqrt7` | main: descend along `isIntegral_algebraMap_iff`, `IsIntegrallyClosed.isIntegral_iff` ⇒ `q∈ℤ`, contradicted by bounds + `omega` |

**Verification done (build-free)**: re-ran `verify_strategy_d.py` → ALL CHECKS PASSED (integrality
of each √k, degree-16 minimal poly, and the exact radical witnesses 141/100…53/20 that the Lean
`norm_num` bounds rely on). In-repo cross-checks: `monic_X_pow_sub_C (k:ℤ) (h:n≠0)` and
`isIntegral_algebraMap_iff (algebraMap _ _).injective` both already used in
`NthRootIrrationalOQ01.lean` / `AngleTrisectionOQ02OQ01OQ02Incomplete01.lean`; descent +
integrally-closed bearers file:line-confirmed at pin v4.26.0 (S4).

**Self-review fix**: caught and corrected a `sqrt_bounds` bug pre-commit — the upper branch's
`Real.sqrt_lt_sqrt` needs `0 ≤ x`, which `positivity` cannot prove for an abstract `x`; derived
it from `lo²<x` via `lt_of_le_of_lt (sq_nonneg lo) h1`.

**Residual transcription risk (not Lean-checked, backends down)**: (i) the `simp only` aeval set
in `isIntegral_sqrt_natCast`; (ii) `IsIntegrallyClosed.isIntegral_iff` / `eq_ratCast` instance
resolution (`IsScalarTower ℤ ℚ ℝ`, `IsFractionRing ℤ ℚ`). All math is verifier-confirmed; only
Lean plumbing is at risk. If CI flags either, patch the single offending line.

**Prior state (S1–S4, retained below)**: ORIENT (ACT-ready), iter 5.

## Current Focus
Strategy D is now **paste-port-ready** (Session 4, researcher-5). Every step of the
integral-closure descent has a Mathlib bearer **confirmed at the repo pin `v4.26.0`**: the
previously-unnamed "descent along `algebraMap ℚ ℝ`" is `isIntegral_algebraMap_iff`
(`Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:179`) and the ℤ-step is
`IsIntegrallyClosed.isIntegral_iff`
(`Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:210`). Combined with Session 3's
durable `verify_strategy_d.py` and the bound-witness recipe, no genuinely-open Mathlib gap
remains for Strategy D — only transcription. Still build-gated: Docker down (`docker info` 15s
timeout) AND Aristotle MCP `prove` returns "Resource not found" (probed this session).

## Active Approach
Strategy D — α = √2+√3+√5+√7 is a sum of algebraic integers ⇒ integral over ℤ; a rational
integral over ℤ lies in ℤ; but 8 < α < 9 ⇒ not an integer ⇒ irrational. Full bearer-confirmed
descent chain in knowledge.md Session 4. Deferred to ACT until Docker/Aristotle returns.
Fallback: Strategy A (elementary 3-squaring chain) or `m(α)=0` + rational-root theorem.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Docker build wrapper unavailable (`docker ps` timeout) — cannot verify Lean locally.
- Aristotle MCP tools now load but `prove` returns "Resource not found" — backend still down,
  cannot delegate the proof.

## Next Action
When Docker **or** Aristotle returns, **transcribe** Strategy D into
`Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (~60–100 LOC). All lemma names are
now confirmed at pin `v4.26.0` (knowledge.md Session 4): step 1 `IsIntegral.add` ×3 over
`IsIntegral ℤ (√k)` (monic `X²−C k`, `Real.sq_sqrt`); step 2 descent
`isIntegral_algebraMap_iff` (`IsIntegral/Basic.lean:179`, needs `[IsScalarTower ℤ ℚ ℝ]` +
`(algebraMap ℚ ℝ).injective`); step 3 `IsIntegrallyClosed.isIntegral_iff`
(`IntegrallyClosed.lean:210`, ℤ integrally closed by instance); step 4 bounds `8<α<9` via the
Session-3 `norm_num` witness recipe ⇒ contradiction. Residual transcription risks: cast plumbing
`√(2:ℕ)` vs `√(2:ℝ)` in step 1, and instance firing for `IsScalarTower ℤ ℚ ℝ`/`IsFractionRing ℤ ℚ`.
Fallbacks: Strategy A (3-squaring chain) or `m(α)=0` + rational-root theorem. Re-run
`verify_strategy_d.py` to re-confirm all math artifacts.
