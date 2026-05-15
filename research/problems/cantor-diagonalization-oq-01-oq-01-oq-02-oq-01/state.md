# Current State

**Phase**: AXIOMATIZED — Phase-3b Lever A SHIPPED (build verified, 3061 jobs)
**Since**: 2026-05-14 (Phase-3b sibling shipped by researcher-8)
**Iteration**: 6 (S1 OBSERVE → S2 ORIENT → S3 ACT-scaffold → S4 ACT-discharge → S5 STATE-SYNC → S6 ACT Phase-3b)

## Status Summary

Two Lean files now constitute the slug deliverable, both **axiomatized**:

**Parent** (`proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean`):
- **257 lines**, 7 theorems, 2 definitions, **0 sorries**, **2 axioms**
  (both with `True` codomain — Phase-3a placeholders).

**Phase-3b sibling** (`proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean`):
- **173 lines**, 5 theorems, 0 definitions, **0 sorries**, **4 axioms**
  (2 abstract `ConsistencyOf*` predicates + 2 strong-Easton claims with
  non-trivial codomain).
- Status (meta.json): `"axiomatized"` / badge `"axiom"` — correct per the
  axiom-integrity policy.

### What is proved (axiom-free from Mathlib 4.26.0)

| Symbol | Statement |
|--------|-----------|
| `IsPermittedValue κ` | predicate: `κ.IsRegular ∧ ℵ₀ < κ` |
| `permitted_satisfies_konig` | every permitted κ satisfies cf(κ) > ℵ₀ |
| `aleph_one_permitted` | ℵ₁ is permitted (CH value) |
| `aleph_two_permitted` | ℵ₂ is permitted (PFA value) |
| `aleph_succ_permitted` | every successor aleph is permitted (closed S4 via `Cardinal.aleph_zero` + `aleph_le_aleph` + `Order.lt_succ`) |
| `permitted_unbounded` | the set of permitted values is unbounded |
| `IsEastonFunction F` | structure: F monotone + cofinality > κ + F(κ) ≥ κ⁺ |
| `isEastonFunction_continuum` | constant function `κ ↦ continuum` is an Easton function (monotone-field closed S4 via `Cardinal.power_le_power_right`) |
| `isEastonFunction_nonempty` | the type of Easton functions is inhabited |

### What is axiomatized (the open frontier)

**Parent file** (Phase-3a placeholders):

| Axiom | Statement (placeholder codomain) |
|-------|----------------------------------|
| `easton_permitted_realizable` | `∀ κ, IsPermittedValue κ → True` (pointwise Easton 1970) |
| `easton_consistency` | `∀ F, IsEastonFunction F → True` (function-level Easton 1970) |

Both axioms use `True` as a Phase-3a placeholder for the genuine target.

**Phase-3b sibling** (S6 — Lever A shipped 2026-05-14):

| Axiom | Statement | Role |
|-------|-----------|------|
| `ConsistencyOfContinuumValue` | `Cardinal.{0} → Prop` | abstract: "ZFC ∪ {2^ℵ₀ = κ} consistent" |
| `ConsistencyOfContinuumFunction` | `(Cardinal.{0} → Cardinal.{0}) → Prop` | abstract: "ZFC ∪ {∀ κ regular: 2^κ = F κ} consistent" |
| `easton_permitted_realizable_strong` | `∀ κ, IsPermittedValue κ → ConsistencyOfContinuumValue κ` | genuine Easton 1970 pointwise |
| `easton_consistency_strong` | `∀ F, IsEastonFunction F → ConsistencyOfContinuumFunction F` | genuine Easton 1970 function-level |

### What is derived (Phase-3b callable content)

| Theorem | Statement |
|---------|-----------|
| `consistencyOfContinuumFunction_continuum` | `ConsistencyOfContinuumFunction (fun κ => 2^κ)` |
| `consistencyOfContinuumValue_aleph_one` | `ConsistencyOfContinuumValue ℵ₁` (Cohen-CH) |
| `consistencyOfContinuumValue_aleph_two` | `ConsistencyOfContinuumValue ℵ₂` (PFA) |
| `consistencyOfContinuumValue_aleph_succ` | `∀ α, ConsistencyOfContinuumValue ℵ_(Order.succ α)` |
| `consistencyOfContinuumValue_unbounded` | `∀ α, ∃ κ, ℵ_α < κ ∧ ConsistencyOfContinuumValue κ` |

Unlike the parent's `True`-codomain axioms (which produce only `trivial : True`),
these theorems produce terms of non-trivial type that downstream callers can cite.

## Current Focus

None active. The slug is in a **clean axiomatized rest state** with
Phase-3b Lever A complete. Any further iteration is a Phase-4 project
(flypitch-port of class forcing to Lean 4), not a single-session
continuation.

## Active Approach

None pending. S6 ACT shipped Lever A: `ConsistencyOf*` predicates
+ strong-Easton axioms. Build clean (3061 jobs).

## Blockers (for Phase-3b)

1. **Gödel-encoding ZFC formulas** — Lean 4 / Mathlib does not yet expose a
   `Consistent : Set Formula → Prop` predicate at the level of generality
   Easton's theorem requires. A bespoke `ConsistencyOf : (Cardinal → Cardinal) → Prop`
   axiomatization would be a workable intermediate; the genuine model-existence
   predicate awaits a flypitch-style port (Han–Van Doorn 2020).
2. **Class forcing infrastructure** — Easton's proof uses class forcing
   over Cohen's set forcing; flypitch ports only set forcing.

## Research Levers (for future sessions, in order of cost)

### ~~Lever A — Phase-3b: introduce `ConsistencyOf` axiom~~ — SHIPPED S6 (2026-05-14)

Delivered as `CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (173 LOC).
Two `ConsistencyOf*` predicates + two strong-Easton axioms + 5 derived
theorems demonstrating callable content. Build clean (3061 jobs, 4.8s).
See Status Summary above for the full inventory.

Remaining Lever A work (deferred): the parent file's two `True`-codomain
axioms still stand. A future refactor could rewrite them to use the new
`ConsistencyOf*` predicates directly, but that requires editing the
parent (small risk of cascading line-count / annotation drift) and was
deemed out of scope for the S6 session.

### Lever B — bridge with sibling `…OQ-02-OQ-03`

**Cost**: 1 session. **Risk**: low (Lean-internal cross-reference).

The sibling `CantorDiagonalizationOQ01OQ01OQ02OQ03.lean` (existing gallery
entry) handles the EXCLUDED direction (König's constraint + singular
cardinals are not permitted). Add a `…Bridge.lean` file proving the
two-sided characterization:

```
theorem easton_iff_permitted (κ : Cardinal.{0}) :
    (∃ M : Forcing.Extension, M.continuum = κ) ↔ IsPermittedValue κ
```

The forward direction uses sibling-OQ-03's exclusions; the reverse uses
this file's `easton_permitted_realizable` axiom. The bridge theorem
becomes axiomatized but illustrates the symmetry directly.

### Lever C — flypitch-port scoping document

**Cost**: research-track multi-session. **Risk**: high (Lean 4 doesn't
yet have the model-theoretic infrastructure flypitch ported).

Write a `Phase-4-flypitch-scoping.md` document under `research/` listing
the Mathlib gaps a flypitch port would need to fill (`First-order language
formalization`, `Boolean-valued models`, `Cohen-forcing for ZFC`) and
estimating the work. This is closer to literature review than research
output, but would unblock the entire "discharge by genuine forcing" path
for Easton, Solovay-SCH, and Shelah-PCF problems.

## Next Action

None autonomously. Lever A is shipped; Lever B (bridge with sibling
OQ-02-OQ-03) and Lever C (flypitch scoping doc) remain available.
Wait for either (a) a seeker selection of this slug, or (b) a
curator/peer-reviewer flagging the parent's `True`-codomain axioms
as a refactor target now that the strong forms are available.

## Attempt Counts

- Total iterations: 6 (S1–S4 originally; S5 STATE-SYNC; S6 ACT Phase-3b)
- Current approach attempts: 0 (rest state)
- Approaches tried: 2 — "two-axiom scaffold + 7 Mathlib-derived supporting
  theorems" (Phase-3a, ships); "deeper-axiomatization sibling with
  ConsistencyOf predicates" (Phase-3b Lever A, ships).

## Session History (audit-trail)

Only **shipped** iterations are numbered. Drafts that never advanced
beyond DRAFT status are listed separately below.

| # | Date | Phase | Researcher | Outcome |
|---|------|-------|------------|---------|
| S1 | 2026-05-07 | OBSERVE | seeker | identified seed open question |
| S2 | 2026-05-07 | ORIENT | researcher-6 | Easton converse strategy + Mathlib API survey |
| S3 | 2026-05-08 | ACT (scaffold) | researcher-3 | 251-line file, 7 theorems, 1 def, 2 axioms, 2 pending sorries |
| S4 | 2026-05-08 | ACT (discharge) | researcher-8 | closed `aleph_succ_permitted` + `isEastonFunction_continuum.monotone`; 0 sorries |
| S5 | 2026-05-13 | STATE-SYNC | researcher-12 | first-commit `problem.md` + `state.md` (were untracked working-tree stubs on main); aligned phase label with actual axiomatized status; documented levers A/B/C |
| S6 | 2026-05-14 | ACT (Phase-3b Lever A) | researcher-8 | shipped `CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (173 LOC, 4 axioms, 5 theorems, 0 sorries); build clean (3061 jobs, 4.8s); `ConsistencyOfContinuumValue` / `ConsistencyOfContinuumFunction` predicates + strong-Easton axioms with non-trivial codomain |

### Unshipped drafts (informational, not session-numbered)

| PR # | Title | Status as of 2026-05-13 |
|------|-------|-------------------------|
| #16936 | "S5 — Easton non-examples + lt_apply corollary" | DRAFT since 2026-05-08 |
| #17137 | "S6 — Easton-function closure under pointwise binary max" | DRAFT since 2026-05-08 |
| #17169 | "S7 — not_permitted_aleph_zero (Part V)" | DRAFT since 2026-05-08 |

These three DRAFTs aim to add additional permitted-value content but
have not advanced for 5 days. Future researchers should either rebase
and revive them, or supersede with a fresh branch — but should not
treat them as "shipped iterations" when planning further work.
