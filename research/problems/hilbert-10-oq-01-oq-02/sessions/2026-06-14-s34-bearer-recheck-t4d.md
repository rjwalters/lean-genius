# Iteration 27a S34 — T+4d Mathlib upstream bearer recheck

**Date**: 2026-06-14
**Researcher**: researcher-1
**Phase**: PREP / bearer-recheck (interim check against the S32 PREP-3
release verdict and the S33 iter 27a-δ "deltas exhausted" verdict)
**Type**: Doc-only. No edits to `proofs/Proofs/Hilbert10OQ01OQ02.lean`,
gallery `meta.json`, or `knowledge.{md,markdown}` content semantics. Edits
limited to this session log, `state.md` (S34 prepend), and
`src/data/research/problems/hilbert-10-oq-01-oq-02.json`
(`currentState.focus` + `knowledge.progressSummary` prepend + `lastUpdate`).
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged since PREP-2; v4.26.0).

## Headline

**5/5 dormant verdict holds at T+4d.** No new Mathlib PR motion on any of
the 5 missing bearers (`HilbertSymbol`, `HasseMinkowski`, `BrauerRational`,
`PoonenNonSquaresDiophantine`, `Hilbert10Rational`) since the S32 PREP-3
baseline (2026-06-09). The 30-day re-survey cadence anchored to **2026-07-03
is unchanged.** S33 already shipped iter 27a-δ (the only feasible
single-cycle Lean delta) on 2026-06-10 — so there is no in-file delta left
to ship this cycle either. Claim re-released; researcher-1 returns to the
pool.

## Why this session exists

The slug was reclaimed by the random picker on 2026-06-14 (~T+4d after S33
shipped iter 27a-δ on 2026-06-10, and well inside the 30-day dormancy
window S32 anchored to 2026-07-03). With the only single-cycle Lean delta
(27a-δ) already merged and the main 27a Σ₂(ℤ) attack upstream-blocked, the
honest move on an in-window reclaim is to verify the release verdict still
holds rather than fabricate a cosmetic theorem. This session does the
verification.

## Survey method

1. **Pinned-tree bearer presence** — `gh api .../contents/...?ref=<pin>` to
   confirm the bearer source files are still absent from the pinned Mathlib
   tree (not just from HEAD).
2. **PR motion since S32 baseline** — `gh search prs --repo
   leanprover-community/mathlib4 <kw> --updated ">=2026-06-09"` for each of
   the 5 bearer keywords.

## Findings — pinned-tree presence (ref = pin)

| Path queried | Result |
|---|---|
| `Mathlib/NumberTheory/` listing | only `DiophantineApproximation` (the unrelated continued-fractions bearer); no `HilbertSymbol`, `HasseMinkowski`, `Hilbert10`, or Diophantine-definability file |
| `Mathlib/Algebra/BrauerGroup/` listing | only `Defs.lean` (abstract Brauer-group infrastructure) — **no** rational classification / `BrauerRational` bearer |
| `HilbertSymbol` (code search, repo-scoped) | 0 code hits in mathlib4 (only `docs/references.bib` Matiyasevich citation + a `Topology/.../PiNat.lean` "Hilbert cube" string, both unrelated) |
| `HasseMinkowski` (code search, repo-scoped) | 0 code hits |

The only Brauer infrastructure present at the pin is abstract
(`Algebra/BrauerGroup/Defs.lean`); it does **not** carry the rational
classification (`Br(ℚ)` exact sequence / local-global) the 27a Σ₂(ℤ) attack
needs. This matches the S32 note that the Brauer bearer is "dormant since
2025-01" — abstract defs exist, the rational classification does not.

## Findings — PR motion since S32 (>= 2026-06-09)

| # | Bearer keyword | New/updated PRs since 2026-06-09 | Δ |
|---|----------------|--------------------------------:|---|
| 1 | `HilbertSymbol` | 0 | **none** |
| 2 | `HasseMinkowski` | 0 | **none** |
| 3 | `brauer` | 0 | **none** |
| 4 | `Poonen` | 0 | **none** |
| 5 | `Hilbert10` | 0 | **none** |

**Net at T+4d**: 5/5 still dormant. Zero upstream motion on the five
load-bearing objects since the S32 baseline.

## Invariants verified at T+4d

| Surface | S33 (2026-06-10) | S34 (2026-06-14) | Δ |
|---|---|---|---|
| Mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | same | = |
| `Hilbert10OQ01OQ02.lean` LOC | 3174 | 3174 | = |
| Axiom count | 1 (`koenigsmann_2016_universal`) | 1 | = |
| Sorries | 0 | 0 | = |
| theoremCount | 90 | 90 | = |
| Open PRs on slug | 0 | 0 | = |

All invariants stable. The mathematical surface is in the holding pattern
S30/S31/S32/S33 documented.

## Verdict — re-anchor unchanged

- **S32's "no motion → release" branch continues to fire** at T+4d.
- **30-day cadence anchor `2026-07-03` is unchanged** — S34 does not reset
  it.
- **iter 27a-δ is already shipped (S33, 2026-06-10)** — the in-file
  re-export surface against the existing Σ₁/Π₁/Σ₂/Π₂ lattice is exhausted;
  there is no remaining single-cycle Lean delta to ship this cycle.
- **Claim re-released** ahead of TTL expiry.
- Recommended **next-pickup gate**: don't pull the slug back via
  `claim-random` before 2026-07-03 unless a Mathlib bearer event is detected
  externally (any new PR/issue mentioning `HilbertSymbol`, `Hasse-Minkowski`,
  `Brauer ℚ` / `BrauerQ` / rational Brauer classification, `Poonen
  Diophantine`, or `Hilbert10` / `H10/Q`).

## Picker matrix (carried from S32/S33)

| ID | Description | Status |
|---|---|---|
| 27a | Σ₂(ℤ) attack via Koenigsmann lift + complement-collapse against `IntegersAreExistentialUniversalOverQ` | ⏳ **upstream-blocked** (5/5 bearers absent + dormant at T+4d) |
| 27a-δ | Sharpen H10/ℚ implication chain via re-export theorems | ✅ **shipped S33 (2026-06-10)** — surface now exhausted |
| 27a-γ | Upstream Mathlib contribution of HilbertSymbol + Hasse-Minkowski over ℚ | ⏳ multi-quarter deferred |
| 27b/27c/27d/27e | level-2 cell closures / stale-PR cleanup / Daans axiom / trivial-set dualities | 🚫 anti-candidates (see S32) |

## Deliverables (this PR, doc-only)

1. **NEW session memo**: this file.
2. **state.md head**: S34 prepend.
3. **Canonical JSON** (`src/data/research/problems/hilbert-10-oq-01-oq-02.json`):
   `knowledge.progressSummary` prepend with S34 narrative; `currentState.focus`
   pointer update; `lastUpdate` → 2026-06-14.

## Out of scope (deferred)

- Gallery `meta.json` numerics — Lean file unchanged, no drift.
- `pnpm build` — slug-targeted JSON edit only.
- Lean file edits — none required for a doc-only T+4d recheck; 27a-δ already
  exhausted the in-file delta in S33.
- New 27a-δ-style theorems — declined: the existing Σ₁/Π₁/Σ₂/Π₂ re-export
  surface is exhausted, and further glue would be cosmetic scaffolding.
