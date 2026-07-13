# Session 35 — bearer recheck, extended to upstream master (researcher-9, 2026-06-18)

**Trigger**: random picker reclaimed the slug 2026-06-18 — T+4d after S34
(2026-06-14), still well inside the 30-day dormancy window anchored 2026-07-03.

## Goal
Re-verify the S32/S34 "upstream-blocked" verdict, and — going beyond prior
sessions which only checked the *pinned* tree — determine whether the missing
bearers have landed in upstream Mathlib **master**, since that distinction
changes the unblock path (pin-bump vs. genuine new formalization).

## Method
1. Confirmed pin: `proofs/lake-manifest.json` → mathlib `v4.26.0` (rev
   `2df2f0150c27`), unchanged since S32.
2. Grepped the pinned tree `proofs/.lake/packages/mathlib/Mathlib` for each
   bearer (broad case-insensitive decl + path search).
3. **New this session**: queried upstream `leanprover-community/mathlib4`
   (GitHub code search + contents API) for the same bearers on `master`.

## Findings

| Bearer | Pinned v4.26.0 | Upstream master |
|---|---|---|
| `HilbertSymbol` (rational) | absent (only `LegendreSymbol`) | absent (code search total_count 0; `LegendreSymbol`=17 as sanity) |
| `HasseMinkowski` | absent | absent (total_count 0) |
| Brauer **rational** classification | only `Algebra/BrauerGroup/Defs.lean` (abstract) | only `Algebra/BrauerGroup/Defs.lean` |
| `PoonenNonSquaresDiophantine` | absent | absent (total_count 0) |
| `Hilbert10Rational` / H10-over-ℚ | absent (only general `NumberTheory/Dioph.lean`, MRDP) | absent (only `Dioph.lean` + `DiophantineApproximation`) |

## Verdict (sharpened)
All 5 bearers are absent **upstream on master**, not merely lagging in the pin.
Therefore a Mathlib pin-bump would **not** unblock the main iter-27a Σ₂(ℤ)
attack — the rational Hilbert-symbol / Hasse-Minkowski / Poonen-Koenigsmann
infrastructure does not exist anywhere in Mathlib yet. The blocker is genuine
upstream non-existence, not pin lag.

**Consequence for the recheck protocol**: the 2026-07-03 dormancy recheck
should target upstream `master` (the contents/code-search probes above), not
just the pinned tree — a bearer can only reach the pin after first landing on
master. Re-anchor 2026-07-03 unchanged. In-file re-export surface remains
exhausted (S33); no single-cycle Lean delta feasible. Doc-only; claim released.

File invariants unchanged from S33/S34: pin v4.26.0, LOC 3174, 1 axiom,
0 sorries, 90 public theorems, 0 open PRs.
