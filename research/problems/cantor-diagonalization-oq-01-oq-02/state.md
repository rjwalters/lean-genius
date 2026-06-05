# Current State

**Phase**: ACT (Docker-verified clean after Mathlib API drift repair, 2026-06-05)
**Since**: 2026-04-26 (S1 ACT initial formalization) → 2026-06-05 (S2 ACT API drift repair)
**Iteration**: 2

`proofs/Proofs/CantorDiagonalizationOQ01OQ02.lean` is **311 LOC** with **14 theorems**, 7 axioms (all deep set-theoretic results), 10 defs, 0 sorries. **Docker-verified 3061/3061 jobs on 2026-06-05** after a one-iteration API drift repair (April 2026 → June 2026 Mathlib changes).

## S2 ACT (2026-06-05, researcher-1) — Mathlib API drift repair

**Mode**: ACT (file last touched 2026-04-26 by initial S1 author; never Docker-verified. This iteration discharges the gallery-JSON next-action "Docker build to verify compilation" by actually executing it, finding 5 hard errors + 3 warnings, and fixing all of them.)

**Outcome**: ~10 lines edited; 5 errors → 0; 3 warnings → 0; **Docker-verified 3061/3061 jobs**.

### What broke and what was fixed

Six categories of Mathlib API drift (April → June 2026, Mathlib v4.26.0):

1. **`λ` reserved as binder** (line 65): Lean 4 parser now rejects `λ` (Unicode lambda) as a bound-variable name; reserved for lambda abstraction. Renamed to `μ`.
2. **`Ordinal.cof` returns Cardinal** (line 69): the `.card` projection no longer applies; `cof` now produces a Cardinal directly.
3. **`MartinsMaximum → MartinsAxiom`** (line 118): direction issue — `le_of_eq` was wrong for an `≥` target; replaced with `ge_of_eq`.
4. **`continuum` ambiguity** (lines 179, 190, 268): conflict with `𝔠` notation / `Cardinal.continuum`; qualified all references with `ContinuumHypothesis.continuum`.
5. **`Cardinal.aleph_lt` renamed** (lines 183, 194, 280): now `Cardinal.aleph_lt_aleph`; matches sibling file `CantorDiagonalizationOQ01OQ01OQ02.lean`.
6. **`omega` on Ordinal target** (line 284): `Cardinal.aleph_lt_aleph.mpr` requires an Ordinal-side inequality which `omega` cannot handle. Wrapped with `exact_mod_cast` from a ℕ-side `omega` proof; matches sibling file pattern (`CantorDiagonalizationOQ01OQ01OQ02.lean:239`).
7. **Unused simp args** (line 270, was `gch_implies_ch`): replaced explicit `simp only [Nat.zero_add, Cardinal.aleph_zero]` with `simpa` after `unfold`.

### What did NOT change

- **0 new theorems, 0 new axioms, 0 new definitions.** Pure API-drift repair.
- **All 7 axioms retained** (deep set-theoretic results not in Mathlib).
- **All 14 theorems retained**.

### Counts after S2 ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `CantorDiagonalizationOQ01OQ02.lean` | **311** | **14** | 7 | 10 | 0 |

### Build status

**Docker-verified clean**: `./proofs/scripts/docker-build.sh Proofs.CantorDiagonalizationOQ01OQ02` → `✔ [3061/3061] Built ... (7.9s) === Build succeeded ===`. Mathlib v4.26.0.

## Current Focus

**Gallery file is now buildable under current Mathlib.** The 7 axioms remain legitimate (none are routine; all require Mathlib infrastructure that does not exist: forcing theory for Lévy-Solovay and MM/MA consistency, inner model theory for Woodin's Ultimate-L). The file is honestly `status: axiomatized`.

## Active Approach

Pure API-drift repair iteration. No new mathematical content; the focus is keeping the existing formalisation buildable as Mathlib evolves.

## Blockers

- **Forcing theory absent from Mathlib**: blocks reduction of 6 of the 7 axioms (Lévy-Solovay × 4, mm_consistent, ma_consistent). Multi-year infrastructure project; unlikely to land before 2027.
- **Inner model theory absent from Mathlib**: blocks reduction of `ultimate_l_implies_ch_consistent` (and the underlying open Ω-conjecture remains a genuinely open mathematical question, so axiomatisation is necessary regardless).

## Next Action

**Either of (lower priority, doc-only):**

1. **Gallery `meta.json` enrichment**: add explicit references to Lévy-Solovay (1967), Foreman-Magidor-Shelah (1988), Woodin's Ultimate-L program. The file's docstrings already cite these but the gallery JSON does not. ~1 session; doc-only.

2. **Cross-reference to sibling gallery entries**: e.g., `cantor-diagonalization-oq-01-oq-01-oq-02` (Easton's theorem for full GCH), `continuum-hypothesis` parent. Add `relatedGalleryProofs` entries. ~1 session; doc-only.

**Or (higher priority but blocked):**

3. **Axiom reduction is BLOCKED** until Mathlib has forcing / inner model theory. This is not feasible in a single research session and likely not feasible in 2026.

## Attempt Counts

- Total attempts: 2 (S1 ACT 2026-04-26 + S2 ACT 2026-06-05)
- Current approach attempts: 1 (API drift repair, this iteration)
- Approaches tried: 2 (S1: initial formalisation; S2: API drift repair)
