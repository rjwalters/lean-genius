# S2 ACT — Mathlib API Drift Repair (Docker-Verified Clean)

**Date**: 2026-06-05
**Author**: researcher-1
**Phase**: ACT (Docker build, repair, re-verify)
**Iteration**: 2 (after S1 ACT 2026-04-26)
**Mode**: ACT — file was last touched 2026-04-26 (S1) and never Docker-verified; this iteration discharges the gallery-JSON next-action "Docker build to verify compilation" by actually doing it, finding ~6 Mathlib API drift breakages, and fixing them.

## Outcome

`proofs/Proofs/CantorDiagonalizationOQ01OQ02.lean` was **broken** at HEAD on 2026-06-05: 5 hard errors + 3 warnings under current Mathlib v4.26.0. Net change ~10 lines edited to repair API drift; no mathematical content added or removed. **Docker-verified 3061/3061 jobs after repair.**

## What broke and why (Mathlib API drift, April → June 2026)

| Line | Old API | New API | Notes |
|---|---|---|---|
| 65 | `∀ λ : Cardinal.{0}, λ < κ → 2 ^ λ < κ` | `∀ μ : Cardinal.{0}, μ < κ → 2 ^ μ < κ` | Lean 4 parser tightened: `λ` (lambda Unicode) can no longer be a binder name; reserved for lambda abstraction. Renamed to `μ`. |
| 69 | `κ.ord.cof.card = κ` | `κ.ord.cof = κ` | `Ordinal.cof : Ordinal → Cardinal` returns Cardinal directly; the `.card` projection no longer applies (`Quot.card` does not exist). |
| 118 | `le_of_eq` | `ge_of_eq` | `MartinsMaximum : x = y`, `MartinsAxiom : x ≥ y` (i.e. `y ≤ x`). The conversion direction needs `ge_of_eq : a = b → a ≥ b`, not `le_of_eq`. |
| 179, 190, 268 | `unfold CH aleph_one continuum` | `unfold CH aleph_one ContinuumHypothesis.continuum` | `continuum` is now ambiguous (clashes with the `𝔠` notation / Mathlib's `Cardinal.continuum`). Qualified with the parent namespace. |
| 183, 194, 280 | `Cardinal.aleph_lt.mpr` | `Cardinal.aleph_lt_aleph.mpr` | The lemma was renamed (sibling files `CantorDiagonalizationOQ01OQ01OQ02.lean` already use the new name, so this is internally consistent). |
| 273 (was 273 of `gch_implies_ch`) | `simp only [Nat.zero_add, Cardinal.aleph_zero] at h0; exact h0` | `simpa using h0` (after `unfold`) | The two simp arguments were flagged as unused; `simpa` after `unfold CH ContinuumHypothesis.continuum aleph_one` handles the residual `0 + 1 = 1` and `Cardinal.aleph 0 = ℵ₀` reductions in one shot. |
| 284 (was 280 of `gch_continuum_below_aleph_add_two`) | `Cardinal.aleph_lt_aleph.mpr (by omega)` | `Cardinal.aleph_lt_aleph.mpr (by exact_mod_cast (by omega : (n + 1 : ℕ) < n + 2))` | `Cardinal.aleph_lt_aleph` returns an Ordinal-side inequality `(n + 1 : Ordinal) < (n + 2 : Ordinal)`; `omega` does not handle Ordinal, so we cast via `exact_mod_cast` from the ℕ-side inequality. This is the same pattern sibling file `CantorDiagonalizationOQ01OQ01OQ02.lean:239` uses. |

## What did NOT change

- **No new theorems, no new axioms, no new definitions.** Pure API-drift repair.
- **All 7 axioms retained**: `levy_solovay_inaccessible_ch/not_ch`, `levy_solovay_measurable_ch/not_ch`, `mm_consistent`, `ma_consistent`, `ultimate_l_implies_ch_consistent`. These are all deep results not in Mathlib (forcing theory, inner model theory, Woodin's Ultimate-L program); none can be reduced without infrastructure that Mathlib v4.26.0 does not have.
- **All 14 theorems retained**: `measurable_is_inaccessible`, `inaccessible_is_strong_limit`, `inaccessible_uncountable`, `measurable_implies_inaccessible`, `mm_implies_ma`, `inaccessible_independent_of_ch`, `measurable_independent_of_ch`, `mm_implies_not_ch`, `ma_implies_not_ch`, `gch_implies_ch`, `gch_decides_all_aleph`, `gch_continuum_below_aleph_add_two`, `large_cardinals_and_ch_summary`, `ch_independent_of_large_cardinals`.

## Counts after S2 ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `CantorDiagonalizationOQ01OQ02.lean` | **311** | **14** | 7 | 10 | 0 |

(Up from 306 LOC pre-repair; difference is ~5 lines of doc clarifying the API drift.)

## Build status

**Docker-verified clean**:
`./proofs/scripts/docker-build.sh Proofs.CantorDiagonalizationOQ01OQ02`
→ `✔ [3061/3061] Built Proofs.CantorDiagonalizationOQ01OQ02 (7.9s)`
→ `=== Build succeeded ===`.
Mathlib v4.26.0.

## Remaining work

- **Gallery integration**: the file is `axiomatized` (7 axioms, all deep set-theoretic results). The gallery `meta.json` should reference Lévy-Solovay (1967), Foreman-Magidor-Shelah (1988), and Woodin's Ultimate-L program as the source of the axioms. Each axiom is honestly labeled in the file as a relative-consistency assertion or open conjecture.
- **Axiom elimination**: in principle, **none of the 7 axioms** can be reduced without:
  - Mathlib formalisation of forcing (Lévy-Solovay, Cohen, MM/MA consistency proofs)
  - Mathlib formalisation of inner model theory (Ultimate-L, Woodin's program)
  - Neither exists in Mathlib v4.26.0; both would be multi-year infrastructure projects.
- **Cross-references**: the file is well-placed as a Cantor diagonalization gallery extension; explicitly cross-referencing related entries (e.g., `cantor-diagonalization-oq-01-oq-01-oq-02` on Easton's theorem for full GCH) would strengthen the gallery navigation. This is a separate enrichment task.

## Honesty

This iteration is **pure infrastructure repair**: 0 new mathematical theorems, 0 new axioms, 0 sorries closed, 0 axioms eliminated. The value is making a previously-unbuildable gallery file actually buildable under current Mathlib. The gallery JSON's stated `nextAction` was "Docker build to verify compilation" — that has been executed for the first time since the file was created in April 2026; the file did NOT build (5 hard errors) and now does build (3061/3061 clean).

The mathematical claims in the file (Lévy-Solovay independence, MM/MA → ¬CH, GCH → CH, gch_continuum_below_aleph_add_two) are correct and proven (modulo the 7 axiomatised deep results). The Continuum Hypothesis question — "is CH decided by large cardinal axioms?" — is answered honestly: **partially** (standard large cardinals: no, by Lévy-Solovay; forcing axioms: yes, by Foreman-Magidor-Shelah; Ultimate-L: open).
