# Can moduli space theory be formalized in Mathlib to remove the 2 axioms

## Source

- **Proof**: Motivic Class of Genus 0 Maps to Flag Varieties (`motivic-flag-maps`)
- **Type**: open-question
- **Category**: extension
- **Tractability**: challenging (full removal: blocked on Mathlib's lack of moduli/K₀(Var); sub-goal A: tractable refactor)

## Problem Statement (original)

Can moduli space theory be formalized in Mathlib to remove the 2 axioms?

## Refined target (S1 OBSERVE 2026-05-13)

The OQ targets the **2 axioms in `proofs/Proofs/MotivicFlagMaps.lean`**:

| # | Name (line) | Type |
|---|---|---|
| 1 | `motivicClassBasedMaps` (L309) | `(n : ℕ) (β : HomologyClass n) : K.carrier` — the moduli space class `[Ω²_β(Fl_{n+1})]` in K₀(Var). |
| 2 | `motivic_class_flag_maps` (L320) | `[Ω²_β(Fl_{n+1})] = [GL_n × A^a]` — BEMSV 2025 main theorem (arXiv:2601.07222). |

Two further axioms in `MotivicFlagMapsPartialFlags.lean` (`motivicClassPartialFlagMaps`, `partial_flag_extension`) are **out of scope**: the latter is a genuinely open conjecture, the former is the partial-flag analogue.

## Related Gallery Proofs

- `motivic-flag-maps`: parent (`axiomatized`, 4 axioms across 3 files, 0 sorries).
- `motivic-flag-maps-oq-03`: **active sibling thread** — established the `MotivicMeasure` structure-encoded pattern (PRs #18299, #18401, #18457, #18524, #18744).
- Mathlib: `GrothendieckGroup.lean` (only existing K₀-like primitive); no flag variety, moduli, or motivic infrastructure at pinned SHA.

## Sub-goal decomposition (see `state.md` for full details)

- **Sub-goal A** (TRACTABLE, ~30–60 LOC, low risk): Bundle the 2 axioms into a `BEMSVTheoremAxioms` structure. Architectural refactor; **does not reduce assumption count** (per CLAUDE.md Axiom Integrity Policy) but provides a cleaner interface aligned with the OQ-03 `MotivicMeasure` pattern. Recommended next step.

- **Sub-goal B** (HARDER, ~100–200 LOC + sorries): Replace axiom #2 with a weaker F_q-realization axiom. The K₀(Var) identity implies an exact F_q-point count for `Ω²_β(Fl_{n+1})(F_q)`, which is verifiable combinatorially for small `(n, β)` without moduli space theory.

- **Sub-goal C** (BLOCKED, multi-month): Build `K₀(Var)`, define flag varieties as schemes, and formalize BEMSV 2025. Requires ~10–20 KLOC of new Mathlib content.

## Mathlib bearer audit summary

At lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
- ✅ Basic scheme theory (`Mathlib/AlgebraicGeometry/*`).
- ✅ Generic Grothendieck-group construction (`Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean`).
- ❌ No `K₀(Var)`, no flag varieties as schemes, no moduli of stable maps, no Hilbert/Quot schemes, no motivic infrastructure.

## Suggested First Steps

1. Read parent `proofs/Proofs/MotivicFlagMaps.lean` to understand the 2 axioms and their downstream usage.
2. Review the OQ-03 `MotivicMeasure` pattern (`MotivicFlagMapsProvable.lean` if landed; otherwise PR #18744 diff).
3. For a single-session win: sub-goal A (~30–60 LOC refactor).
4. For sub-goal B: study the BEMSV cell-decomposition (Section 3 of arXiv:2601.07222) and combinatorial F_q count.

## Honesty note

Full removal of the 2 axioms is **blocked on Mathlib's lack of moduli space and K₀(Var) infrastructure**. This is a recognized blocker (already documented in the OQ-03 S1 OBSERVE). Single-session contributions are limited to:
- Doc-only PREPs and structural roadmaps (this S1 OBSERVE).
- Sub-goal A (architectural refactor — same assumption count, cleaner interface).
- Possibly sub-goal B starting with small `(n, β)` F_q-count proofs.
