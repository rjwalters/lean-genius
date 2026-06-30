# algebraic-reals-meager-oq-02 — Knowledge Base

## Problem

Quantify the comeagre transcendental complement as an explicit dense Gδ set, and
relate comeagreness (category) to conullness (measure).

## Status

**RESOLVED — verified, 0 axioms, 0 sorries.**

## Resolution (cross-file)

The two halves of OQ-02 are fully formalized:

### 1. The transcendentals are an explicit dense Gδ (the literal ask)
File: `proofs/Proofs/AlgebraicRealsMeagerDenseGDelta.lean`
- `isGδ_compl_of_countable` / `dense_compl_of_countable` / `isGδ_dense_compl_of_countable`
  — general: in a perfect T1 space the complement of a countable set is a dense Gδ.
- `transcendentalReals_isGδ`, `transcendentalReals_dense_isGδ` — the transcendental
  reals `{x : ℝ | ¬ IsAlgebraic ℚ x}` *are* a dense Gδ (not merely "contain one"), as
  `⋂ a, {a}ᶜ` over the countable algebraic reals — mirroring Mathlib's `IsGδ.setOf_irrational`.
- `transcendentalReals_residual_of_dense_Gδ` — hence residual (comeagre).
- `algebraicReals_not_isGδ` — sharp dual: the algebraic reals are NOT Gδ (a dense
  meagre set in a Baire space cannot be Gδ).

### 2. Category vs measure (the contrast)
File: `proofs/Proofs/AlgebraicRealsMeagerOQ02.lean`
- `algebraicReals_null` — algebraic reals are Lebesgue-null (measure counterpart of meagre).
- `ae_transcendental` — a.e. real is transcendental (transcendentals conull).
- `liouville_residual` / `liouville_dense` / `liouville_null` — Liouville numbers are a
  dense comeagre set of measure zero.
- `exists_residual_dense_null` — **comeagre ⇏ conull**: ∃ dense comeagre null set.
- `residual_ae_disjoint` — `Disjoint (residual ℝ) (ae volume)`: the two σ-ideals are orthogonal.

## Verification

Both files compile under `lake env lean` (mathlib 4.26.0). `#print axioms` on the
transcendental-Gδ theorems shows only propext / Classical.choice / Quot.sound — no
`native_decide`, no `Lean.ofReduceBool`, no `sorryAx`.

## Sessions

### Session 2026-06-25 (researcher-5)
Claimed `algebraic-reals-meager-oq-02` (fresh, knowledge score 0). Investigation found
the problem is **already fully resolved and verified** across the two files above; the
seeker had re-minted it because the `research/problems/algebraic-reals-meager-oq-02`
directory was missing (only `oq-01` existed). Per the project's credibility policy
(no fabricated/redundant theorems), this session records the resolution and adds the
missing problem directory so the problem is no longer re-selected as fresh. Confirmed
both Lean files still build cleanly offline.
