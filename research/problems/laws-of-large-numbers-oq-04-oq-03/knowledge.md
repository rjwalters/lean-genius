# laws-of-large-numbers-oq-04-oq-03: Glivenko-Cantelli Integration Axioms

**Problem**: Prove the two integration axioms left open in the Glivenko-Cantelli
formalization (LawsOfLargeNumbersOQ04.lean):
  1. `thresholdIndicator_integrable`: 1_{Xᵢ ≤ x} is integrable on probability spaces
  2. `integral_thresholdIndicator_eq_cdf`: E[1_{X₀ ≤ x}] = F(x)

**Status**: COMPLETE — PR #16099, 0 sorries, 0 axioms

---

## Session 2026-05-06 (Session 1) — Complete Formalization

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Claimed problem, created branch `feature/researcher-4-lln-glivenko-indicator-axioms`
2. Read `LawsOfLargeNumbersOQ04.lean` — identified 3 axioms, 2 provable
3. Proved Axiom 1 (integrability) via `Integrable.mono'` with constant bound
4. Proved Axiom 2 (integral = CDF) via preimage rewrite + `integral_indicator` + `integral_const`
5. Created gallery entry and committed

### Key Findings

- Axiom 1: `Integrable.mono'` with `integrable_const 1` as bound — indicator takes values 0/1
- Axiom 2: Three-step chain: `thresholdIndicator_eq_preimage_indicator_fun` → `integral_indicator` → `integral_const` + `Measure.restrict_apply`
- Axiom 3 (`glivenko_cantelli_uniform`) genuinely hard: needs CDF continuity point density argument not in Mathlib 4.26

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03.lean` (new, 128 lines)
- `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/meta.json` (new)
- `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/annotations.json` (new)
- `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/index.ts` (new)
- `src/data/proofs/listings.json` (updated)

### Next Steps

- Docker build verification pending
- Glivenko-Cantelli axiom 3 (uniform bracketing) remains open — would need CDF continuity point infrastructure

---

## Session 2026-05-08 (Session 2) — Bracketing Decomposition Specification

**Mode**: REVISIT
**Outcome**: surveyed (pre-formalization specification)
**Researcher**: researcher-9

### What I Did

Produced `bracketing-decomposition-draft.md` — a pre-formalization specification
that decomposes the remaining `glivenko_cantelli_uniform` axiom into three named
pieces and identifies the precise Mathlib gap.

### Key Findings

The classical bracketing argument decomposes orthogonally as:

1. **Grid existence** — analytic, on `F`. For ε > 0, finitely many continuity
   points `q₀ < ⋯ < q_{k+1}` of `F` cover `[0,1]` with F-jump ≤ ε per cell.
   **This is the only piece missing from Mathlib 4.26**: the constructive
   ε-cover induction using `Monotone.countable_setOf_not_continuousAt`.
2. **Simultaneous pointwise convergence** — provable from
   `MeasureTheory.ae_all_iff` + the parent file's
   `empiricalCDF_pointwise_convergence`. ~10–20 lines.
3. **Uniform sup-bound from grid** — deterministic monotone interpolation.
   Provable from the parent's `empiricalCDF_mono` and `trueCDF_mono`. ~50
   lines (case-split on x-position relative to grid; both ends + middle).

Out of ten Mathlib lemmas needed by the decomposition, **nine are already in
Mathlib 4.26**. The tenth is a single proposed
`Monotone.exists_increasing_continuity_seq` lemma that is purely
real-analytic (no probability) and is the natural Mathlib home for the
bracketing scaffolding.

### Lean Targets (Pre-Formalization Signatures)

- `BracketingGrid (F : ℝ → ℝ) (ε : ℝ)` — structure with `k`,
  `q : Fin (k+2) → ℝ`, `mono`, `cont`, `step_le`, `left_le`, `right_ge`.
- `axiom bracketingGrid_exists` (only axiom in target file).
- `theorem bracketing_simultaneous_pointwise` — finite intersection.
- `theorem bracketing_uniform_from_grid` — deterministic sup-bound.
- `theorem glivenko_cantelli_uniform_proved` — composition (§2.5), reduces
  to single axiom + countable-intersection `ae_iInter_iff` along
  ε = 1/(m+1).

### Files Modified

- `research/problems/laws-of-large-numbers-oq-04-oq-03/bracketing-decomposition-draft.md` (new, ~370 lines)
- `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md` (updated — this entry)

### Next Steps

1. **Promote draft to Lean**. Create
   `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` per §6
   checklist. ~150 lines total. Build pending; expect a 45-min cold build
   due to broken `proofs/.lake` symlink.
2. **Mathlib upstream PR**. After §2.3 + §2.4 + §2.5 are proved in Lean,
   draft a Mathlib PR for `Monotone.exists_increasing_continuity_seq`.
3. **VC-class generalisation**. Once classical GC is axiom-free, the
   decomposition's §2.2 generalises to a VC-class symmetrization /
   Sauer–Shelah argument. Independent of §2.4. See
   `bracketing-decomposition-draft.md` §4.

### Honesty

This session produced **specification only**, no compiled Lean code. The
gallery entry's `verified`/0-axioms status is unchanged. The Lean signatures
in the draft have been hand-checked against the parent file's namespacing
but not run through the elaborator. Nothing in this session reduces axiom
counts or eliminates sorries; the contribution is a clear roadmap that
isolates the Mathlib gap for the next session.


---

## Session 2026-05-08 (Session 4) — §2.3 bracketing_simultaneous_pointwise

**Mode**: REVISIT
**Outcome**: progress (one of three remaining bracketing theorems landed)
**Researcher**: researcher-4

### What I Did

Filled in §2.3 of `bracketing-decomposition-draft.md`:
`bracketing_simultaneous_pointwise`. Added to
`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (the companion file
S3 introduced).

### Key Findings

- `MeasureTheory.ae_all_iff` is the right tool for "simultaneous a.s.
  convergence at finitely many points": one rewrite reduces the universally
  quantified a.s. statement to a per-point a.s. statement, which the parent
  file already proves.
- `Fin (k + 2)` has `Countable` automatically (since finite types are
  countable in Mathlib), so no extra hypothesis on `ι` is needed.
- The 3-line proof matches the spec sketch verbatim — no surprise.

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`: 120 → 147 lines,
  +1 theorem (`bracketing_simultaneous_pointwise`).
- `research/problems/laws-of-large-numbers-oq-04-oq-03/state.md`: S4 entry.
- `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md`: this entry.

### Counts Delta

- `meta.json` (main file `LawsOfLargeNumbersOQ04OQ03.lean`): unchanged
  (still `verified`, 0 sorries, 0 axioms, 158 lines, 4 theorems).
- Bracketing companion: lineCount 120 → 147; theoremCount 0 → 1; axioms,
  sorries unchanged.

### Next Steps

- §2.4 (`bracketing_uniform_from_grid`): deterministic case-split using
  parent's `empiricalCDF_mono` / `trueCDF_mono`. ~50 lines, the longest of
  the three.
- §2.5 (`glivenko_cantelli_uniform_proved`): composition of §2.2 + §2.3 + §2.4
  via countable union of null sets along ε = 1/m. ~20 lines.
- Once §2.5 lands, retire the parent's `glivenko_cantelli_uniform` axiom.
- Future Mathlib upstream: `Monotone.exists_increasing_continuity_seq` to
  discharge `bracketingGrid_exists`.
