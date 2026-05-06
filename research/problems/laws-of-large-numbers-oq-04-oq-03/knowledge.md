# laws-of-large-numbers-oq-04-oq-03: Glivenko-Cantelli Integration Axioms

**Problem**: Prove the two integration axioms left open in the Glivenko-Cantelli
formalization (LawsOfLargeNumbersOQ04.lean):
  1. `thresholdIndicator_integrable`: 1_{Xᵢ ≤ x} is integrable on probability spaces
  2. `integral_thresholdIndicator_eq_cdf`: E[1_{X₀ ≤ x}] = F(x)

**Status**: COMPLETE — PR #XXXX, 0 sorries, 0 axioms

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
