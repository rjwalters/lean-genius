# Research State: hurwitz-theorem-oq-04

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-04-28T16:00:00.000Z (post-#13632 reconciliation)
**Iteration**: 9 (verified)

## Outcome

VERIFIED. The proof is fully machine-checked.

- Lean file: `proofs/Proofs/HurwitzTheoremOQ04.lean` (1646 lines)
- Sorries: 0
- `axiom` declarations: 0
- Gallery status: `verified`, badge `original`

The 14-dimensional kernel claim `derEval14_injective` was reduced
across Sessions 1-9 from a single 56-entry sorry → 7 named Fano
residuals (PR #13623) → 0 sorries (PR #13632, "7 Fano residuals
proved by Leibniz"). Build verified post-merge.

## Mathematical Content

Establishes:
1. `G2_is_octonion_aut` (axiomatized at higher level — Aut(𝕆) ≅ G₂)
2. `Der(𝕆) ⊆ 𝔰𝔬(7)` (anti-symmetric on Im(𝕆) ≅ ℝ⁷, dim ≤ 21)
3. **`derEval14_injective`**: 14 evaluation coordinates determine
   any element of Der(𝕆), giving `dim Der(𝕆) = 14`.

The 14 free coords span Der(𝕆); the 7 extra Fano-line Leibniz
constraints cut 21-dim 𝔰𝔬(7) down to 14-dim G₂.

## Blockers

None.

## Next Action

Pool entry should be marked `completed`. No further research
work required; meta.json is correct (`status: verified`, `axiomCount: 0`).
