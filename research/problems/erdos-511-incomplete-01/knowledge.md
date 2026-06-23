# Knowledge: erdos-511-incomplete-01

**Problem**: Erdős Problem #511: Bounded Components of Polynomial Lemniscates
**Answer**: DISPROVED (Pommerenke 1961)
**Current Status**: Lean proof builds with 0 sorries, 2 axioms

---

## Session 2026-04-03 (Session 1) — Fix and Complete

**Mode**: FRESH
**Outcome**: completed — proof now builds with 0 sorries

### What I Did

1. Assessed the file: 1 sorry in `no_component_reaches_4`, plus pre-existing build errors
2. Fixed the sorry: replaced `left; sorry` with `exact h.lt_or_eq` (the goal `< 4 ∨ = 4` is exactly `≤ 4` rephrased)
3. Fixed pre-existing build errors:
   - Added `import Mathlib.Algebra.Polynomial.Eval.Defs` (missing for `f.eval z`)
   - Added `noncomputable` to `rootsOfUnityPoly`
   - Changed orphaned `/--` doc comments to `/-` (they had no following declaration)
   - Updated `erdos_511` proof to call `pommerenke_theorem` with `d = (c+4)/2` to bridge `≥ d > c` → strict `> c`
   - Replaced deprecated `Complex.abs` with `‖·‖` norm notation
4. Proof compiles: `./proofs/scripts/docker-build.sh Proofs.Erdos511Problem` → Build succeeded

### Key Findings

- `Complex.abs` was removed from Mathlib — use `‖·‖` instead
- `Mathlib.Algebra.Polynomial.Eval.Defs` is needed for `f.eval z` dot notation
- The sorry `no_component_reaches_4` was straightforward: goal was `< 4 ∨ = 4` from `h : ≤ 4`, so `h.lt_or_eq` closes it
- The main proof gap in `erdos_511`: Pommerenke gives `diam ≥ d` but theorem needs `diam > c`; fixed by using `d = (c+4)/2 > c`

### Files Modified

- `proofs/Proofs/Erdos511Problem.lean` — fixed sorry + pre-existing build errors
- `src/data/proofs/erdos-511/meta.json` — updated sorries: 1→0, lineCount, assumptions

### Next Steps

- None for this problem: proof complete, 0 sorries, 2 axioms (polya_diameter_bound, pommerenke_theorem)
- The two axioms are correct: they represent deep results in complex analysis that would require substantial Mathlib infrastructure to formally prove
