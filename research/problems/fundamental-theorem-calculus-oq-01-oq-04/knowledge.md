# fundamental-theorem-calculus-oq-01-oq-04

**Problem**: Should AbsolutelyContinuousOn be generalized to functions between normed spaces?

**Answer**: YES — define `AbsolutelyContinuousOnNormed` using ‖·‖, prove AC_Normed → BV.

---

## Session 2026-05-05 (Session 1) — COMPLETED

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms, 7 theorems)

### What I Did
- Surveyed parent file `FundamentalTheoremCalculusLebesgueOQ01.lean` (AC → BV for ℝ → ℝ)
- Defined `AbsolutelyContinuousOnNormed f a b` for `f : ℝ → E` (NormedAddCommGroup E)
- Key insight: replace `|f(b) - f(a)|` with `‖f(b) - f(a)‖` throughout
- Proved 7 theorems mirroring the real-valued theory:
  1. `const_normed_ac` — constant functions are normed-AC
  2. `lipschitz_implies_normed_ac` — Lipschitz → normed-AC
  3. `normed_ac_implies_real_ac` — E=ℝ specialization gives original AC
  4. `real_ac_implies_normed_ac` — original AC gives normed-AC at E=ℝ
  5. `real_ac_iff_normed_ac` — equivalence at E=ℝ
  6. `normed_ac_mono_subinterval` — restriction to subintervals
  7. `normed_ac_implies_bv` — main theorem: AC_Normed → BV
- Key: `edist x y = ENNReal.ofReal ‖x - y‖` (via `edist_dist` + `dist_norm`)
- Disjointness proof for partition: uses `Nat.succ_le_of_lt` (not `h.le`) for correct indexing
- Created gallery entry `src/data/proofs/fundamental-theorem-calculus-oq-01-oq-04/meta.json`
- Docker build submitted; PR creation pending

### Key Findings
- `eVariationOn` and `BoundedVariationOn` already work for `f : ℝ → E` (any PseudoEMetricSpace)
- `edist_dist` + `dist_norm` give `edist x y = ENNReal.ofReal ‖x - y‖` for normed groups
- The partition proof from OQ01 carries over identically; only the "edist = ofReal ‖·‖" lemma changes
- Disjointness for monotone partition: need `hu_mono (Nat.succ_le_of_lt h)` not `hu_mono h.le`

### Files Modified
- `proofs/Proofs/FundamentalTheoremCalculusLebesgueOQ04.lean` (new, 253 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/fundamental-theorem-calculus-oq-01-oq-04/meta.json` (new)
- `src/data/proofs/fundamental-theorem-calculus-oq-01-oq-04/index.ts` (new)

### Next Steps
- Docker build verification
- If passes: commit, push, create PR
- Follow-up OQ-01: does normed-AC imply Fréchet differentiability a.e.?
- Follow-up OQ-02: Jordan decomposition for normed-valued BV functions
