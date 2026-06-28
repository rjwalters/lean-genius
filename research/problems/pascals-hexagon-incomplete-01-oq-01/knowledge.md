# pascals-hexagon-incomplete-01-oq-01

**Goal:** Discharge the remaining `sorry` `sylvester_stdConic_of_isotropic` in
`proofs/Proofs/PascalsHexagon.lean` — a non-degenerate symmetric real conic carrying a
real point is projectively equivalent to `stdConic = diag(1,1,-1)`. This is the sole gap
on the `proof_sketch_conic_implies_pascal` path (Pascal's theorem for general symmetric
non-degenerate conics).

## Summary of state
- The theorem statement is TRUE (Sylvester's law of inertia; the real-point hypothesis is
  essential and rules out the definite case).
- As of session 2026-06-28 the proof is **reduced** to a single clean linear-algebra core
  lemma; the projective-geometry wrapper is fully machine-checked (0-axiom).

## Session 2026-06-28 (researcher-8, Session 1) — REDUCTION + verified infrastructure

**Mode:** FRESH | **Outcome:** progress (1 sorry → 1 sorry, but isolated + 2 new verified lemmas)

### What I did
- Aristotle was unreachable this session ("Resource not found" on every call incl. a trivial
  ping), so all work was manual.
- Added two fully-verified (`propext`/`Classical.choice`/`Quot.sound` only) lemmas:
  - `conicQF_projTransform (S M p) : conicQuadraticForm S (M·p) = conicQuadraticForm (Mᵀ*S*M) p`
    — the matrix-congruence identity `(Mp)ᵀ S (Mp) = pᵀ(MᵀSM)p`. Proof chases
    `mulVec_mulVec` / `dotProduct_mulVec` / `vecMul_transpose`.
  - `pointOnConic_projTransform_iff_of_congr (C M c hc hcong p)` : if `Mᵀ*stdConic*M = c•C`
    with `c ≠ 0` then `pointOnConic p C ↔ pointOnConic (M·p) stdConic`. This is the
    *structural heart* of projective equivalence of conics.
- Reproved `sylvester_stdConic_of_isotropic` so its body is now `sorry`-free: it `obtain`s
  the congruence witness from the new core lemma and applies
  `pointOnConic_projTransform_iff_of_congr`.
- Isolated the single remaining `sorry` into a new, sharper, purely matrix-algebraic core
  lemma `exists_scaledCongr_stdConic_of_isotropic`:
  `∃ M, M.det ≠ 0 ∧ ∃ c ≠ 0, Mᵀ * stdConic * M = c • C`.

### Key findings
- The scalar `c` (signature ±1) is genuinely needed: Sylvester gives congruence to
  `±stdConic`, and `-stdConic` has the same zero locus, so the `iff` is preserved.
- Validated against the live Mathlib 4.26 API:
  `QuadraticForm.equivalent_one_neg_one_weighted_sum_squared (Matrix.toQuadraticMap' C) hsep`
  applies (hypothesis discharged by the pre-existing `mathlibQF_separatingLeft`), returning
  `w : Fin (Module.finrank ℝ (Fin 3 → ℝ)) → ℝ` with `w i = ±1` + an `IsometryEquiv`.
- **Main remaining obstacle** (documented in the core lemma's docstring): turning the abstract
  `IsometryEquiv` into a *matrix* congruence `C = Lᵀ * diagonal w * L` requires the
  `Fin (Module.finrank ℝ (Fin 3 → ℝ)) ↔ Fin 3` cast (`Module.finrank_fin_fun`/`finrank_pi`).
- Remaining sub-steps after the cast are elementary: (a) real point ⟹ `w` indefinite
  (definite forms vanish only at 0); (b) indefinite ±1 weights ⟹ permutation/sign matrix `P`
  with `Pᵀ * diagonal w * P = ±stdConic`.

### Files modified
- `proofs/Proofs/PascalsHexagon.lean` (verified, 1 sorry, all on host `lake env lean` exit 0)

### Next steps
1. Prove the permutation/sign correction as its own verified lemma (elementary, 6 cases /
   `Equiv.Perm` conjugation of `diagonal`) — cuts the core to just the Sylvester+cast step.
2. Prove the matrix-congruence extraction from `IsometryEquiv` + finrank cast — the hard part;
   ideal Aristotle target once the service is reachable again (submit
   `exists_scaledCongr_stdConic_of_isotropic`).
