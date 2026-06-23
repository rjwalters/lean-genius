# Research State: roth-theorem-k3

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-03-22
**Iteration**: 1

## Current Focus
Roth's theorem: every subset of ZMod N with density ≥ δ contains a non-trivial
3-term arithmetic progression. COMPLETE — `proofs/Proofs/RothTheorem.lean` is
0 sorries / 0 axioms; registry status `graduated`; gallery meta `verified`,
badge `mathlib`.

## Resolution
The original plan (a hand-built Fourier-analytic density-increment argument, see
"History" below) was **superseded** by the reduction route that state.md had listed
as open Next-Action #3: `roth_density_bound` now discharges directly onto Mathlib's
`roth_3ap_theorem_nat` via the corners-theorem chain
(Regularity Lemma → Triangle Removal → Corners → Roth).

Final proof shape (`RothTheorem.lean:1372` `roth_density_bound`):
1. Map `A : Finset (ZMod N)` to `S = A.image ZMod.val ⊆ Finset.range N` (injective, density-preserving).
2. Bridge `APFree A → ThreeAPFree (S : Set ℕ)` via `apFree_imp_threeAPFree_val` (`:1337`).
3. Pick `N₀ = cornersTheoremBound (δ/3) + 1` and apply `roth_3ap_theorem_nat`.

The earlier Fourier infrastructure lemmas (`parseval_on_zmod`, `fourier_large_coefficient`,
`density_increment_lemma`, `density_iteration`) remain in the file as a self-contained
analytic development and are themselves sorry-free.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 2 (hand-built Fourier density increment; Mathlib corners-chain reduction — the latter closed it)

## Blockers
None. Proof complete and verified.

## Key Findings
- Mathlib's `roth_3ap_theorem_nat` (`Mathlib.Combinatorics.Additive.Roth`) + `cornersTheoremBound`
  (`...Additive.Corners`) close the ℕ-density form directly; no hand-built Fourier increment needed.
- The ZMod → ℕ bridge is the only nontrivial glue: `ZMod.val` injectivity preserves card and density,
  and `APFree` on `ZMod N` implies `ThreeAPFree` on the image in ℕ.
- Mathlib's `ZMod.dft`, `ZMod.stdAddChar`, `ThreeAPFree`, additive energy remain available for the
  companion / quantitative open questions (oq-01/02/03), which are tracked separately.

## Next Action
None — problem complete. Companion open questions (roth-theorem-k3-oq-01/02/03,
RothTheoremOQ02/OQ03/Quantitative.lean) carry the remaining sorries/axioms and are
tracked under their own slugs.

---

## History: original Active Approach (superseded)

Fourier-analytic density increment. Six-part proof structure:
1. AP-free definitions (COMPLETE)
2. AP counting via tripleCount (COMPLETE — proved APFree ↔ tripleCount = 0)
3. Fourier analysis infrastructure (norm bound, Parseval, AP-Fourier identity)
4. Large Fourier coefficient
5. Density increment lemma (with APFree B in conclusion)
6. Iteration + main theorem

All six parts are now sorry-free in `RothTheorem.lean`; the main theorem was ultimately
closed by the Mathlib corners-chain reduction rather than by chaining the density increment.
