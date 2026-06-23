# Knowledge Base: shannon-channel-coding-oq-04-oq-01

## Problem

Prove strict concavity of binary entropy h(p) = -p·log(p) - (1-p)·log(1-p) on (0,1).

## Session 2026-04-05 (Session 1)

**Outcome**: COMPLETE. Fully proved with 0 sorries, 0 axioms, 126 lines.

### What I Did

1. Identified `strictConcaveOn_of_deriv2_neg` as the key Mathlib API (in `Mathlib.Analysis.Convex.Deriv`)
2. Computed h'(p) = log(1-p) - log(p) via product rule on x·log(x) and chain rule on (1-x)·log(1-x)
3. Computed h''(p) = -1/(1-p) - 1/p using chain rule on each log term
4. Showed h''(p) < 0 by rewriting as -(1/(1-p) + 1/p) and using positivity
5. Applied `strictConcaveOn_of_deriv2_neg` with `EventuallyEq.deriv_eq` for the deriv^[2] computation
6. Fixed multiple Lean API issues through iterations:
   - `simp only [h]` → `unfold h` (h is a def, not a simp lemma)
   - `HasDerivAt.sub` type mismatch → `simpa [id, zero_sub]`
   - `linarith` atom mismatch for fractions → `ring` rewrite first
   - `id` not simplified in ContinuousOn proof → `simp only [id_eq]`
   - `deriv^[2]` simp leaving `id` → add `id_eq` to simp set
   - `open Topology` needed for `𝓝` notation
7. Proof builds cleanly with 0 errors, 0 warnings
8. Created gallery data: meta.json, annotations.json, index.ts

### Key Findings

- **strictConcaveOn_of_deriv2_neg** is the right API: `(hD: Convex ℝ D) (hf: ContinuousOn f D) (hf'': ∀ x ∈ interior D, deriv^[2] f x < 0) : StrictConcaveOn ℝ D f`
- **EventuallyEq.deriv_eq pattern**: Show `deriv h =ᶠ[𝓝 x] g` via `Filter.eventually_of_mem (Ioo_mem_nhds hx0 hx1)` + `HasDerivAt.deriv`, then use `HasDerivAt.deriv` for the second derivative
- **linarith and fractions**: linarith cannot link `1/(1-p)` and `-1/(1-p)` as atoms without help. Fix: use `ring` to rewrite `-1/(1-p) - 1/p = -(1/(1-p) + 1/p)`, then `linarith [add_pos h1 h2]`
- **simpa [id, zero_sub]** pattern: cleanly handles `HasDerivAt ((fun _ => 1) - id) (0-1) p` → `HasDerivAt (fun x => 1-x) (-1) p`
- **unfold h** needed instead of `simp only [h]` for noncomputable defs not marked @[simp]
- **id_eq in simp**: needed to reduce `id x` in the ContinuousOn nonvanishing condition and in deriv^[2] unfolding

### Files Modified

- `proofs/Proofs/ShannonChannelCodingOQ04OQ01.lean` (created, 126 lines, 0 sorries)
- `src/data/proofs/shannon-channel-coding-oq-04-oq-01/meta.json` (created)
- `src/data/proofs/shannon-channel-coding-oq-04-oq-01/annotations.json` (created)
- `src/data/proofs/shannon-channel-coding-oq-04-oq-01/index.ts` (created)

### Next Steps

- Extend to strict concavity of general entropy H(p₁,...,pₙ) = -∑ pᵢ·log(pᵢ) on the simplex
- Prove the maximizer h(1/2) = log 2 is unique, giving capacity of binary symmetric channel
