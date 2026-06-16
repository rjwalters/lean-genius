# Research State: cauchy-interlacing-theorem

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-16T00:32:21-07:00
**Iteration**: 7

## Current Focus
Keystone (Courant–Fischer k-th max–min) integration. Sublemmas A & B are PROVEN
on main (`CauchyInterlacingSublemmas.lean`, PR #24939, 0 sorry/0 axiom). The open
PR #24796 (`CauchyInterlacingMinMax.lean`) has the keystone scaffold with 2 sorries
+ a mis-stated keystone identity.

## Active Approach
Wire the merged Sublemma A (`rayleigh_bounds_on_eigenspan`) into the keystone via
`hT.eigenvectorBasis`/`hT.eigenvalues`/`hT.apply_eigenvectorBasis`, and prove the
keystone directly over `hT.eigenvalues`. **CORRECTION (s07, researcher-8 2026-06-16):**
the earlier "`eigenvalues` is unsorted → restate over `sortedEigs`" plan is a red
herring and is RETRACTED — `LinearMap.IsSymmetric.eigenvalues_antitone`
(`Mathlib/Analysis/InnerProductSpace/Spectrum.lean:254`,
`Antitone (hT.eigenvalues hn)`) proves `hT.eigenvalues` is already descending-sorted.
Use it directly for the ordering; do NOT introduce a custom `sortedEigs`. (This also
matches #24796 iter-3, which already retracted the unsorted claim, and #24977 s07.)

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Dual backend blackout (s06): Aristotle 404; Docker saturated at 10 lean-build
  containers / 3 GiB free → build would OOM peers. No verification this session.
- `proofs/.lake` corrupt self-symlink → no local Mathlib grep.

## Next Action
When a backend opens (Aristotle non-404, or Docker ≤2 containers):
1. Apply the turnkey glue (knowledge.md s06 #1) to discharge
   `rayleigh_mem_Icc_of_mem_eigenspan` from the merged `rayleigh_bounds_on_eigenspan`.
2. State the keystone directly over `hT.eigenvalues` and invoke
   `eigenvalues_antitone` (Spectrum.lean:254) wherever descending order is used —
   NO `sortedEigs` restatement (supersedes the retracted s06 #2). The genuine
   remaining gap is the k-th Courant–Fischer min-max, absent from Mathlib.
3. Prove both halves with the span-witness (≥) and Sublemma-B pigeonhole (≤);
   pin down `finrank (span (b''I)) = I.card` for the orthonormal subfamily.
