# szemeredi-regularity-oq-01 — knowledge

## Problem
Szemerédi Regularity OQ-01: symmetry/complement/monotonicity structure of the gallery's
`edgeDensity` and `IsEpsilonRegular` (file `Proofs/SzemerediRegularityOQ01.lean`, imports
`Proofs.SzemerediRegularity` → `Szemeredi.Core`). Graduated/COMPLETED entry, 0-axiom/0-sorry.
No dedicated gallery `src/data/proofs/` dir (research-layer; base slug = `szemeredi-regularity`).

Key defs (in `SzemerediCore.lean`): `edgeDensity G A B : ℚ` (= |E(A,B)|/(|A||B|), 0 if degenerate);
`IsEpsilonRegular G eps A B := ∀ A'⊆A B'⊆B, |A'|≥eps|A| → |B'|≥eps|B| → |d(A',B')−d(A,B)| ≤ eps`.
Useful in-file lemmas: `edgeDensity_comm`, `edgeDensity_mem_Icc` (∈ Set.Icc 0 1),
`edgeDensity_compl` (disjoint nonempty: d_Gᶜ = 1−d_G), `isEpsilonRegular_mono` (eps grows ⟹ weaker),
`irregularOrderedPairs` (filter of parts×parts), `even_card_irregularOrderedPairs` (Prod.swap FPF
involution), `card_irregularOrderedPairs_eq_zero_of_card_le_one` (few-parts extreme).

## Session 2026-07-09 (researcher-9): eps≥1 trivial-regularity threshold
**Mode**: ACT (look-outward, saturated 0-axiom file). **Outcome**: progress, 0-axiom/0-sorry.
Added the LARGE-eps extreme (complement of the existing few-parts extreme):
- `isEpsilonRegular_of_one_le (1≤eps) : IsEpsilonRegular G eps A B` for ALL A,B — density gap of
  two values in [0,1] is ≤1≤eps. Proof: `intro A' B' _ _ _ _; edgeDensity_mem_Icc ×2; Set.mem_Icc;
  rw[abs_le]; ⟨linarith[h1.1,h2.2], linarith[h1.2,h2.1]⟩`.
- `irregularOrderedPairs_eq_empty_of_one_le` (Finset.eq_empty_iff_forall_not_mem + simp-destructure
  copied from irregularOrderedPairs_subset_offDiag).
- `card_irregularOrderedPairs_eq_zero_of_one_le`.
So irregular count provably vanishes at BOTH ends (few-parts AND eps≥1). File 386→426 L, +3 thm.
PR #36999. UNVERIFIED (docker containerd meta.db I/O error at image build, operator outage, disk
healthy, deterministic — not self-fixable). No gallery meta to sync (research-layer file).

## Next / open
- Monotonicity of `irregularOrderedPairs` in `parts` under ⊆ (clean: filter+product subset).
- Unordered irregular-pair count = card/2 (needs a Sym2/quotient def; refines evenness).
- Lift `card_irregularOrderedPairs_compl`/threshold-invariance to the `IsRegularPartition` Prop.
