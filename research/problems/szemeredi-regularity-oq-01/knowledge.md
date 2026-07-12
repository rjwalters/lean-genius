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

## Session 2026-07-11 (researcher-5): lift to the gallery `IsRegularPartition` Prop
**Mode**: ACT (look-outward, saturated 0-axiom file). **Outcome**: progress, 0-axiom/0-sorry.
Closed the "lift threshold-invariance to `IsRegularPartition`" gap. `IsRegularPartition`
(in `SzemerediCore.lean`) = equitable-sizes ∧ `(filter …).card ≤ eps·k(k−1)`, and that filter
is DEFEQ to `irregularOrderedPairs`. Added:
- `irregularOrderedPairs_eq_regularityFilter` (`:= rfl`) — the count set thresholded by
  `IsRegularPartition` *is* `irregularOrderedPairs`.
- `isRegularPartition_iff` (`Iff.rfl`) — restates the gallery Prop in this file's vocabulary
  (equitable ∧ `(irregularOrderedPairs …).card ≤ eps·k(k−1)`).
- `isRegularPartition_compl` — **marquee**: `IsRegularPartition Gᶜ eps parts ↔ IsRegularPartition G eps parts`
  for `0<eps` + pairwise-disjoint nonempty parts. Proof: `rw [isRegularPartition_iff ×2,
  card_irregularOrderedPairs_compl …]` (equitable clause is G-free, count clause via compl-invariance).
- `isRegularPartition_of_one_le` — at `eps≥1` the only content is equitability (irregular count=0,
  bound `eps·k(k−1)≥0` via `mul_nonneg` + `nlinarith` on `1≤k`).
File 470→550 L, 25→29 thm. PR #TBD. VERIFIED (docker build succeeded, 0-axiom/0-sorry).
★GOTCHA: mathlib cache had a corrupt `Mathlib/Topology/Constructible.ir` (olean header, dated
07-09, pre-existing) → SIGBUS (exit 135) then "invalid header"; `rm` the stray `.ir` → cache re-fetch fixed it.

## Next / open
- Unordered irregular-pair count = card/2 (needs a Sym2/quotient def; refines evenness).
- `partitionEnergy` (defined in Core) monotonicity under refinement — untouched by this file.

## Session 2026-07-11 (researcher-1) — SURVEY: saturated; pinned next increment, no PR

Re-examined `SzemerediRegularityOQ01.lean` (550L, 29 thm, 0-axiom/0-sorry). Confirms saturation:
commutativity, complementation (`edgeDensity_compl`/`isEpsilonRegular_compl`/`_compl` count),
parameter- and part-monotonicity, empty/eps≥1 extremes, evenness of the ordered irregular count
(`even_card_irregularOrderedPairs` via the reusable `even_card_of_fpf_involution`), and the lift to
the gallery `IsRegularPartition` Prop are all present. No clean non-cosmetic single-lemma gap.

**Precise next increment (for a future session with a stable build cache):** upgrade
`even_card_irregularOrderedPairs` (currently only `Even card`) to the EXACT
`(irregularOrderedPairs G eps parts).card = 2 * u`, where `u` counts UNORDERED irregular pairs.
Two viable routes: (a) define `irregularUnorderedPairs : Finset (Sym2 (Finset V))` as the
`Sym2.mk`-image and prove `card_image` halving via the fixed-point-free `Prod.swap` involution;
(b) add a general `Finset` lemma `card = 2 * (orbit-reps).card` for a fpf involution (strengthening
`even_card_of_fpf_involution`) — the cleaner, reusable option, but needs an orbit-representative
selection (decidable rep predicate) that Mathlib doesn't provide off the shelf. Est. 40–80 L.

NOT done this session: the build cache was intermittently corrupting under concurrent fleet load
(SIGBUS/135, `invalid header`), making iterative verification of a fiddly Sym2 proof unreliable;
deferred rather than ship UNVERIFIED. The larger `partitionEnergy` monotonicity-under-refinement
(the energy-increment core, defined in `SzemerediCore.lean`) remains the substantive open direction.
Released claim (honest no-op PR-wise).
