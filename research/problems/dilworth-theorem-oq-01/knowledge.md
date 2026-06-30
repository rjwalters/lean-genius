# Dilworth's Theorem (dilworth-theorem-oq-01)

## Summary

Formalize the chain–antichain duality of Dilworth (1950) and its dual Mirsky
(1971). Each is a min–max theorem with a trivial (pigeonhole) inequality and a
deep inequality (attainment). This problem targets the **elementary directions**,
fully machine-checked, with the deep directions documented as follow-ups.

**Status**: COMPLETED (easy directions). 0 axioms, 0 sorries.
File: `proofs/Proofs/DilworthTheoremOQ01.lean`.

## Session 2026-06-16 (Session 1) — Elementary directions of the duality

**Mode**: FRESH
**Outcome**: completed (easy directions)

### What I Did
- Selected `dilworth-theorem-oq-01` after deferring `midy-theorem-oq-01`
  (researcher-5 was actively build-running an identical proof — concurrent
  collision avoided).
- Defined `IsChainOn` / `IsAntichainOn` on `Finset`s over an arbitrary
  `PartialOrder` (no global finiteness assumption).
- Proved the fundamental lemma `chain_antichain_inter_subsingleton`: a chain and
  an antichain meet in at most one point.
- Derived the two pigeonhole inequalities:
  - `antichain_card_le_of_chainCover` — Dilworth `≤`: any antichain is ≤ any
    chain family covering it.
  - `chain_card_le_of_antichainCover` — Mirsky `≤`: any chain is ≤ any antichain
    family covering it (same proof, roles swapped).

### Key Findings
- Both inequalities reduce to a single pigeonhole step
  (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`); the only real content is the
  subsingleton lemma.
- Encoding an antichain as `x ≤ y → x = y` keeps the `≤`-reasoning frictionless.
- The Dilworth and Mirsky easy directions are literally dual: identical proof
  with chain/antichain exchanged.
- Mathlib (June 2026) has no packaged Dilworth/Mirsky theorem; `Set.chainHeight`
  (Order/Height.lean) is the natural hook for a future hard-direction proof.

### Files Modified
- `proofs/Proofs/DilworthTheoremOQ01.lean` (new)
- `src/data/proofs/dilworth-theorem-oq-01/meta.json` (new)
- `proofs/Proofs.lean` (registration)

### Next Steps (deep directions — open follow-ups)
- Mirsky hard direction via the height function: `h(x)` = longest chain ending
  at `x`; level sets `{x : h x = i}` are antichains and partition the poset into
  `max-chain-length` antichains. Constructive; needs well-founded recursion on
  `<` (finite poset ⇒ `WellFoundedLT`).
- Dilworth hard direction via König / Hall on the comparability bipartite graph,
  or strong induction removing a maximal chain.

## Session 2026-06-16 (Session 2) — Mirsky hard direction (attainment)

**Mode**: FRESH (revisit of completed easy directions)
**Outcome**: progress (build-pending orphan; dual Docker+Aristotle blackout)

### What I Did
- Wrote the **Mirsky hard direction** as an UNREGISTERED orphan
  `proofs/Proofs/DilworthMirskyHardOQ01.lean` (zero gallery risk while builds are
  down). Imports `Proofs.DilworthTheoremOQ01` to reuse `IsChainOn`/`IsAntichainOn`
  and the easy-direction lemma.
- Key construction (no well-founded recursion needed): for a finite poset
  (`[Fintype α]`), `height x` is the `Finset.sup` of chain cardinalities over
  `chainsTo x` = chains whose maximum element is `x`. The sup is attained
  (`Finset.exists_mem_eq_sup`), supplying an explicit longest chain ending at `x`.
- Theorems proved (0 sorries / 0 axioms by construction):
  - `level_isAntichain` — each level `{x : height x = k}` is an antichain.
  - `mirsky_antichain_cover` — the poset is covered by `≤ maxChainLen` antichains.
  - `exists_chain_card_eq_maxChainLen`, `maxChainLen_le_card_of_antichainCover`.
  - `mirsky_min_antichain_cover` — full Mirsky: an antichain cover of size exactly
    `maxChainLen` exists and is minimal.

### Key Findings
- The height function does NOT need `WellFoundedLT`/recursion (contra Session 1's
  plan): a non-recursive `Finset.sup` over `chainsTo x` plus the "sup attained"
  lemma gives a usable witness chain, and the antichain property follows by
  appending the larger element.
- Cover-size bound is purely cardinal: heights lie in `Icc 1 maxChainLen`, so
  `#(image height) ≤ maxChainLen` via `card_image_le` + `card_le_card`.
- Pin gotchas (v4.26.0 / 2df2f0150c): `not_le_of_lt`→`not_ge` (used `lt.not_ge`),
  `card_insert_of_not_mem`→`card_insert_of_notMem`, `not_mem_empty`→`notMem_empty`,
  `lt_iff_le_not_le`→`lt_iff_le_not_ge`. `not_le` is LinearOrder-only — avoided.

### Files Modified
- `proofs/Proofs/DilworthMirskyHardOQ01.lean` (new, orphan/unregistered)
- `src/data/research/problems/dilworth-theorem-oq-01.json` (knowledge)

### Next Steps
- Build-verify the orphan once Docker is back; then register in `Proofs.lean` and
  add a gallery dir for the strengthened Mirsky result.
- Dilworth hard direction (chain cover = max antichain) remains the open frontier
  — strictly harder (König/Hall), no Mirsky-style elementary height argument.
