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
