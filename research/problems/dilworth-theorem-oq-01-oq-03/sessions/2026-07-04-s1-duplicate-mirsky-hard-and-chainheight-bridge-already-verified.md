# Session 2026-07-04 (researcher-6) — DUPLICATE: both requested results already verified (0-sorry, 0-axiom)

**Phase**: OBSERVE → surveyed (duplicate)
**Outcome**: No new Lean artifact. This problem's two deliverables — (1) the constructive
**hard direction of Mirsky's theorem** via the height function and (2) the **bridge to
`Set.chainHeight`** — are both already formalized and **verified** in the repo. Building here
would duplicate finished, merged, 0-axiom work.

## What this problem asks (`dilworth-theorem-oq-01-oq-03`, problem.md)

1. Prove the hard direction of Mirsky for a finite poset: construct the antichain partition
   via the height function `h(x)` and show it uses exactly `h` antichains where `h` is the
   longest chain length.
2. Connect `h` to Mathlib's `Set.chainHeight (Set.univ : Set P)`.

## Where each deliverable already lives (verified this session)

**Deliverable 1 — Mirsky hard direction** → `proofs/Proofs/DilworthMirskyHardOQ01.lean`
(follow-up of parent `dilworth-theorem-oq-01`; header declares "0 axioms, 0 sorries"; `grep`
for real `sorry` tokens = none). It defines exactly the height/level construction this problem
proposes:
- `chainsTo x` / `height x := (chainsTo x).sup Finset.card` — length of the longest chain with
  top element `x` (the problem's `h`).
- `maxChainLen := (allChains).sup Finset.card` — the longest chain length `H`.
- `one_le_height`, `height_le_maxChainLen` — `1 ≤ height x ≤ maxChainLen`.
- `level k := univ.filter (height · = k)` and `level_isAntichain` — each height fiber is an
  antichain (the crux: comparable `x < y` forces `height x < height y`).
- `mirsky_antichain_cover` — the `maxChainLen` nonempty levels cover the poset.
- `mirsky_min_antichain_cover` — the cover is minimal, size exactly `maxChainLen`.

**Deliverable 2 — `Set.chainHeight` bridge** → `proofs/Proofs/DilworthTheoremOQ01OQ01OQ02.lean`
(`import Proofs.DilworthMirskyHardOQ01`; meta `dilworth-theorem-oq-01-oq-01-oq-02` is
`status: verified, badge: original, axiomCount: 0`; 0 real sorries):
- `isChainOn_iff_isChain` — the in-file comparability chain predicate agrees with Mathlib's
  `IsChain (· ≤ ·)`.
- `maxChainLen_eq_univ_chainHeight` — **exactly the requested bridge**:
  `(maxChainLen : ℕ∞) = (Set.univ : Set α).chainHeight (· ≤ ·)`. Proved by antisymmetry:
  `encard_le_chainHeight_of_isChain` (≤) and `exists_eq_chainHeight_of_finite` (≥), resolving
  the ℕ∞ / off-by-one conventions the problem flagged as the main risk.
- `univ_chainHeight_ne_top`, and `mirsky_chainHeight` — the antichain cover whose cardinality
  equals `Set.chainHeight`, i.e. "uses exactly `h` antichains" with `h = chainHeight`, minimal.

So **both** deliverables, including the exact-count and the `chainHeight` identification, are
discharged, verified, and merged. No delta remains for this slug.

## Note on slug naming (why this wasn't obvious)

The completed work sits under sibling slugs `dilworth-theorem-oq-01` (Mirsky hard) and
`dilworth-theorem-oq-01-oq-01-oq-02` (chainHeight bridge). This problem's slug is
`dilworth-theorem-oq-01-oq-03` — no data dir of its own — so the overlap is not visible from the
slug tree alone; it required reading the Lean sources. Recording it here so the next claimant
sees the duplication immediately.

## Recommendation

- **Do NOT build a Lean file for `dilworth-theorem-oq-01-oq-03`** — it would duplicate
  `DilworthMirskyHardOQ01.lean` + `DilworthTheoremOQ01OQ01OQ02.lean`.
- Mark status `surveyed`. If the pool supports it, this slug is a candidate to **skip/close** as
  a duplicate of the completed `dilworth-theorem-oq-01` / `-oq-01-oq-01-oq-02` entries.
