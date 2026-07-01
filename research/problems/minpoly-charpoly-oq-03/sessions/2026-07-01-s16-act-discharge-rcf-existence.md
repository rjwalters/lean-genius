# S16 ACT — Discharge `rational_canonical_form_exists` (RCF existence)

**Researcher:** researcher-2
**Date:** 2026-07-01
**Phase:** ACT → COMPLETED
**Result:** The lone remaining `sorry` in `Proofs/MinpolyCharpolyOQ03.lean`
is discharged. The file is now **0-sorry, 0-axiom** (`#print axioms` reports
only `propext` / `Classical.choice` / `Quot.sound`). Gallery entry promoted
`formalized`/`wip` → `verified`/`verified`.

## The key observation

The parent's open sorry (`rational_canonical_form_exists`, strong form:
`∃ c, c.prodFactors = M.charpoly ∧ c.lastFactor = minpoly F M`) is the
**exact same statement** already proved, axiom-free, elsewhere in-tree:

- `Proofs/RationalCanonicalFormExists.lean` contains a fully-proved
  `rational_canonical_form_exists` (Aristotle-synthesized, project
  `d2395b8d`, integrated verbatim). It builds the theory from scratch:
  the `F[X]`-module `mulX` on `Fⁿ`, `charpoly_mulX_*` naturality lemmas,
  `det/charpoly_blockDiagonal'`, primary decomposition via Mathlib's
  `Module.equiv_directSum_of_isTorsion`, and a combinatorial regrouping of
  prime powers into a divisibility chain (`exists_chain_aux`).
- `Proofs/MinpolyCharpolyOQ03OQ01.lean` already consumed it in
  `xModule_has_invariantFactorChain` (same statement, via a one-line field
  copy) — but the OQ-01 bridge **imports** the parent, so the parent could
  not import it back (cycle).

## The fix (2 lines of proof + 1 import)

Added `import Proofs.RationalCanonicalFormExists` to the parent and inlined
the same bridge the OQ-01 file uses (its `InvariantFactorChain` is
field-identical — `factors`/`monic`/`posDegree`/`chain` — and
`prodFactors`/`lastFactor` are definitionally `factors.prod` /
`factors.getLast?.getD 1` on both):

```lean
obtain ⟨c, hprod, hlast⟩ := RationalCanonicalFormExists.rational_canonical_form_exists M
exact ⟨⟨c.factors, c.monic, c.posDegree, c.chain⟩, hprod, hlast⟩
```

This is a wiring/integration step, not new deep mathematics: the hard proof
already lived in-tree. What it does close is the parent gallery entry —
15 prior iterations left this build-gated behind a hung Docker daemon.

## Build notes

- Docker image build is still broken (`containerd` `input/output error`)
  even though `docker info` succeeds — so `docker-build.sh` fails.
- Fallback: `LAKE_UNSAFE=1 lake env lean` in the worktree (`.lake` symlinks
  the main `proofs/.lake`). `RationalCanonicalFormExists.olean` was missing
  from the shared build, so built it first (~38 s), then the parent (clean).

## Follow-ups (NOT pursued — depth guard)

Slug depth is 1 (`minpoly-charpoly-oq-03`), so follow-ups are allowed, but
both natural ones are genuinely large and better as future sibling OQs:
- explicit similarity transform `M ~ ⊕ companionMatrix pᵢ` (OQ-03-OQ-04, ~200 LOC);
- uniqueness of the invariant-factor chain up to associates.
No weak follow-ups proposed.
