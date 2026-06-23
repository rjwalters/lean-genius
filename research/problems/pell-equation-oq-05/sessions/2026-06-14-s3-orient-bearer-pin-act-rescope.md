# S3 ORIENT — bearer pin at lake commit + ACT re-scope

**Researcher**: researcher-7
**Date**: 2026-06-14
**Phase**: ORIENT (no build — Docker DOWN; Aristotle `prove` → "Resource not found")
**Lean change**: none (0 `.lean` files; no proof produced)

## Goal

The S2 ORIENT (#24131, merged) located the Mathlib Dirichlet-unit-theorem API
by module/name and concluded the remaining work is "specialization + packaging".
This session pins every bearer to an exact file:line at the repo's lake commit
and audits whether the ACT really is just packaging — it is not.

## Bearers confirmed at pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

Via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<pin>` +
`gh search code`:

- `NumberField.Units.rank := Fintype.card (InfinitePlace K) - 1` —
  `…/Units/DirichletTheorem.lean:354` (a **def**, not a theorem).
- `NumberField.Units.finrank_eq_rank` — same file :372.
- `instance {f : Polynomial ℚ} [Fact (Irreducible f)] : NumberField (AdjoinRoot f)` —
  `…/NumberField/Basic.lean:451`.
- `card_eq_nrRealPlaces_add_nrComplexPlaces` — `…/InfinitePlace/Basic.lean:416`.

## Re-scope (the substantive finding)

The ACT plan's step 1 — "instantiate `rank`, prove `rank = 1` from signature" —
hides all its difficulty in three words ("from signature"):

1. **Field construction is off-the-shelf.** `K := AdjoinRoot (X^3-2)` is a
   `NumberField` by the Basic.lean:451 instance; only input is
   `Fact (Irreducible (X^3-2))` (Eisenstein at 2). No bespoke field-building.
2. **`rank = 1` is definitional.** `rank K = card (InfinitePlace K) - 1` *by def*,
   so the goal collapses to `card (InfinitePlace K) = 2`. There is no
   abstract-theorem-instantiation step.
3. **The real work is the signature, and it has NO bearer.**
   `card_eq_nrRealPlaces_add_nrComplexPlaces` reduces to
   `nrRealPlaces + nrComplexPlaces`, but Mathlib ships **no signature-from-minpoly
   procedure** for a general explicit field. Cyclotomic fields get bespoke lemmas
   (`nrRealPlaces_eq_zero`, `Cyclotomic/Embeddings.lean`); `AdjoinRoot (X^3-2)`
   gets nothing. One must count real vs complex embeddings by hand via the
   embeddings↔roots correspondence (X^3-2: one real root, one complex pair ⟹
   `(r1,r2)=(1,1)`). **This is the LOC-dominant part of the ACT.**

## Outcome / next action

Knowledge.md + state.md updated with the pinned bearer table and re-ordered ACT
plan (place-count first). No collision: open PR #24135 touches
`scripts/research/enrich-research.ts` + `src/data/research/problems/...json`
(path-disjoint from `research/problems/.../*.md`). Discharge still gated on a
Docker- or Aristotle-up session.
