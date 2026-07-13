# Repair the stale Aristotle companion file

**Researcher:** researcher-2
**Date:** 2026-07-01
**Phase:** ACT (maintenance) — main research sorry unchanged
**Scope:** `Proofs/SchroederBernsteinOQ03Aristotle.lean` only.

## What was wrong

The Aristotle companion file did **not compile** on `origin/main` — it had a
`sorry` (`partialInverse_partrec`) *and* two genuine compile errors from
Mathlib API drift:

- `partialInverse_spec`: `of_decide_eq_true (Nat.rfind_spec h)` — `Nat.rfind_spec`
  now returns membership `true ∈ p n`, not `p n = true`.
- `partialInverse_dom`: `Nat.rfind_min' (by simp [hk])` left the witness index a
  metavariable (`g ?m = m` unsolved).

All three lemmas are, in fact, **already proved** in the main file
`SchroederBernsteinOQ03.lean` (theorems `partialInverse_partrec` /
`partialInverse_spec` / `partialInverse_dom`, lines 129/142/149) — the companion
is a stale duplicate that was never kept in sync. Per the researcher role doc,
existing `*Aristotle.lean` companion files are not deleted during the
deprecation transition, so this repairs rather than removes it.

## Fixes (all verified, 0-axiom)

- `partialInverse_partrec` — proved: `Partrec.rfind` + `Computable.partrec`, with
  the decidable predicate `fun (m,n) => decide (g n = m)` shown computable via
  `Computable₂.comp (Primrec₂.to_comp Primrec.eq.decide) (hg.comp Computable.snd) Computable.fst`.
  Gotcha: `Primrec.eq : PrimrecRel Eq` does **not** unify with
  `Primrec₂ (fun a b => decide (a = b))` — bridge with `Primrec.eq.decide`.
- `partialInverse_spec` — `simpa using Nat.rfind_spec h`.
- `partialInverse_dom` — pin the `rfind_min'` witness: supply
  `(show decide (g k = m) = true by simp [hk])` explicitly.
- Renamed unused `hg_inj` → `_hg_inj` (matches the main file, silences the linter).

`#print axioms` on the repaired lemmas: only `propext`/`Classical.choice`/`Quot.sound`.
Built with `lake env lean` (Docker image build still broken — `containerd` I/O error).

## Main research sorry: unchanged

The hard direction of `myhill_isomorphism` (`SchroederBernsteinOQ03.lean:715`,
the collision-resolving stage / `isGFree` Π₁ obstruction) is the known
multi-session, cross-agent blocker (r1/r2/r6). Not attempted here — it needs the
~200-line back-and-forth priority construction, not a quick fix.
