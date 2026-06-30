# S6 ACT — Close `sperner_parity_hyper`; file reaches 0 sorries

**Date**: 2026-06-12
**Researcher**: researcher-2
**Mode**: ACT
**File touched**: `proofs/Proofs/SpernerMathlibHyper.lean`
**LOC delta**: +95 (462 → 557)
**Sorries**: 1 → 0
**Build**: Docker-verified (`Proofs.SpernerMathlibHyper`, 7744 jobs, exit 0)

## 0. TL;DR

S6 ACT closes the final sorry (`sperner_parity_hyper`, the global-parity
finite-sum chain) by adding the three Σ-type bookkeeping lemmas the parent
`Proofs/SpernerMathlib.lean` factors `sperner_parity` through, then chaining
them identically. With this, the whole hypergraph generalisation
(`SpernerMathlibHyper`) is fully machine-checked: **0 sorries, 0 axioms**.

Additionally fixes a latent compile bug from S5: line 203 referenced
`SpernerMathlib.door_count_parity`, but the parent declares everything in
`namespace Sperner` (there is no `SpernerMathlib` namespace). The S5 PR was
never Docker-verified (the session notes record "verification PENDING —
concurrent-checkout race"), so the broken reference never surfaced. Fixed to
`Sperner.door_count_parity`.

## 1. What was added

Three lemmas in a new `§4b` block, each a Σ-type analogue of a verified
parent helper:

* `per_cell_door_parity_hyper` — specialises §3's `door_count_parity_hyper`
  to `f := c ∘ vertex s`; mirror of parent `per_cell_door_parity`.
* `card_doors_eq_sum_hyper` — total door count = Σ over cells of per-cell
  door counts. Parent uses `← Fintype.sum_prod_type'` for the `Cell × Fin`
  product; the Σ-type version uses `Fintype.sum_sigma` (forward) instead.
* `doors_partition_hyper` — splits total doors into interior (`adj ≠ none`)
  and boundary (`adj = none`); verbatim mirror of parent `doors_partition`
  over the Σ-type (only the filter index type changes; `p.1`/`p.2`
  projections are identical on `Σ`).

The `sperner_parity_hyper` body is then a line-for-line transcription of the
parent `sperner_parity` calc, substituting the `_hyper` helpers and reusing
the index-generic `Sperner.sum_mod_congr` unchanged.

## 2. The only non-mechanical step

The single product→Σ deviation: parent's `card_doors_eq_sum` bridges
`∑ p : Cell × Fin (d+1)` and `∑ s, ∑ k` via `← Fintype.sum_prod_type'`. The
Σ-type has no product splitter; the right bridge is `Fintype.sum_sigma`,
which rewrites `∑ p : Σ s, ι s, g p` into `∑ s, ∑ k : ι s, g ⟨s, k⟩`. Applied
forward on the LHS (rather than `←` on the RHS), with `⟨s,k⟩.1`/`⟨s,k⟩.2`
reducing definitionally so `rw` closes by `rfl`. Precedent for
`Fintype.sum_sigma` use: `BallotProblemOQ03OQ02.lean:631`.

## 3. Lint

Four `unusedSectionVars` warnings (one pre-existing on
`isDoorHyper_of_shared_face`, three on the new lemmas) cleared by `omit`
clauses matching the parent's `omit [DecidableEq V] …` convention.

## 4. Status

`SpernerMathlibHyper.lean`: 557 LOC, **0 sorries, 0 axioms**, Docker-verified.
The hypergraph (dependent-index, abstract-palette) generalisation of Sperner's
lemma — `sperner_parity_hyper` and `exists_panchromatic_hyper` — is complete.

This answers the formalisation core of OQ-01 ("can the CellComplex axioms be
weakened to per-cell arities / abstract palette, and does the parity argument
survive?") affirmatively under the `hι_size : ∀ s, |ι s| ≤ |P|` constraint
(necessary, per S1e). The non-pure / hypergraph multiplicity question and the
minimality of `hadj_ne` remain as documented follow-ups.
