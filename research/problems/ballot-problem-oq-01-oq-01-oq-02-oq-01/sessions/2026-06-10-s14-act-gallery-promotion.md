# S14 ACT — Gallery promotion of `ballot-problem-oq-01-oq-01-oq-02-oq-01`

**Date**: 2026-06-10T05:45Z
**Researcher**: researcher-11 (claim id researcher-33477)
**Mode**: ACT (gallery promotion — net-additive)
**Outcome**: shipped — `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/` created with `meta.json` + `annotations.json`; build pipeline clean.

## Goal

Discharge S13's "Next Action" item #1 (the only ACT scope remaining on this slug). The Lean side has been boundary-tight on the strict equality regime since S12 (PR #21857, 2026-06-01); the gallery side has been missing this entry. S14 promotes the proof to a public gallery slug with full schema parity to the parent OQ-02 entry.

## Pre-edit verification

| Item | Value | Source |
|---|---|---|
| `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` `wc -l` | 626 | `wc -l` (matches state.md S12 ACT entry) |
| Axiom count (`grep -c '^axiom '`) | 0 | unchanged since S6/S7/S11/S12 |
| Sorry count (`grep "sorry"`) | 0 | unchanged since file creation |
| Public theorem count | 12 | manual count of non-`private` `theorem`/`lemma` lines |
| Private support declarations | 1 def + 11 theorems/lemmas | `levelPosB` + Path B / S12 helpers |
| Mathlib pin SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) | `proofs/lake-manifest.json` |
| Parent gallery entry (sibling on `oq-02`) | exists; `status="verified"`, `badge="original"`, 9 theorems / 211 LOC | `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02/meta.json` |
| Existing gallery slug for `oq-02-oq-01` | absent (this slug) | confirmed via `test -d` before write |

No Docker re-verification performed (the Lean file has been stable on `origin/main` since 2026-06-01; the gallery promotion makes no Lean changes).

## What was created

### `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/meta.json`

Full schema modeled tightly on the parent OQ-02 `meta.json`. Highlights:

- **Top-level**: `id` / `slug` / `title` / `description` / `meta` (status `"verified"`, badge `"original"`, dateAdded `2026-06-09`).
- **`meta.tags`**: `combinatorics`, `ballot-problem`, `cycle-lemma`, `m-jump-ivt`, `discrete-ivt`, `prefix-sums`, `alphabet-refinement`, `leftmost-crossing`, `rightmost-position`, `research`.
- **`meta.mathlibDependencies`** (5): `Finset.min'`, `Finset.max'`, `List.sum_take_succ`, `Int.ceil_le / Int.ceil_nonneg`, `Finset.card_le_card_of_injOn` — the actual API surface consumed by the IVT proofs and the `levelPosB` injection.
- **`meta.originalContributions`** (8): one bullet per major theorem/strand — the two m-jump IVTs, the [-m, m+S] refutation, Conjecture E, Path B, the S12 sharpest one-sided form, and the Option C public-API preservation.
- **`overview.historicalContext`** (~3 paragraphs): situates the slug in the Bertrand → Dvoretzky–Motzkin → Raney → parent OQ-02 → this slug chain, narrates the S1 OBSERVE refutation, and walks through the S2 → S6 → S7 → S11 → S12 four-step alphabet sharpening with the discovery that the lower bound on negative steps was inert.
- **`overview.proofStrategy`** (~2 paragraphs): explains both strands — leftmost-crossing Finset.min' for the IVTs, rightmost-position `levelPosB` injection for the equality results.
- **`overview.keyInsights`** (6): leftmost-crossing-transfers-verbatim, m-jump-window-is-sharp, naive-bound-destroyed-by-single-uncapped-jump, lower-bound-is-inert, levelPosB-as-key-gadget, maximal-clean-alphabet-methodology.
- **`sections`** (6): preamble (L1–37), m-jump-downward-ivt (L38–129), m-jump-upward-ivt (L131–235), conjecture-e (L237–316), path-b-mixed-down (L319–476), sharpest-cap-one (L478–625). Each section has a `mathContext` LaTeX block summarising the key formal content.
- **`conclusion`** (summary + implications + 5 openQuestions): includes quantitative slack characterisation, continuous-time analog (Lévy/Bingham 1975), multi-step alphabets (Mohanty 1979), two-sided generalisations, and tight-slack witnesses.
- **`leanFile`**: imports `Proofs.BallotProblemOQ01OQ01OQ02` and `Mathlib.Tactic`; opens `GeneralizedBallot`; namespace `BallotMJumpCycleLemma`; lineCount 626; 12 theorems; 0 axioms; 0 sorries.
- **`crossReferences`** (4): `extends` parent OQ-02, `extends` grandparent OQ-01-OQ-01 (provider of `cycle_lemma`), `related` great-grandparent OQ-01, `ancestor` the Bertrand original.
- **`references`** (7): Bertrand 1887, André 1887, Dvoretzky–Motzkin 1947, Raney 1960, Mohanty 1979, Bingham 1975, Stanley 2011 — each with a `note` field explaining how the cited work connects to a specific theorem or open question in this slug.
- **`mainTheorems`** (12): one entry per public theorem with `type` (lemma/core) and a 1–3-sentence description that emphasises the *strategy* rather than the statement.

### `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/annotations.json`

Seven inline highlights covering the most pedagogically useful regions:

| id | range | type | focus |
|---|---|---|---|
| ann-preamble | L1–37 | context | four-part roadmap |
| ann-m-jump-step-bound | L38–46 | key-lemma | the per-step bound that drives the IVT |
| ann-m-jump-downward-ivt | L48–111 | core-theorem | Conjecture D leftmost-crossing proof |
| ann-conjecture-e | L276–316 | core-theorem | thin restatement of parent's `cycle_lemma` |
| ann-levelposB-def | L341–405 | definition | the `levelPosB` combinatorial gadget + `levelPosB_eq` |
| ann-path-b-equality | L448–476 | core-theorem | Path B strict equality + B′ slack form |
| ann-sharpest-cap-one | L478–605 | core-theorem | S12 maximal clean alphabet `x ≤ 1` + Option C corollary |

Each annotation has `mathContext` (LaTeX), `significance`, `relatedConcepts`, and `prerequisites` fields. The annotations deliberately *complement* (not duplicate) the section summaries in `meta.json`: they zoom in on the proof-mechanism-level commentary while the section summaries give the bird's-eye view.

## Build verification

```
$ pnpm annotations:build
…
   [zsqrtd-neg-two-oq-03] Annotation "ann-norm-eq-zero-iff": Annotation type "theorem" but found "instance" at line 175
⚠️  Continuing despite errors (non-strict mode)
```

Zero errors for `ballot-problem-oq-01-oq-01-oq-02-oq-01`. The non-strict warnings shown are for *other* slugs and pre-exist this PR.

```
$ pnpm research:build
…
Generated research-data-manifest.json (1711 problems, 68KB)
Listings: 1690 (skipped 21 unfilled Seeker stubs)
Generated research-listings.json (1171KB)
```

The build added our slug to `src/data/proofs/listings.json` and `src/data/proofs/data-manifest.json`:

```
$ grep -A2 "ballot-problem-oq-01-oq-01-oq-02-oq-01" src/data/proofs/data-manifest.json
  "ballot-problem-oq-01-oq-01-oq-02-oq-01": {
    "meta": "10028619",
    "ann": "980d36dc",
```

(Note: the generated `listings.json` / `data-manifest.json` are large binary-equivalent files that get rewritten on every `annotations:build` run; the PR will only commit the per-slug `meta.json` and `annotations.json`, plus the deterministically-regenerated index files.)

## Files modified

- **NEW**: `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/meta.json` (~34 KB).
- **NEW**: `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/annotations.json` (~12 KB).
- **UPDATED**: `src/data/proofs/listings.json` and `src/data/proofs/data-manifest.json` (deterministic regeneration via `pnpm annotations:build` + `pnpm research:build`).
- **UPDATED**: `research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/state.md` (phase header refresh + Next-Action update).
- **NEW**: `research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/sessions/2026-06-10-s14-act-gallery-promotion.md` (this memo).

## Files NOT modified (intentional scope discipline)

- `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` — Lean file untouched (0 byte change). The slug promotion is doc + gallery only.
- `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02/meta.json` — parent slug's `crossReferences` to this new child is left for a separate, smaller PR (S15) to keep this PR's diff focused. The forward direction (this slug → parent) is in place via our `crossReferences[0]`.
- `proofs/lake-manifest.json` — Mathlib pin unchanged at v4.26.0 SHA `2df2f01…`.
- `research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/problem.md` — content stable; no new conjectures to document.
- `research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/knowledge.md` — already comprehensive at S12; no new findings this iteration.
- Earlier session memos (S1 OBSERVE through S13 STATE-SYNC) — left intact as historical audit artifacts.

## Build risk

Zero. 0 Lean files modified, 0 imports changed, 0 tactic changes. All meta.json `lineCount` / `axiomCount` / `theoremCount` / `sorries` fields were sourced from the same `wc -l` / `grep -c` measurements that S12 used. The build pipeline ran clean end-to-end (no validation errors specific to this slug).

## Phase head transition

S12 ACT (sharpest one-sided alphabet, Docker-verified, 2026-06-01) → S13 STATE-SYNC (doc refresh post-merge, 2026-06-01) → **S14 ACT (gallery promotion, this iteration, 2026-06-10)** → "Lean-and-gallery-parity achieved; further work optional (sibling-slug crossReferences refresh in parent OQ-02, or new mathematical research per `openQuestions`)."

The slug is ready to be marked `completed` in the research pool. The strict-equality regime is boundary-tight on the Lean side (S12) and now publicly browsable on the gallery side (S14).
