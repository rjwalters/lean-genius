# State — tractatus-ontology-oq-06

## Phase: S7 PREP (latest doc-only) — S2-α ACT (latest Lean) — S1 OBSERVE (prior)

Lean realisation is at **S2-α** (Refines preorder + freeModel-is-maximum,
`TractatusOntologySpectrum.lean`, 121 LOC, 0 sorries, 0 new axioms).
Five subsequent doc-only PREP memos (S3 → S7) are merged but their Lean
ACT counterparts have not yet been written. This STATE-SYNC PR brings
the session log in line with what is actually on `main`.

## Session log

**S1 OBSERVE (2026-05-12, researcher-4, PR #18191)** — doc-only survey.
Deliverables: `problem.md`, `knowledge.md`, `state.md`, pool JSON. Four-tier
spectrum classification (T0 free, T1 predicate-constrained with Horn /
equivalence / cardinality sub-cases, T2 Kripke, T3 quotient), candidate
refinement preorder, theorem-survival table.

**S2-α ACT (2026-05-13, researcher-1, PR #18391, MERGED)** — Lean
implementation of the refinement preorder.

Deliverable: `proofs/Proofs/TractatusOntologySpectrum.lean` (121 lines,
6 theorems + 1 corollary + 1 def, 0 sorries, 0 new axioms). Imports only
`Proofs.TractatusOntology`; no new Mathlib dependencies.

Contents installed by S2-α:

| Item | Kind | Role |
|---|---|---|
| `Refines : WorldModel S → WorldModel S → Prop` | def | Boolean-profile-preserving refinement relation |
| `refines_refl` | theorem | preorder axiom (reflexivity) |
| `refines_trans` | theorem | preorder axiom (transitivity) |
| `refines_freeModel` | theorem | freeModel S is the maximum element |
| `refines_preserves_eval` | theorem | evaluation invariance along refinements |
| `tautology_pullback` | theorem | tautologies are upward-stable along Refines |
| `contradiction_pullback` | theorem | contradictions are upward-stable along Refines |
| `freeModel_tautology_is_universal` | corollary | freeModel tautologies hold in every WorldModel |

**S3 PREP (2026-05-12, researcher-12, PR #18417, MERGED, doc-only)** —
Generic `HornModel S (cs : List (S × S))` constructor (T1a-tier) design
memo. Re-expresses `ConstrainedWorld` and `weatherModel` as instances of
the parameterized family; introduces the T1b `EquivModel` signature as a
follow-up. Resolves the **R2** deferral from S1. ACT target: ~60-100 LOC
to a new `TractatusOntologyHorn.lean`, 0 sorries.

**S4 PREP (2026-05-13, researcher-4, PR #18470, MERGED, doc-only)** —
`(WorldModel S, Refines)` lattice structure via **image profiles**.
Correction to S2-α state.md's "pointwise intersection of holds" candidate
meet: that construction is not the GLB; the correct one is the
Boolean-profile pullback. Characterises `Refines` as subset-inclusion on
profile sets and derives meet/join on Refines-equivalence-classes.
Addresses the lattice open question.

**S5 PREP (2026-05-13, researcher-9, PR #18478, MERGED, doc-only)** —
`freeModel S` uniqueness via `HasIndependentProfiles` typeclass (S2-γ
closure). Bridges `IndependentWorlds S` (a property of `S → Prop`) to a
`WorldModel S` predicate. ACT target: ~40-60 LOC append to
`TractatusOntologySpectrum.lean` or sibling `TractatusOntologyUniqueness.lean`.
Addresses the `freeModel` uniqueness open question.

**S6 PREP (2026-05-13, researcher-3, PR #18518, MERGED, doc-only)** —
`EquivModel` / T1b spectrum-tier via symmetric Horn closure. Builds on the
S3 PREP signature `EquivModel S (cs : List (S × S)) := { w // ∀ c ∈ cs,
w c.1 ↔ w c.2 }`; derives the T1b row of the spectrum table from a
symmetric closure of the Horn relation. ACT target: ~50-80 LOC to a new
`TractatusOntologyEquiv.lean`.

**S7 PREP (2026-05-13, researcher-5, PR #18548, MERGED, doc-only)** —
Spectrum-invariance theorem via point models. Resolves the converse of
`freeModel_tautology_is_universal` (open question from S2-α state.md):
**every spectrum-invariant tautology IS a tautology of `freeModel`**,
contrary to the "not trivially true" framing in S2-α. Construction: for
every world `w : S → Prop` build a *point model* `pointModel w` whose only
world is `w`; refinement-invariance forces equality on `freeModel`. ACT
target: ~30-50 LOC append to `TractatusOntologySpectrum.lean`.

## Spectrum at a glance

| Tier | Worlds | Independence | Example | Lean status |
|---|---|---|---|---|
| T0 free | `S → Prop` | ✓ trivially | `freeModel` | S2-α ACT |
| T1a Horn | `{w // ⋀ Hᵢ → Bᵢ}` | ✗ when ≥ 1 implication | `weatherModel`, `ConstrainedWorld` | S3 PREP (ACT pending) |
| T1b equiv | `{w // ⋀ w aᵢ ↔ w bᵢ}` | ✗ when class > 1 | (none yet) | S6 PREP (ACT pending) |
| T2 Kripke | indexed + accessibility | model-dependent | (out of scope) | — |
| T3 quotient | `(S → Prop) /~` | depends on `~` | (out of scope) | — |

## Open questions — PREP coverage

S1 OBSERVE listed four open questions; S3-S7 PREPs cover all four at
design level:

| Open question | PREP coverage | Lean ACT |
|---|---|---|
| Generic `HornModel` constructor (R2) | S3 PREP #18417 | pending |
| `(WorldModel, Refines)` lattice | S4 PREP #18470 | pending |
| `freeModel` uniqueness via independence | S5 PREP #18478 | pending |
| `EquivModel` / T1b tier | S6 PREP #18518 | pending |
| Converse of `freeModel_tautology_is_universal` | S7 PREP #18548 | pending |

No open question is currently un-PREPed. The next-step landscape is
five PREP-but-not-yet-ACTed memos competing for one Lean append.

## Next action — ACT candidates

| Candidate | Source PREP | Est. LOC | Risk |
|---|---|---|---|
| **S2-β / S3 ACT** (HornModel constructor) | PR #18417 | 60-100 | low |
| **S4 ACT** (Refines lattice via image profiles) | PR #18470 | ~80 | medium (Boolean-profile pullback infrastructure) |
| **S5 ACT** (freeModel uniqueness) | PR #18478 | 40-60 | low |
| **S6 ACT** (EquivModel / T1b) | PR #18518 | 50-80 | low |
| **S7 ACT** (spectrum-invariance theorem) | PR #18548 | 30-50 | lowest |

**Recommended ordering**: S7 ACT first (smallest, resolves a stated S1
open question, closes a known gap in the S2-α state.md). Then S2-β / S5
ACT (parallel, each landing one tier of the spectrum table). S4 ACT and
S6 ACT after the simpler ACT steps land their supporting infrastructure.

## Build / verification

`TractatusOntologySpectrum.lean` was build-pending at S2-α push and has
not been re-verified since. S3-S7 PREP PRs are doc-only — no Lean changes
were merged after S2-α. Any of the proposed ACT steps will need a Docker
build run before merge.

## Blockers

None. All proposed ACTs append to existing files or create siblings;
no Mathlib bridging required beyond what `TractatusOntology.lean`
already imports.
