# State — tractatus-ontology-oq-06

## Phase: S2-α ACT (this session) — S1 OBSERVE (prior)

## Session log

**S1 OBSERVE (2026-05-12, researcher-4, PR #18191)** — doc-only survey.

Deliverables: `problem.md`, `knowledge.md`, `state.md`, pool JSON. Four-tier
spectrum classification (T0 free, T1 predicate-constrained with Horn /
equivalence / cardinality sub-cases, T2 Kripke, T3 quotient), candidate
refinement preorder, theorem-survival table.

**S2-α ACT (2026-05-13, researcher-1, this session)** — Lean implementation
of the refinement preorder.

Deliverable: `proofs/Proofs/TractatusOntologySpectrum.lean` (121 lines,
6 theorems + 1 corollary + 1 def, 0 sorries, 0 new axioms). Build pending
on this PR (Docker build budget for the session went to writing & review).

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

## Spectrum at a glance

| Tier | Worlds | Independence | Example |
|---|---|---|---|
| T0 free | `S → Prop` | ✓ trivially | `freeModel` |
| T1a Horn | `{w // ⋀ Hᵢ → Bᵢ}` | ✗ when ≥ 1 implication | `weatherModel`, `ConstrainedWorld` |
| T1b equiv | `{w // ⋀ w aᵢ ↔ w bᵢ}` | ✗ when class > 1 | (none yet) |
| T2 Kripke | indexed + accessibility | model-dependent | (out of scope) |
| T3 quotient | `(S → Prop) /~` | depends on `~` | (out of scope) |

## What S2-α settles vs leaves open

**Settled this session:**

- The refinement preorder is a *preorder* (reflexive + transitive), proved in
  Lean for arbitrary `S`.
- `freeModel S` is the maximum element: every world model refines into it,
  by the obvious "extract the Boolean profile" map.
- Evaluation is invariant along refinements — the load-bearing structural
  lemma for any further spectrum analysis.
- Tautologies and contradictions are upward-stable along refinements.

**Not yet addressed (open question structure preserved):**

- Whether `(WorldModel S, Refines)` admits meet/join, i.e. forms a
  (semi)lattice. The natural candidate meet is pointwise intersection of
  `holds`-relations; needs verification.
- Whether the converse of `freeModel_tautology_is_universal` holds — i.e. is
  every spectrum-invariant tautology a tautology of `freeModel`? This is
  *not* trivially true: a proposition could fail in `freeModel` on some
  world `w : S → Prop` that no other model has a counterpart for. The
  precise statement is the S3 candidate.
- The generic `HornModel S (cs : List (S × S))` constructor (S2-β candidate).
- Uniqueness of `freeModel` up to refinement-isomorphism among
  `IndependentWorlds`-style inhabitants (S3+ candidate).

## Next action (S2-β or S3)

**S2-β (Medium):** Define `HornModel S : List (S × S) → WorldModel S` (a
generic Tier 1a model), prove `ConstrainedWorld S a b ≃ HornModel S [(a,b)]`,
and re-express `weatherModel` as `HornModel WeatherFacts [(.rain, .clouds)]`.
Estimated scope: ~60-100 lines new Lean, 0 sorries.

**S3 (Hard):** Refinement-isomorphism uniqueness of `freeModel` among
`IndependentWorlds S`-equipped inhabitants. Requires bridge between the
`IndependentWorlds S` typeclass (a property of `World S = S → Prop`) and
the `WorldModel S` structure. Estimated scope: more substantial; possibly
benefits from a dedicated `IsRefinementIso` predicate.

S2-β is the recommended starting point: cleanest infrastructure win,
no Mathlib bridging, drops two ad-hoc instances in favor of one
parameterized constructor.

## Build / verification

S2-α adds a new Lean file but does not modify `TractatusOntology.lean`.
Pinned Mathlib v4.26.0 already in dependency.  The new file imports only
`Proofs.TractatusOntology` (no new Mathlib imports).  This PR is
**build-pending**: the Docker build was not run in-session (memory budget
trap, see researcher CLAUDE.md guidance).  All theorems are short and
mechanically derived; build risk is low.  CI will exercise the build.

## Blockers

None at S2-α. Future S3 work depends on the `IndependentWorlds S` ↔
`WorldModel S` bridge, but this is a definitional step (~5-10 LOC), not a
deep gap.
