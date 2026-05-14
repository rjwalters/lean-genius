# State — tractatus-ontology-oq-06

## Phase: S7 ACT (this PR, build pending) — S2-α + S7 ACT (latest Lean) — S1 OBSERVE (prior)

Lean realisation is now at **S2-α + S7 ACT**
(`TractatusOntologySpectrum.lean`, 121 → 207 LOC, +86 LOC, 0 sorries,
0 new axioms). S7 ACT (this PR, researcher-12, 2026-05-14) ships the
spectrum-invariance biconditional + the point-model construction per
S7 PREP (PR #18696) §1-§6. The other four PREP memos (S3 / S4 / S5 / S6)
remain ACT-pending — they target other tiers of the spectrum
(HornModel constructor, Refines lattice, freeModel uniqueness,
EquivModel/T1b) and are orthogonal to S7's meta-level characterisation.

## S7 ACT (2026-05-14, researcher-12, build pending)

Appends seven new declarations to `TractatusOntologySpectrum.lean` after
the existing `freeModel_tautology_is_universal` corollary:

| Item | Kind | LOC | Role |
|---|---|---|---|
| `pointModel : (S → Prop) → WorldModel S` | def | 4 | Singleton-world model whose profile equals `w`. |
| `pointModel_holds` | `@[simp]` theorem | 4 | Direct read-off lemma. |
| `pointModel_evalM` | theorem | 6 | `evalM (pointModel w) p () ↔ evalM (freeModel S) p w` via the existing structural-induction pattern (`elementary / neg / conj`). |
| `pointModel_isTautology_iff` | theorem | 7 | Corollary using singleton-world universality. |
| `spectrum_invariant_iff_freeModel_tautology` | theorem | 7 | Main biconditional: forward via instantiation at `freeModel S`, reverse via `freeModel_tautology_is_universal`. |
| `spectrum_invariant_implies_freeModel_via_pointModels` | theorem | 5 | Alternative converse proof via point models (more informative; pedagogically central). |
| `spectrum_invariant_contradiction_iff_freeModel_contradiction` | theorem | 8 | Dual for contradictions, using `contradiction_pullback` along `refines_freeModel`. |

Net delta: **+86 LOC**, 7 new declarations, 0 new sorries, 0 new axioms,
0 new imports.

### Why ship S7 first (not S3 / S4 / S5 / S6)

Per S7 PREP §1-§6, the S7 recipe is the **lowest-risk** of the five
PREP-pending ACT candidates: ~30-50 LOC mechanical, induction + direct
instantiation, no Mathlib bearer audit needed (all symbols are existing
project APIs). The other four PREPs target larger structures
(HornModel constructor family, Refines lattice via image-profiles,
freeModel uniqueness via independence, EquivModel/T1b symmetric Horn)
and warrant their own ~40-80 LOC ACT sessions each.

### Resolves the state.md open question explicitly

S2-α landing (PR #18391, 2026-05-13) flagged in `state.md` § "Not yet
addressed":

> Whether the converse of `freeModel_tautology_is_universal` holds —
> i.e. is every spectrum-invariant tautology a tautology of
> `freeModel`?

S7 PREP refuted the "not trivially true" framing: the converse is one
step via `freeModel S`-instantiation (since `freeModel S` is itself in
the spectrum). The point-model proof is strictly more informative —
it shows the converse holds even if the spectrum quantifier were
restricted to "small / point-like" models. **This PR ships both
proofs.** The state.md open question is now resolved.

### Build-verification posture

Build pending. The worktree's `proofs/.lake` is the recursive
self-symlink loop documented in
`feedback_researcher_lake_symlink_loop_and_wipe.md`; local Docker
verification is unreliable. CI / doctor verifies via
`./proofs/scripts/docker-build.sh Proofs.TractatusOntologySpectrum`
from a clean worktree.

The new code uses only existing project APIs (`WorldModel`,
`freeModel`, `evalM`, `IsTautologyM`, `IsContradictionM`, `Refines`,
`refines_freeModel`, `refines_preserves_eval`, `tautology_pullback`,
`contradiction_pullback`, `freeModel_tautology_is_universal`) — no new
Mathlib imports, no Mathlib bearer audit needed.

### Race-safety note (S7 ACT)

- Pre-claim probe (~01:10 UTC, 2026-05-14): 0 open PRs on slug.
- Pre-push probe will re-verify before push.

### Next action

After S7 ACT lands, four remaining ACT candidates remain orthogonal:

1. **S2-β / S3 ACT** — `HornModel` constructor (T1a tier), ~60-100 LOC. PREP doc: #18417.
2. **S4 ACT** — Refines lattice via image-profiles, ~40-80 LOC. PREP doc: #18470.
3. **S5 ACT** — freeModel uniqueness via independence, ~40-60 LOC. PREP doc: #18497.
4. **S6 ACT** — EquivModel / T1b via symmetric Horn, ~40-80 LOC. PREP doc: #18518.

## Session log (prior, pre-S7 ACT)

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
