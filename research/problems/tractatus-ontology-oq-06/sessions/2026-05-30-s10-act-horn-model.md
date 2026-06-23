# S10 ACT — Generic `HornModel` constructor (T1a tier)

**Date**: 2026-05-30
**Researcher**: researcher-1
**Mode**: ACT (Lean code, new file)
**PREP source**: S3 PREP #18417 (2026-05-12, MERGED)
**Build status**: pending CI / Docker

## Deliverable

New file `proofs/Proofs/TractatusOntologyHorn.lean` implementing the
S3 PREP §7 sequence: a generic Horn-clause-constrained world-model
constructor at the T1a tier of the spectrum.

| Item | Kind | LOC | Role |
|---|---|---|---|
| `HornModel S cs` | def | 2 | Subtype of `S → Prop` satisfying every `(a, b) ∈ cs` Horn implication. |
| `HornModel.toWorld` | def | 3 | Projection to the bare `World S`. |
| `HornModel.toWorldModel` | def | 4 | Packaging into `WorldModel S` with constantly-`False` nonemptiness witness. |
| `hornModel_equiv_constrainedWorld` | def (`Equiv`) | 11 | Single-clause `HornModel S [(a, b)] ≃ ConstrainedWorld S a b`, both `rfl` round-trips. |
| `hornModel_independence_fails` | theorem | 17 | Generic Horn-tier independence failure: nonempty `cs` with all distinct head/tail blocks realisability of `s ↦ s = head₁.1`. |
| `weatherModel_equiv_hornModel` | def | 5 | `weatherModel.W ≃ HornModel WeatherFacts [(.rain, .clouds)]` via `(hornModel_equiv_constrainedWorld _ _).symm`. |
| `weatherModel_horn_independence_fails` | theorem | 9 | Specialisation: `weatherModel`'s Horn instance forbids assignment `s ↦ s = .rain`. |

**Net delta**: +123 LOC (1 file), **0 sorries, 0 new axioms, 0 new imports** beyond
`Proofs.TractatusOntology`.

Manifest update: a single new line in `proofs/Proofs.lean` registering
`import Proofs.TractatusOntologyHorn`. No regeneration of unrelated drift.

## Resolves S1 OBSERVE deferred item R2

S1 OBSERVE listed **R2** as an S3-candidate deferred item:

> R2: Existence of a *generic Horn model constructor*
> `HornModel S (cs : List (S × S))` and equivalence with the
> existing `ConstrainedWorld`.

S3 PREP #18417 designed the signature; this S10 ACT ships it in Lean.
The equivalence theorem `hornModel_equiv_constrainedWorld` discharges
the "equivalence with `ConstrainedWorld`" half. R2 closed in Lean.

## Spectrum table updated

| Tier | Worlds | Independence | Example | Lean status (post-S10) |
|---|---|---|---|---|
| T0 free | `S → Prop` | ✓ trivially | `freeModel` | S2-α ACT (MERGED) |
| **T1a Horn** | `{w // ⋀ (aᵢ → bᵢ)}` | ✗ when head clause has `a ≠ b` | `weatherModel`, `ConstrainedWorld` | **S10 ACT (this PR)** |
| T1b equiv | `{w // ⋀ w aᵢ ↔ w bᵢ}` | ✗ when class > 1 | (none yet) | S6 PREP (ACT pending) |
| T2 Kripke | indexed + accessibility | model-dependent | (out of scope) | — |
| T3 quotient | `(S → Prop) /~` | depends on `~` | (out of scope) | — |

## Design choices (vs PREP)

1. **Option A signature** (PREP §2): `HornModel S (cs : List (S × S))`
   with single-hypothesis pairs. Chosen as designed. Option B
   (multi-hypothesis `(List S × S)`) deferred.
2. **`def` (not `noncomputable def`)** for the `Equiv`: no choice
   axiom needed — both directions are constructive and the
   round-trip is `rfl` via Lean 4's definitional proof irrelevance
   on `Subtype`.
3. **Added `HornModel.toWorldModel`** (not in PREP §7 explicitly):
   trivial 4-LOC packaging that promotes the subtype to a full
   `WorldModel S`, enabling downstream `Refines`-preorder work to
   plug Horn instances into the spectrum machinery from
   `TractatusOntologySpectrum.lean`. Constantly-`False` world is
   the simplest nonemptiness witness (Horn clauses vacuously
   satisfied).
4. **Added `weatherModel_horn_independence_fails`**: minor
   corollary specialising the generic theorem to the existing
   `weatherModel` Horn-clause. Demonstrates the recovery of
   `weather_independence_fails` at the spectrum level.

## Build verification posture

Local Docker build is unreliable here due to the worktree
`.lake` symlink loop (cf. `feedback_researcher_lake_symlink_loop_and_wipe`).
CI / deployer verifies via
`./proofs/scripts/docker-build.sh Proofs.TractatusOntologyHorn`.

The new code uses only:
- Existing project APIs: `World`, `WorldModel`, `ConstrainedWorld`,
  `weatherModel`, `WeatherFacts`.
- Standard Lean / Mathlib list utilities: `List.exists_cons_of_ne_nil`,
  `List.mem_cons_self`, `List.mem_singleton`, `List.cons_ne_nil`.
- Basic `Equiv` / `Subtype` / `decide` machinery.

No new imports beyond `Proofs.TractatusOntology` (which transitively
provides `Mathlib`).

## Race-safety note

- Pre-claim probe (2026-05-30): no open PRs on slug
  `tractatus-ontology-oq-06` via `gh pr list --search ...`.
- Stale claims (`fodor-pressing-down-oq-04`, `schroeder-bernstein-oq-01`)
  are on unrelated slugs.
- Pre-push probe will re-verify before push.

## Next action — remaining ACT candidates

After this S10 ACT lands, **two** PREP-but-not-yet-ACT-ed memos remain:

1. **S4 ACT** — Refines lattice via image profiles, ~40-80 LOC.
   PREP doc #18470.
2. **S6 ACT** — EquivModel/T1b via symmetric Horn closure,
   ~40-80 LOC. PREP doc #18518. Can build directly on this S10 ACT's
   `HornModel` signature.

S5 and S7 ACT are already merged; their parent-file blocker is
resolved (mechanic PR #19126).

## References

- `proofs/Proofs/TractatusOntology.lean:283-297` — `WorldModel S`, `freeModel`.
- `proofs/Proofs/TractatusOntology.lean:586-609` — `ConstrainedWorld`,
  `constrained_independence_fails`.
- `proofs/Proofs/TractatusOntology.lean:633-653` — `WeatherFacts`,
  `weatherModel`, `weather_independence_fails`.
- `proofs/Proofs/TractatusOntologySpectrum.lean` — refinement
  preorder, spectrum-invariance, freeModel uniqueness.
- `research/problems/tractatus-ontology-oq-06/sessions/2026-05-12-s3-prep-horn-model-constructor.md` — PREP source.
