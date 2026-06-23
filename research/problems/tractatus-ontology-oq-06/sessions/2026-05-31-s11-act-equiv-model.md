# S11 ACT — `EquivModel` constructor via symmetric Horn closure (T1b tier)

**Date**: 2026-05-31
**Researcher**: researcher-1
**Mode**: ACT (Lean code, new file)
**PREP source**: S6 PREP #18518 (2026-05-13, MERGED)
**Build status**: Docker-verified (3061 jobs clean) on
`./proofs/scripts/docker-build.sh Proofs.TractatusOntologyEquiv`.

## Deliverable

New file `proofs/Proofs/TractatusOntologyEquiv.lean` implementing the
S6 PREP §8 sequence: a generic biconditional-constrained world-model
constructor at the **T1b tier** of the spectrum, plus the structural
iso witnessing T1b ⊆ T1a under symmetric-pair closure.

| Item | Kind | Role |
|---|---|---|
| `EquivModel S cs` | def | Subtype of `S → Prop` satisfying `w c.1 ↔ w c.2` for every `c ∈ cs`. |
| `EquivModel.toWorld` | def | Projection to bare `World S`. |
| `EquivModel.toWorldModel` | def | Packaging into `WorldModel S` with constantly-`False` nonemptiness witness. |
| `equivModel_iso_hornModel_symm` | def (`Equiv`) | `EquivModel S cs ≃ HornModel S (cs ++ cs.map Prod.swap)` — the structural subsumption iso. Both directions are `rfl` round-trips. |
| `refines_equivModel_hornModel` | theorem | T1b refines into T1a sharing the constraint list (strictly more constrained side embeds upward). |
| `equivModel_independence_fails` | theorem | Biconditional-tier `HasIndependentProfiles` failure for nonempty `cs` with distinct head/tail. |

**Net delta**: +138 LOC (1 new file), **0 sorries, 0 new axioms,
0 new Mathlib imports** beyond `Proofs.TractatusOntologyHorn` and
`Proofs.TractatusOntologySpectrum`.

Manifest update: a single new line in `proofs/Proofs.lean`
registering `import Proofs.TractatusOntologyEquiv` (no regeneration
of unrelated drift).

## Closes the last remaining T1-tier deferral

S1 OBSERVE listed the T1b row of the spectrum table as "(none yet)";
S3 PREP §5 introduced the signature; S6 PREP locked the architecture
and pinned the symmetric-closure subsumption. This S11 ACT ships the
Lean realisation:

- `EquivModel S cs` is now a first-class constructor.
- `equivModel_iso_hornModel_symm` records the subsumption iso.
- `refines_equivModel_hornModel` plus the strict-below remark in
  the docstring document that T1b sits below T1a in the refinement
  preorder (the converse is **false in general** — see docstring
  example).
- `equivModel_independence_fails` upgrades the independence-failure
  result to the spectrum-level statement (`HasIndependentProfiles`),
  matching the S2-α/S5/S7 idiom.

## Spectrum table updated

| Tier | Worlds | Independence | Example | Lean status (post-S11) |
|---|---|---|---|---|
| T0 free | `S → Prop` | ✓ trivially | `freeModel` | S2-α ACT (MERGED) |
| T1a Horn | `{w // ⋀ (aᵢ → bᵢ)}` | ✗ when head clause has `a ≠ b` | `weatherModel`, `ConstrainedWorld` | S10 ACT (MERGED) |
| **T1b equiv** | `{w // ⋀ w aᵢ ↔ w bᵢ}` | ✗ when class > 1 | (none yet — subsumed by T1a-symm) | **S11 ACT (this PR)** |
| T2 Kripke | indexed + accessibility | model-dependent | (out of scope) | — |
| T3 quotient | `(S → Prop) /~` | depends on `~` | (out of scope) | — |

## Design choices (vs PREP)

1. **Option C of S6 PREP §6** (keep both `HornModel` and
   `EquivModel` as named constructors, document the subsumption).
   The iso `equivModel_iso_hornModel_symm` makes the structural
   subsumption explicit; the named `EquivModel` retains
   Lean-side ergonomics (biconditional constraint lists read more
   naturally than asymmetric Horn lists `cs ++ cs.map Prod.swap`).
2. **`def` (not `noncomputable def`)** for the `Equiv`: no choice
   axiom; both directions are constructive and the round-trip is
   `rfl` via Lean 4 definitional proof irrelevance on `Subtype`
   (the underlying `S → Prop` is unchanged across both directions).
3. **`EquivModel.toWorldModel`** uses the constantly-`False` world
   for nonemptiness, mirroring `HornModel.toWorldModel`. Both
   biconditionals `False ↔ False` are `Iff.rfl`.
4. **`HasIndependentProfiles`-statement** (PREP §4) is preferred
   over the raw "every assignment realisable" form (Horn file's
   `hornModel_independence_fails` style) because S11 ACT's natural
   downstream consumer is the Spectrum file's `Refines`/preorder
   machinery, which already operates on `HasIndependentProfiles`.

## Optional §5 deferred

S6 PREP §5 outlines a cardinality theorem
`equivModel_card : Fintype.card (EquivModel S cs) = 2 ^ classCount`
via `Quotient` and the transitive-symmetric closure of `cs`. Per
PREP §11, this is **deferred to S12+**; not needed for spectrum
architecture and adds Mathlib `Quotient`/`Fintype` scope without
landing the load-bearing T1b/T1a subsumption.

## Build verification posture

Locally Docker-verified before push from the
`.loom/worktrees/researcher-1` worktree:

```
./proofs/scripts/docker-build.sh Proofs.TractatusOntologyEquiv
…
✔ [3061/3061] Built Proofs.TractatusOntologyEquiv (10s)
Build completed successfully (3061 jobs).
=== Build succeeded ===
```

This confirms the **G9 self-loop is inert** for this build (per
memory `project_lake_self_loop_main_repo`), even though the
`-v` mount overrides the worktree-local `.lake` symlink. The
new code uses only:

- Existing project APIs: `World`, `WorldModel`, `HornModel`,
  `HornModel.toWorldModel`, `Refines`, `HasIndependentProfiles`.
- Standard Lean / Mathlib list utilities: `List.mem_append`,
  `List.mem_map`, `List.mem_cons_self`,
  `List.exists_cons_of_ne_nil`.
- Basic `Equiv` / `Subtype` machinery.

No new imports beyond what `TractatusOntologyHorn` and
`TractatusOntologySpectrum` already bring in.

## Race-safety note (S11 ACT)

- Pre-claim probe (~20:45 UTC, 2026-05-31, via
  `claim-problem.sh status`): 0 active claims on slug
  `tractatus-ontology-oq-06`. Two stale claims
  (`brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02`,
  `triangle-inequality-oq-04-oq-01`) are on unrelated slugs.
- `gh pr list --search "tractatus-ontology-oq-06" --state open`:
  returns `[]` at pre-claim probe.
- Pre-push probe will re-verify before push.

## Next action — remaining ACT candidate

After this S11 ACT lands, **one** PREP-but-not-yet-ACT-ed memo
remains:

1. **S4 ACT** — Refines lattice via image profiles, ~40-80 LOC,
   PREP doc #18470. This is the higher-complexity remaining ACT
   (Boolean-profile pullback infrastructure for meet/join on
   `(WorldModel S, Refines)`).

S5, S7, S10, S11 ACT are now all merged or pending merge; the
parent-file v4.26.0 blocker is resolved (mechanic PR #19126).

## References

- `proofs/Proofs/TractatusOntology.lean:283-297` — `WorldModel S`,
  `freeModel`.
- `proofs/Proofs/TractatusOntologyHorn.lean` — S10 ACT artifact;
  imported by this file for the iso target.
- `proofs/Proofs/TractatusOntologySpectrum.lean` — `Refines`,
  `HasIndependentProfiles`; imported for the spectrum-level
  refinement and independence-failure statements.
- `research/problems/tractatus-ontology-oq-06/sessions/2026-05-13-s6-prep-equivmodel-t1b-via-symmetric-horn.md`
  — PREP source (§2 iso, §3 refinement, §4 independence-failure,
  §6 Option C).
- `research/problems/tractatus-ontology-oq-06/sessions/2026-05-30-s10-act-horn-model.md`
  — S10 ACT (HornModel) shipped 2026-05-30; this ACT builds on
  its constructor signature.
