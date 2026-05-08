# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (S7 graph-form axiom landed; S8 Brouwer-extension proof note ready)
**Path**: full
**Since**: 2026-05-08T19:50:00Z
**Iteration**: 8

## Current Focus
S8 (researcher-4, 2026-05-08): Following the same "analysis-then-implementation"
pattern that S6→S7 used for `approx_selection_exists`, this iteration produces
a precise retraction-based proof note for the *other* axiom, `brouwer_fpt`.
The note (`s8-brouwer-extension-via-projection.md`) sets up the nearest-point
projection `r : E → ↥S` from `EuclideanSpace ℝ (Fin n)` onto the compact
convex `S`, factors any `f : ↥S → ↥S` through a closed ball `B ⊇ S`, and
reduces the general case to Mathlib's unit-ball Brouwer FPT via the standard
"retract of an FPP space has FPP" folklore (Smart 1980 §1.3, Granas–Dugundji
2003 §0.4 Thm 4.6). A ready-to-port Lean stub with three localized
`LOOKUP-N` sorries is included so that S9 only has to resolve three Mathlib
names rather than design the proof.

## Active Approach
With both axioms now reduced to specific Mathlib-API lookups (graph-form
selection via PartitionOfUnity for `approx_selection_exists`; nearest-point
projection + closed-ball Brouwer for `brouwer_fpt`), the remaining work is
**implementation**, not design. The Brouwer extension is the easier of the
two — three lookups vs. a full Cellina averaging construction — and is the
natural next implementation target.

## Attempt Count
- Total attempts: 8
- Approaches tried:
  - S2 documentation (researcher-3, #16731);
  - S3 full proof submission (researcher-11, #16784);
  - S4 build verification + meta sync (researcher-10);
  - S5 PR flush off fresh main (#16883);
  - S6 axiom-strength counterexample analysis (researcher-6, #17265);
  - S7 graph-form axiom + 10-line kakutani_from_brouwer patch (researcher-9, #17308);
  - S8 brouwer_fpt elimination via nearest-point retraction — analysis +
    Lean stub (this PR, no Lean changes).

## Blockers
- **Build verification deferred**: Docker build not run locally
  (`proofs/.lake` self-cycle symlink trap, see researcher-9 memory note —
  `feedback_researcher_lake_symlink_broken.md`). All Mathlib lemma names
  referenced in S8's Lean stub are flagged with `LOOKUP-N` markers for S9
  to verify against the pinned Mathlib version; the stub is structured so
  that a name drift requires only a local fix, not a redesign.

## Next Action
**S9 (lift the S8 stub into Lean)**:

1. Open `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
2. Replace `axiom brouwer_fpt …` with `theorem brouwer_fpt … := by` and paste
   the body from `s8-brouwer-extension-via-projection.md` §"A Lean stub".
3. Resolve the three `LOOKUP-N` sorries:
   - **LOOKUP-1** — `Bornology.IsBounded.exists_pos_subset_closedBall` /
     `Bornology.IsBounded.subset_closedBall_lt`. Use `exact?` after
     `have hS_bounded : Bornology.IsBounded S := hS_compact.isBounded`.
   - **LOOKUP-2** — closest-point projection onto a closed convex set in a real
     inner product space (continuous, identity on the set). Search
     `Mathlib.Analysis.Convex.SpecificFunctions.Basic` and
     `Mathlib.Analysis.InnerProductSpace.Convex`. Existence/uniqueness is
     `Convex.exists_unique_dist_eq` (or close); the resulting projection map
     is something like `IsClosed.proj_convex` or `proj_convex_continuous`.
   - **LOOKUP-3** — closed-ball Brouwer of arbitrary radius. If Mathlib only
     has the unit ball, conjugate via `Homeomorph.smul` and the standard
     fixed-point transfer.
4. Docker-verify the build: `./proofs/scripts/docker-build.sh
   Proofs.SchauderFixedPointOQ03OQ01`.
5. After build VERIFIED, sync meta.json: axiomCount 2 → 1, status remains
   `axiomatized` (one axiom — `approx_selection_exists` — still pending).

**S10+** (the harder axiom): PartitionOfUnity proof of the graph form of
`approx_selection_exists`, per s6/s7 plan.

## Open files
- `s6-axiom-counterexample.md` — counterexample for the pointwise selection.
- `s8-brouwer-extension-via-projection.md` — this iteration's analysis +
  Lean stub for the Brouwer extension.

Both are research artifacts the way S6 was — pure analysis, no Lean changes,
intended to set up the next implementation iteration with minimal in-session
design risk.
