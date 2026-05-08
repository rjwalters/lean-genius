# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (S9 reconnaissance refines S8 stub; pre-lift name verification)
**Path**: full
**Since**: 2026-05-08T19:50:00Z
**Iteration**: 9

## Current Focus
S9 (researcher-5, 2026-05-08): Pre-lift Mathlib reconnaissance for the
brouwer_fpt elimination. Greps the on-disk Mathlib (v4.10 copy at
`/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib/`) for
the three `LOOKUP-N` names from S8's Lean stub. Findings refine the S8
optimism in two material ways:

* **LOOKUP-1 — confirmed direct.** `Bornology.IsBounded.subset_closedBall_lt`
  is the right Mathlib lemma; the stub line replaces with a one-liner.
* **LOOKUP-2 — scope expanded.** Mathlib gives only existence/uniqueness of
  the nearest point (`exists_norm_eq_iInf_of_complete_convex` in
  `Mathlib.Analysis.InnerProductSpace.Projection`). A *continuous*
  projection function with idempotency on `S` is NOT packaged; assembling it
  is its own ~30–80-line lemma using the variational inequality plus
  `dist_self` for idempotency. This was understated in the S8 stub.
* **LOOKUP-3 — version-conditional.** The verified Mathlib copy is v4.10,
  pinned project Mathlib is v4.26. Brouwer FPT is absent in v4.10; presence
  in v4.26 cannot be verified from this worktree (the `proofs/.lake`
  self-cycle symlink trap, see `feedback_researcher_lake_symlink_broken.md`,
  blocks direct on-disk inspection). Flagged for the next session with
  v4.26 access.

S8 (researcher-4, 2026-05-08): retraction-based proof note for `brouwer_fpt`.
The note (`s8-brouwer-extension-via-projection.md`) sets up the nearest-point
projection `r : E → ↥S` from `EuclideanSpace ℝ (Fin n)` onto the compact
convex `S`, factors any `f : ↥S → ↥S` through a closed ball `B ⊇ S`, and
reduces the general case to Mathlib's unit-ball Brouwer FPT via the standard
"retract of an FPP space has FPP" folklore (Smart 1980 §1.3, Granas–Dugundji
2003 §0.4 Thm 4.6). A ready-to-port Lean stub with three localized
`LOOKUP-N` sorries.

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
**S10.A (Mathlib v4.26 LOOKUP-3 probe — requires `proofs/.lake` repaired or
v4.26 copy on disk)**:

1. `grep -r "Brouwer\|brouwer" Mathlib/` against the pinned-version source.
2. If a closed-ball Brouwer FPT theorem exists, record its precise name in
   the `s9-mathlib-lookup-refinements.md` note (LOOKUP-3 section) and
   proceed to S10.B.
3. If not, decide between (a) shipping the retraction reduction with a
   strictly weaker `axiom brouwer_unit_ball` (axiom-count neutral, axiom-
   strength reduced), or (b) building a Brouwer FPT proof in our `proofs/`
   tree (significant scope; algebraic-topology infrastructure required).

**S10.B (continuous-projection lemma, ~30–80 lines)**:

1. Add a helper lemma (likely in
   `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` or a new helper file):
   ```lean
   lemma exists_continuous_proj_convex {n : ℕ}
       (S : Set (EuclideanSpace ℝ (Fin n)))
       (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
       ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
         Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x
   ```
2. Existence via `exists_norm_eq_iInf_of_complete_convex` plus uniqueness
   from strict convexity, then `Classical.choose` packaging.
3. Continuity from the variational inequality
   (`norm_eq_iInf_iff_real_inner_le_zero` family in
   `Mathlib.Analysis.InnerProductSpace.Projection`).
4. Idempotency on `↥S` from `dist_self` + uniqueness.

**S11 (lift the brouwer_fpt stub once both prerequisites land)**:

1. Open `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
2. Replace `axiom brouwer_fpt …` with `theorem brouwer_fpt … := by` and
   paste the body from `s8-brouwer-extension-via-projection.md`
   §"A Lean stub", with these substitutions:
   - **LOOKUP-1**: replace `hS_bounded.exists_pos_subset_closedBall (0 : E)`
     with `hS_bounded.subset_closedBall_lt 0 (0 : E)`.
   - **LOOKUP-2**: replace the `sorry` block with
     `exists_continuous_proj_convex S hS_ne hS_compact hS_convex`.
   - **LOOKUP-3**: invoke the verified Brouwer name + `Homeomorph.smul`
     rescaling if only unit-ball form is in Mathlib.
3. Docker-verify the build:
   `./proofs/scripts/docker-build.sh Proofs.SchauderFixedPointOQ03OQ01`.
4. After build VERIFIED, sync meta.json: axiomCount 2 → 1, status remains
   `axiomatized` (one axiom — `approx_selection_exists` — still pending).

**S12+** (the harder axiom): PartitionOfUnity proof of the graph form of
`approx_selection_exists`, per s6/s7 plan.

## Open files
- `s6-axiom-counterexample.md` — counterexample for the pointwise selection.
- `s8-brouwer-extension-via-projection.md` — S8 (researcher-4) retraction
  proof note + Lean stub for the Brouwer extension.
- `s9-mathlib-lookup-refinements.md` — S9 (researcher-5) Mathlib
  reconnaissance refining the S8 stub: confirms LOOKUP-1, expands
  LOOKUP-2 scope, flags LOOKUP-3 for version-conditional resolution.

All are research artifacts the way S6 was — pure analysis, no Lean changes,
intended to set up the next implementation iteration with minimal in-session
design risk.
