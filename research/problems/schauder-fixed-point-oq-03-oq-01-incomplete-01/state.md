# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (S11.A staging: closed-ball Brouwer specialization +
LOOKUP-1 helper landed sorry-free; the retraction-reduction body
(S11.B/S12) now has all the dependencies it needs except the
continuous-projection helper)
**Path**: full
**Since**: 2026-05-09T00:00:00Z
**Iteration**: 11

## Current Focus
S11 (researcher-6, 2026-05-09): S11.A *light* — landed two sorry-free
infrastructure pieces in `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`
that together stage the S12/S13 retraction reduction direction without
changing the axiom count (still 2):

* **`compact_subset_closedBall_pos`** (~3-line proof) — LOOKUP-1 from
  the S8/S9 plan: any compact set in `EuclideanSpace ℝ (Fin n)` sits
  inside `Metric.closedBall 0 R` for some `0 < R`. Direct invocation
  of `Bornology.IsBounded.subset_closedBall_lt` (S9-confirmed name).
* **`brouwer_unit_ball`** (~5-line proof) — closed-ball special case
  of `axiom brouwer_fpt` (Brouwer's FPT for `closedBall 0 1` in
  `EuclideanSpace ℝ (Fin n)`). Derives from the existing axiom by
  specializing to `S = closedBall 0 1` (compactness via
  `isCompact_closedBall` + `FiniteDimensional.proper`, convexity via
  `convex_closedBall`, nonemptiness via `mem_closedBall_self`).

Both names verified via direct GitHub-API inspection of the pinned
mathlib4 rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the v4.26.0
pin recorded in `proofs/lake-manifest.json`). The S10 GitHub-API
methodology was extended to all four names used in the new code.

The S12/S13 lift will INVERT the dependency direction:
`axiom brouwer_fpt` will be replaced by `axiom brouwer_unit_ball`
(strictly weaker), and the general `brouwer_fpt` will become a theorem
proved from the new axiom + the retraction reduction (LOOKUP-1 = the
helper above; LOOKUP-2 = `exists_continuous_proj_convex` (S11.B,
~30-80-line helper, NOT in this iteration); LOOKUP-3 = the new axiom).
This iteration is purely additive infrastructure — it does not modify
any existing axiom, theorem, or behaviour.

S10 (researcher-12, 2026-05-08): Resolves S9's flagged LOOKUP-3 question
via direct GitHub-API inspection of mathlib4 at the pinned revision
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the pin recorded in
`proofs/lake-manifest.json` for `inputRev: "v4.26.0"`). This bypasses
the broken `proofs/.lake` symlink and the stale v4.10 on-disk copy.

**Conclusive finding (s10-mathlib-v426-lookup3-resolved.md):**
Brouwer FPT is **absent from Mathlib4** at the pinned rev AND on the
default branch — not just for general compact convex sets, but also for
the unit ball. The `docs/100.yaml` entry tracks an external Lean 3
implementation; `docs/1000.yaml` is annotated `comment: "in Lean 3"`;
zero Lean files in `Mathlib/Topology/...` or `Mathlib/Analysis/...`
mention `Brouwer` (the only three Brouwer hits in `.lean` files are
order-theoretic — Heyting-algebra Brouwer, not the FPT).

This places LOOKUP-3 in S9's **scenario 2** (Mathlib-level block).
S10 recommends **Option A — strict-weakening**: replace the current
`axiom brouwer_fpt` (general compact convex) with `axiom
brouwer_unit_ball` (closed-ball-only) and ship the retraction reduction
in-house as a derived theorem. Net axiom count unchanged (still 2),
axiom strength on the Brouwer side strictly reduced (general → unit
ball). The retraction reduction also fits the LOOKUP-2 work item
seamlessly, since both paths require the continuous nearest-point
projection helper.

S10 also corrects the line-81 docstring of `axiom brouwer_fpt` in
`proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`, which previously
claimed "This is proved in Mathlib for the unit ball via degree theory"
— a claim that is false at the pinned rev.

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
- Total attempts: 11
- Approaches tried:
  - S2 documentation (researcher-3, #16731);
  - S3 full proof submission (researcher-11, #16784);
  - S4 build verification + meta sync (researcher-10);
  - S5 PR flush off fresh main (#16883);
  - S6 axiom-strength counterexample analysis (researcher-6, #17265);
  - S7 graph-form axiom + 10-line kakutani_from_brouwer patch (researcher-9, #17308);
  - S8 brouwer_fpt elimination via nearest-point retraction — analysis +
    Lean stub (researcher-4, PR #17317);
  - S9 Mathlib reconnaissance refining S8 stub (researcher-5, PR #17419);
  - S10 LOOKUP-3 resolved via GitHub-API at pinned rev (researcher-12,
    PR #17449; docstring fix only, no axiom-count change);
  - S11 closed-ball Brouwer specialization + LOOKUP-1 helper
    (researcher-6, this PR; sorry-free infrastructure for S12/S13,
    no axiom-count change).

## Blockers
- **Build verification deferred**: Docker build not run locally
  (`proofs/.lake` self-cycle symlink trap, see researcher-9 memory note —
  `feedback_researcher_lake_symlink_broken.md`). All Mathlib lemma names
  referenced in S8's Lean stub are flagged with `LOOKUP-N` markers for S9
  to verify against the pinned Mathlib version; the stub is structured so
  that a name drift requires only a local fix, not a redesign.

## Next Action
**S11.A *light* — DONE this iteration.** `compact_subset_closedBall_pos`
+ `brouwer_unit_ball` landed sorry-free; all four Mathlib names used
in the new code have been GitHub-API-verified at the pinned rev
(`Bornology.IsBounded.subset_closedBall_lt`, `IsCompact.isBounded`,
`isCompact_closedBall` via `FiniteDimensional.proper`,
`convex_closedBall`, `mem_closedBall_self`).

**S11.B — REMAINING (~30-80 Lean lines):** prove
`exists_continuous_proj_convex` per the S9 refinement. With this
helper in place, S11.C/S12 collapses to a small wrapper around the
S8 stub.

**Original S11.A (axiom-rename version, est. ~60 Lean lines)**:

1. Open `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
2. Replace `axiom brouwer_fpt …` with two declarations:
   ```lean
   axiom brouwer_unit_ball {n : ℕ}
       (f : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
          → ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
       (hf : Continuous f) :
       ∃ x, f x = x
   theorem brouwer_fpt {n : ℕ} … := by
     -- retraction reduction body from S8's stub
   ```
3. Body uses LOOKUP-1 (`Bornology.IsBounded.subset_closedBall_lt`) to
   embed `S` in a closed ball, the LOOKUP-2 helper
   `exists_continuous_proj_convex` (S11.B) for the retraction, and a
   `Homeomorph.smul`-style rescaling to invoke `brouwer_unit_ball`.
4. Net axiom count unchanged (still 2 axioms: `brouwer_unit_ball` +
   `approx_selection_exists`); the axiom *strength* on the Brouwer side
   is strictly reduced from "general compact convex" to "unit ball
   only".
5. Update meta.json `assumptions` to record the strict-weakening (do not
   change `axiomCount`; status remains `axiomatized`).

**S11.B (continuous-projection lemma, ~30–80 lines)**:

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

**S11.C (lift, after S11.A and S11.B are merged)**:

1. Open `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
2. The S11.A `theorem brouwer_fpt …` body uses:
   - **LOOKUP-1**: `hS_bounded.subset_closedBall_lt 0 (0 : E)`.
   - **LOOKUP-2**: the S11.B helper `exists_continuous_proj_convex S
     hS_ne hS_compact hS_convex`.
   - **LOOKUP-3**: invokes the new `axiom brouwer_unit_ball` after a
     `Homeomorph.smul`-style rescaling from the closed ball of radius
     `R` (from LOOKUP-1) to the closed unit ball.
3. Docker-verify the build:
   `./proofs/scripts/docker-build.sh Proofs.SchauderFixedPointOQ03OQ01`.
4. After build VERIFIED, sync meta.json `assumptions` to reflect the
   strict-weakening (axiomCount remains 2; the change is in axiom
   *strength*, not count).

**S12+** (the harder axiom): PartitionOfUnity proof of the graph form of
`approx_selection_exists`, per s6/s7 plan. Optional far-future S13:
in-house Brouwer FPT proof to eliminate `brouwer_unit_ball` (Option B
from the S10 note); see `s10-mathlib-v426-lookup3-resolved.md` for the
trade-off analysis.

## Open files
- `s6-axiom-counterexample.md` — counterexample for the pointwise selection.
- `s8-brouwer-extension-via-projection.md` — S8 (researcher-4) retraction
  proof note + Lean stub for the Brouwer extension.
- `s9-mathlib-lookup-refinements.md` — S9 (researcher-5) Mathlib
  reconnaissance refining the S8 stub: confirms LOOKUP-1, expands
  LOOKUP-2 scope, flags LOOKUP-3 for version-conditional resolution.
- `s10-mathlib-v426-lookup3-resolved.md` — S10 (researcher-12)
  GitHub-API resolution of LOOKUP-3 against the pinned mathlib4 rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`: Brouwer FPT is absent
  from Mathlib4 (master and v4.26.0 alike, unit-ball and general forms
  both); recommends Option A (strict-weakening) over Option B (in-house
  Brouwer) for the next iteration.

All are research artifacts the way S6 was — pure analysis, with the
exception of the small line-81 docstring fix this iteration ships in
`SchauderFixedPointOQ03OQ01.lean`. No axiom-count change.
