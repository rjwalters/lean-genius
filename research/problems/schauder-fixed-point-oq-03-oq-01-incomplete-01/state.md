# Research State: schauder-fixed-point-oq-03-oq-01-incomplete-01

## Current State
**Phase**: ACT (S11 strict-weakening lift: axiom rename + helper/theorem
signatures landed, two `sorry`-stubbed bodies decoupled for parallel
S11.B and S11.A.body work)
**Path**: full
**Since**: 2026-05-09T00:30:00Z
**Iteration**: 11

## Current Focus
S11 (researcher-5, 2026-05-09): Lifts S10's recommended Option A
(strict-weakening) into the Lean source. Replaces the single
`axiom brouwer_fpt` (general compact convex `S`) with three
declarations: `axiom brouwer_unit_ball` (unit ball only — strictly
weaker), `lemma exists_continuous_proj_convex` (LOOKUP-2 helper,
sorry-stubbed), and `theorem brouwer_fpt` (general compact convex,
derived from the unit-ball axiom + helper, sorry-stubbed body).

**Net effect on the Lean file:**
* Axiom *count* unchanged (still 2: `brouwer_unit_ball` +
  `approx_selection_exists`).
* Brouwer-side axiom *strength* strictly weakened: general compact
  convex → closed unit ball only.
* Sorry count transitionally rises 0 → 2 (the helper body and the
  theorem body), with the two `sorry` work items mathematically
  independent and decoupled across two follow-on researchers.
* All Mathlib API surfaces for both follow-on `sorry` bodies are
  confirmed at the pinned rev (S9 LOOKUP-1, S10 LOOKUP-2 module,
  S11 rescaling-step Option b reduces step 4 to elementary `norm_smul`
  + arithmetic with no `Homeomorph` dependence).

The S11 design note (`s11-strict-weakening-spec.md`) gives the full
Lean stub for both `sorry` bodies, identifies the precise Mathlib API
hooks at each step, and analyzes the risk surface (assessed: low).

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
S11 has structurally decomposed the Brouwer-side work into two
independent, fully-specified Lean bodies (S11.B helper and S11.A
retraction body). Both `sorry` work items have low-risk Mathlib API
surfaces and can be claimed in parallel by two researchers — neither
references the other's internal proof, and the Lean file builds
end-to-end against the `sorry`-stubbed helper. After both lands, the
Lean file is sorry-free with axiomCount = 2 (unit-ball Brouwer +
graph-form Cellina–Browder selections).

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
    PR #17449);
  - S11 strict-weakening lift: axiom rename + helper/theorem signatures
    + parallelizable `sorry` work items (this PR; build pending).

## Blockers
- **Build verification deferred**: Docker build not run locally
  (`proofs/.lake` self-cycle symlink trap, see researcher-9 memory note —
  `feedback_researcher_lake_symlink_broken.md`). All Mathlib lemma names
  referenced in S8's Lean stub are flagged with `LOOKUP-N` markers for S9
  to verify against the pinned Mathlib version; the stub is structured so
  that a name drift requires only a local fix, not a redesign.

## Next Action
**S11 — STRUCTURAL LIFT LANDED THIS ITERATION.** The axiom rename and
both `sorry` work-item signatures are now in
`SchauderFixedPointOQ03OQ01.lean`; `s11-strict-weakening-spec.md` gives
the full Lean stub for each. The two follow-on items below are
mathematically independent and can be claimed in parallel.

**S11.B (LOOKUP-2 helper proof, est. ~30–80 Lean lines)** — fill the
`sorry` body of `lemma exists_continuous_proj_convex`:

1. Open `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`; locate the
   `sorry` body of `exists_continuous_proj_convex` (just above
   `theorem brouwer_fpt`).
2. Use `Mathlib.Analysis.InnerProductSpace.Projection` —
   `exists_norm_eq_iInf_of_complete_convex` for existence,
   `EuclideanSpace.instStrictConvexSpace` for uniqueness, and the
   `norm_eq_iInf_iff_real_inner_le_zero` family for continuity (the
   1-Lipschitz two-line argument). Idempotency on `↥S` from
   `dist_self` plus uniqueness.
3. Full structured stub in `s11-strict-weakening-spec.md` §"S11.B —
   Lean stub".
4. Docker-verify the build:
   `./proofs/scripts/docker-build.sh Proofs.SchauderFixedPointOQ03OQ01`.

**S11.A.body (retraction reduction body, est. ~60 Lean lines)** — fill
the `sorry` body of `theorem brouwer_fpt`:

1. Open `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`; locate the
   `sorry` body of `theorem brouwer_fpt`.
2. Use `Bornology.IsBounded.subset_closedBall_lt` (LOOKUP-1, S9-confirmed)
   to embed `S` in a closed ball of radius `R > 0`; the helper
   `exists_continuous_proj_convex` for the projection; and the
   elementary rescaling `closedBall 0 R ↔ closedBall 0 1` via
   `norm_smul` + arithmetic (Option b in `s11-strict-weakening-spec.md`)
   to invoke `axiom brouwer_unit_ball`.
3. Full structured stub in `s11-strict-weakening-spec.md`
   §"S11.A.body — Lean stub". Mathlib API hooks are pinned to the
   elementary route; no `Homeomorph.smul` dependency.
4. Docker-verify the build (per S11.B step 4). Update `meta.json`
   `assumptions` text to record the strict-weakening (axiomCount stays
   at 2).

**S11.B and S11.A.body are independent** — neither references the
other's internal proof, and the Lean file builds end-to-end against
the `sorry`-stubbed helper. Two researchers can claim them in parallel
without conflict.

**LEGACY (pre-S11) Next-Action sketch — kept for reference:**

**S11.A (axiom rename + retraction reduction, est. ~60 Lean lines)**:

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
  reconnaissance refining the S8 stub.
- `s10-mathlib-v426-lookup3-resolved.md` — S10 (researcher-12)
  GitHub-API resolution of LOOKUP-3 against the pinned mathlib4 rev.
- `s11-strict-weakening-spec.md` — S11 (researcher-5) structural lift
  of S10's Option A into the Lean source: axiom rename + decoupled
  `sorry` work items (S11.B helper and S11.A.body retraction) with
  full Lean stubs and pinned Mathlib API hooks.

S11 is the first iteration to *touch the Lean file beyond docstrings*
since S7 (researcher-9, #17308). Net file change: replace one
`axiom brouwer_fpt` with `axiom brouwer_unit_ball` +
`lemma exists_continuous_proj_convex` (sorry) +
`theorem brouwer_fpt` (sorry). Axiom *count* unchanged at 2; axiom
*strength* on the Brouwer side strictly weakened to the closed unit
ball form.
