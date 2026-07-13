# S9 Reconnaissance — Mathlib lookup refinements for the brouwer_fpt lift

**Researcher**: researcher-5
**Date**: 2026-05-08
**Status**: Mathlib lookup intelligence; no Lean changes
**Pattern**: pre-lift reconnaissance (refines `s8-brouwer-extension-via-projection.md`)

## Why this note

S8 (PR #17317, researcher-4) packaged a ready-to-port Lean stub with three
`LOOKUP-N` sorries that S9 was expected to resolve directly. Before lifting
the stub into `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` (which carries
non-trivial regression risk: 2 axioms → 1 axiom, 0 sorries → 3 sorries, with
no in-session build verification due to `feedback_researcher_lake_symlink_broken`
— `proofs/.lake` is a self-cycle and cold-cache Docker builds take 45+ min),
this iteration verifies how *resolvable* each LOOKUP actually is by grepping
the local Mathlib source.

The findings refine the S8 stub's optimism in two ways. LOOKUP-1 is in fact
trivial. LOOKUP-2 is *more* work than S8 suggested (Mathlib gives only
existence/uniqueness of the nearest point, not a packaged continuous projection
function). LOOKUP-3's status depends on the pinned Mathlib version, which
this researcher could not directly verify on disk (only an older v4.10 copy
was accessible; the pinned v4.26 lives behind the broken symlink).

## Important caveat on the Mathlib version checked

The Mathlib copy actually grepped is at
`/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib/`,
which is pinned to **`leanprover/lean4:v4.10.0`**. The lean-genius `proofs`
project is pinned to **`v4.26.0`** (`proofs/lakefile.toml`,
`proofs/lake-manifest.json`: rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

Therefore *absence* findings here are **not authoritative for v4.26** — many
items added between v4.10 and v4.26 will be missing from the copy I grepped.
*Presence* findings are likely stable (these particular lemmas have been in
Mathlib for years).

When a future session has either the v4.26 copy on disk or the broken
`proofs/.lake` symlink repaired, the LOOKUP-3 confirmation step below should
be re-run.

## LOOKUP-1 — bounded set sits inside a closed ball

**Status: CONFIRMED, direct one-line invocation.**

The Mathlib lemma is `Bornology.IsBounded.subset_closedBall_lt`,
defined in `Mathlib.Topology.MetricSpace.Bounded`:

```lean
theorem _root_.Bornology.IsBounded.subset_closedBall_lt
    (h : IsBounded s) (a : ℝ) (c : α) :
    ∃ r, a < r ∧ s ⊆ closedBall c r :=
  let ⟨r, har, hr⟩ := h.subset_ball_lt a c
  ⟨r, har, hr.trans ball_subset_closedBall⟩
```

So the S8 stub line

```lean
obtain ⟨R, hR_pos, hSR⟩ := hS_bounded.exists_pos_subset_closedBall (0 : E)
```

should be replaced by

```lean
obtain ⟨R, hR_pos, hSR⟩ := hS_bounded.subset_closedBall_lt 0 (0 : E)
```

The `0` argument before `(0 : E)` is the lower bound on `r` (we ask for
`r > 0`); the second `0` is the center of the ball. The result is
`∃ r, 0 < r ∧ s ⊆ Metric.closedBall (0 : E) r`. No `sorry` needed.

## LOOKUP-2 — continuous nearest-point projection onto a closed convex set

**Status: PARTIALLY available — only EXISTENCE/UNIQUENESS is packaged. Continuity must be proved separately.**

What Mathlib provides (in `Mathlib.Analysis.InnerProductSpace.Projection`):

```lean
theorem exists_norm_eq_iInf_of_complete_convex
    {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K) (h₂ : Convex ℝ K) :
    ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖
```

This gives an *existence* witness for the nearest-point projection. Pairing
this with strict convexity of `EuclideanSpace ℝ (Fin n)` gives uniqueness, so
classical `Classical.choose` packages the projection as a function `r : E → ↥S`.

**However:** Mathlib does not (in the version verified) bundle this as a
*continuous* function. The continuity of the metric projection onto a closed
convex set in a Hilbert space is a non-trivial theorem in its own right
(standard reference: Conway, *A Course in Functional Analysis*, Theorem 3.14;
the proof goes via the variational inequality
`⟨u - r u, w - r u⟩ ≤ 0  ∀ w ∈ S` plus the parallelogram law). It is not a
one-line `exact?` lookup.

This was understated in the S8 stub. The stub's

```lean
obtain ⟨r, hr_cont, hr_id⟩ :
    ∃ r : E → ↥S, Continuous r ∧ ∀ x : ↥S, r (x : E) = x := by
  sorry  -- proj_convex API (LOOKUP-2)
```

is therefore *not* a routine three-line Mathlib pull but a self-contained
30–80-line lemma that S10 needs to prove, comprising:

1. Define `r : E → ↥S` via `Classical.choose` on
   `exists_norm_eq_iInf_of_complete_convex`.
2. **Prove continuity** of `r` from the variational characterization
   (`norm_eq_iInf_iff_real_inner_le_zero`, which *is* in
   `Mathlib.Analysis.InnerProductSpace.Projection`, line 177-ish: it gives
   the variational inequality used as the standard route to continuity).
3. **Prove idempotency on `↥S`**: `∀ x : ↥S, r (x : E) = x.val` — this is
   one line from uniqueness (the unique nearest point of `S` to a point
   already in `S` is the point itself, since `dist_self` certifies the
   minimum).

**Updated estimate**: LOOKUP-2 is its own multi-step task, not a one-line
Mathlib hit. This may be the dominant work item for the brouwer_fpt
elimination — comparable in size to the S6/S7 graph-form analysis.

## LOOKUP-3 — closed-ball Brouwer at arbitrary radius

**Status: UNVERIFIED for v4.26; absent in v4.10.**

A grep for `brouwer_fixed`, `exists_fixed.*ball`, `fixed.*closedBall`,
`fixedPoint.*closed` (case-insensitive) in the v4.10 Mathlib copy returned
no relevant matches. The only fixed-point hit was
`isClosed_fixedPoints` in `Mathlib.Dynamics.FixedPoints.Topology`, which
is unrelated.

This means **Brouwer FPT was not yet in Mathlib v4.10**. The S8 stub assumes
it is in v4.26 (per the table reference to `Mathlib.Topology.MetricSpace.Brouwer`
in some versions). Two scenarios:

1. **v4.26 has Brouwer FPT, in some module name.** Then LOOKUP-3 is
   resolvable but requires a name-discovery step in a session that has
   either Docker access or a working `.lake` symlink, plus a brief
   rescaling argument from unit-ball to general-radius (homeomorphism via
   `Homeomorph.smul`).

2. **v4.26 still lacks Brouwer FPT entirely.** Then LOOKUP-3 cannot be
   resolved against Mathlib at all, and the brouwer_fpt elimination
   strategy is **blocked at Mathlib level** until Brouwer FPT is upstreamed.
   In that case the gallery-side options are:
   * Keep the axiom indefinitely (current state, no progress).
   * Replace `brouwer_fpt` with a *strictly weaker* axiom that only
     promises Brouwer-on-the-unit-ball, and ship the retraction reduction
     in-house. Net axiom *count* unchanged but axiom *strength* reduced.
   * Build out a Brouwer FPT proof in our own `proofs/` tree (significant
     undertaking; requires algebraic-topology infrastructure).

**The next session should resolve scenario 1 vs 2 first**, before touching
any Lean. A 1-min `grep -r "brouwer\|Brouwer" Mathlib/` against the v4.26
source (in a session that has it) settles the question.

## Recommended S10 plan (refined)

Given the LOOKUP-2 expansion and LOOKUP-3 uncertainty, the refined plan is:

1. **(S10.A, requires Mathlib v4.26 access)** Verify LOOKUP-3 — does
   `Mathlib.Topology.MetricSpace.Brouwer` exist in our pinned Mathlib? If
   yes, note the precise theorem name. If no, decide between strict-weakening
   and in-house proof.
2. **(S10.B, ~50-line lemma)** Prove the continuous-projection lemma
   (`exists_continuous_proj_convex`) inside the gallery's
   `SchauderFixedPointOQ03OQ01.lean` or a new helper file:
   ```lean
   lemma exists_continuous_proj_convex {n : ℕ}
       (S : Set (EuclideanSpace ℝ (Fin n)))
       (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
       ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
         Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x
   ```
   Body uses `exists_norm_eq_iInf_of_complete_convex` for existence,
   strict convexity for uniqueness, the variational inequality for continuity,
   and `dist_self` for idempotency.
3. **(S11)** Once both prerequisites are in place, lift the S8 stub into
   the main file: replace `axiom brouwer_fpt` with the body, applying
   `subset_closedBall_lt` for LOOKUP-1, `exists_continuous_proj_convex`
   for LOOKUP-2, the verified Brouwer name for LOOKUP-3. Docker-verify.
   Sync meta.json `axiomCount 2 → 1`.

## What this iteration adds

* **Confirmation**: LOOKUP-1 is a direct one-line Mathlib invocation
  (`Bornology.IsBounded.subset_closedBall_lt`).
* **Scope correction**: LOOKUP-2 is NOT a single Mathlib lemma in the
  version checked — it requires assembling a `Classical.choose`
  packaging plus a continuity proof from the variational inequality.
  This is an honest expansion of the S9 work item, ~30-80 lines.
* **Open question**: LOOKUP-3's presence in Mathlib v4.26 cannot be
  verified from this environment; flagged for resolution in a session
  with `proofs/.lake` repaired or v4.26 source on disk.
* **Refined S10/S11 plan**: split the brouwer_fpt elimination into
  three discrete steps (Mathlib version probe → continuous projection
  lemma → final lift) with explicit prerequisites.

## What this iteration does NOT do

* Does not modify `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
* Does not commit to a closed-ball Brouwer name (cannot verify v4.26).
* Does not attempt the continuity-of-projection proof (deferred to S10.B).
* Does not touch the harder `approx_selection_exists` axiom.

## References

* `Mathlib.Topology.MetricSpace.Bounded` — confirms LOOKUP-1.
* `Mathlib.Analysis.InnerProductSpace.Projection` lines 64–69 — provides
  existence-only lemma for LOOKUP-2.
* Conway, *A Course in Functional Analysis*, Theorem 3.14 — standard
  reference for continuity of metric projection on closed convex sets in
  Hilbert space.
* `feedback_researcher_lake_symlink_broken.md` — documents why on-machine
  build verification is not feasible in this worktree.
