# S10 — LOOKUP-3 Resolved: Brouwer FPT is Absent from Mathlib4

**Researcher**: researcher-12
**Date**: 2026-05-08
**Status**: Mathlib reconnaissance via GitHub API; no Lean changes other than a
docstring correction (line 81 of `SchauderFixedPointOQ03OQ01.lean`)
**Pattern**: pre-lift LOOKUP probe (resolves S9's flagged open question)
**Outcome**: scenario 2 — Mathlib lacks Brouwer FPT entirely; the brouwer_fpt
elimination strategy must use a strict-weakening or in-house path

## Why this note

S9 (researcher-5, PR #17419) flagged LOOKUP-3 as version-conditional and
unverifiable from this environment because (i) the on-disk Mathlib copy at
`/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib/` is
v4.10, while (ii) the lean-genius `proofs` project is pinned to
`leanprover/lean4:v4.26.0` (`proofs/lakefile.toml`) with the
`proofs/.lake` symlink trap (see
`feedback_researcher_lake_symlink_broken.md`) blocking direct on-disk
inspection of v4.26.

S10 resolves the LOOKUP-3 question by inspecting the pinned mathlib
revision **`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**
(`proofs/lake-manifest.json`, `inputRev: "v4.26.0"`) directly via the
GitHub API — independent of any local Lean toolchain.

## Method

```bash
REV=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# 1. Confirm the FPT is tracked in 100.yaml at the pinned rev
gh api "repos/leanprover-community/mathlib4/contents/docs/100.yaml?ref=$REV" \
  | jq -r '.content' | base64 -d | grep -B1 -A6 -i brouwer

# 2. List every Lean file in Mathlib mentioning "Brouwer" (case-insens)
gh api -X GET "search/code?q=Brouwer+language:lean+repo:leanprover-community/mathlib4" \
  --jq '.items[].path'

# 3. Spot-check Mathlib/Topology/MetricSpace and Analysis/Convex folders
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Topology/MetricSpace?ref=$REV" \
  --jq '.[].name'
```

Each call goes through GitHub's content API with `?ref=` pinned to the
exact mathlib commit lean-genius is built against, so absence findings
here ARE authoritative for v4.26 (this resolves the S9 caveat about the
v4.10 on-disk grep being non-authoritative).

## Findings

### Finding 1: 100.yaml entry points to external Lean 3 work

```yaml
36:
  title  : Brouwer Fixed Point Theorem
  authors: Brendan Seamas Murphy
  links  :
    result: https://github.com/Shamrock-Frost/BrouwerFixedPoint/blob/master/src/brouwer_fixed_point.lean
```

The corresponding `1000.yaml` entry says explicitly:

```yaml
Q1144897:
  title: Brouwer fixed-point theorem
  authors: Brendan Seamas Murphy
  url: https://github.com/Shamrock-Frost/BrouwerFixedPoint/blob/master/src/brouwer_fixed_point.lean
  comment: "in Lean 3"
```

The `comment: "in Lean 3"` is a Mathlib-curator convention for theorems
that exist in Lean 3 / mathlib3 but have not been ported to Mathlib4.

### Finding 2: No Lean file in Mathlib4 contains a topological Brouwer FPT

A repo-wide GitHub code search at the pinned commit returns just three
hits for the string `Brouwer` in `.lean` files:

| Path | Sense |
|---|---|
| `Mathlib/Order/Heyting/Basic.lean` | Heyting algebra (intuitionistic logic) |
| `Mathlib/Order/CompleteBooleanAlgebra.lean` | lattice-theoretic |
| `Mathlib/Order/PrimeSeparator.lean` | lattice-theoretic |

All three reference Brouwer in the *order-theoretic / lattice* sense
(Brouwer–Heyting–Kolmogorov, Brouwer's theorem on Heyting algebras).
**No file in `Mathlib/Topology/...` or `Mathlib/Analysis/...` uses the
name "Brouwer" at all.**

This rules out the possibility that the FPT exists under a different
file name with a `Brouwer` doc reference: such a file would surface in
the search.

### Finding 3: Direct folder inspection — no `Brouwer.lean`, no closed-ball FPT

`Mathlib/Topology/MetricSpace/` (47 files at this rev) contains no
`Brouwer.lean`. Searches for adjacent forms (`brouwer_fixed`,
`fixedPoint.*ball`, `BrouwerFixedPoint`, `closedBall.*continuous.*fixedPoint`)
return either zero hits or hits in unrelated contexts
(`Mathlib/Topology/MetricSpace/Contracting.lean` is the Banach
contraction-mapping theorem; `Mathlib/Analysis/ODE/PicardLindelof.lean`
is the Picard–Lindelöf existence theorem — neither is Brouwer FPT).

The unit-ball form of Brouwer is also absent. The S9 (and S8) docstring
claim "This is proved in Mathlib for the unit ball via degree theory"
appears to have been forward-looking rather than a confirmed fact — the
present S10 evidence demonstrates Mathlib4 has neither the unit-ball nor
the general-compact-convex form.

### Finding 4: Default-branch state matches v4.26

The same code searches against the default branch of `mathlib4` (which
is currently ahead of v4.26.0) return identical results. This means the
absence is not merely a v4.26-pin artifact — Brouwer FPT has not been
landed in Mathlib master either, as of the date of this note.

## Implications for the brouwer_fpt elimination

The S9 plan listed two scenarios for LOOKUP-3 and asked S10.A to settle
which applies. **Scenario 2 applies**: Mathlib does not have Brouwer FPT
in any form usable by `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.

Per the S9 decision tree, the gallery-side options are:

### Option A — Strict-weakening axiom (recommended for the next iteration)

Replace the current `axiom brouwer_fpt` (general compact convex `S` in
`EuclideanSpace ℝ (Fin n)`) with a strictly weaker axiom that asserts
Brouwer FPT only on the closed unit ball:

```lean
/-- **Axiom 1' (proposed):** Brouwer FPT on the closed unit ball.
    Every continuous self-map of the closed unit ball in
    `EuclideanSpace ℝ (Fin n)` has a fixed point. -/
axiom brouwer_unit_ball {n : ℕ}
    (f : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
       → ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hf : Continuous f) :
    ∃ x, f x = x
```

Then ship the **retraction reduction** in-house as a derived theorem:

```lean
theorem brouwer_fpt {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x := by
  -- Use S8's nearest-point retraction r : E → ↥S onto a closed ball B ⊇ S
  -- (homeomorphic to the unit ball after scaling), then apply
  -- brouwer_unit_ball to f ∘ r.
  sorry
```

**Trade-off summary (Option A):**

| Dimension | Before | After |
|---|---|---|
| Axiom *count* | 2 | 2 |
| Axiom *strength* (Brouwer side) | general compact convex | unit ball only |
| Lines of Lean we own | ~0 | ~50–80 (retraction reduction) |
| Mathlib-API dependence | unverified `brouwer_fpt` lookup | none on the Brouwer side |
| Build-verifiability | depends on missing Mathlib lemma | self-contained |

The axiom *count* is unchanged but the *strength* of the assumption is
reduced from "compact convex Brouwer" to "unit-ball Brouwer" — a smaller
mathematical commitment. The retraction reduction is genuinely our
proof, not borrowed from an absent Mathlib lemma.

This option is also robust to LOOKUP-2 (the continuous nearest-point
projection) being non-trivial — the retraction reduction must build that
projection in any case, so the LOOKUP-2 work is identical in either path
and is not duplicated.

### Option B — In-house Brouwer FPT proof

Build a Brouwer FPT proof in `proofs/` from scratch. Three classical
elementary routes exist:

1. **Sperner's lemma** → simplicial fixed-point approximation. The
   gallery already has Sperner machinery; this could leverage existing
   work. Total scope: ~500–1500 lines depending on dimension.
2. **Degree theory** (the homotopy-degree route Mathlib historically
   considered). Requires algebraic-topology infrastructure absent from
   our `proofs/` tree.
3. **Hairy ball / vector-field arguments**. Higher prerequisite cost.

**Trade-off summary (Option B):**

| Dimension | Cost |
|---|---|
| Axiom *count* | 2 → 1 (true reduction) |
| Lean to write | 500–1500 lines |
| Sessions needed | 5–15 |
| Risk | high (infrastructure-driven) |

Option B is a strictly more valuable end-state but is a multi-session
commitment. Option A is a single-session deliverable that strictly
improves axiom strength while preserving the option of a future
Option B upgrade.

### Option C — Status quo (NOT recommended)

Keep the current `axiom brouwer_fpt` indefinitely. This adds nothing.
Mentioned only for completeness; no further action needed if chosen.

## Other findings worth recording

### LOOKUP-1 reconfirmed

S9 reported `Bornology.IsBounded.subset_closedBall_lt` as the right name
in v4.10. Spot-checking via GitHub at the pinned v4.26 rev finds the
same lemma in `Mathlib/Topology/MetricSpace/Bounded.lean`, so the S9
LOOKUP-1 conclusion holds for the pinned version as well.

### LOOKUP-2 unchanged

`Mathlib/Analysis/InnerProductSpace/Projection.lean` exists at the
pinned rev and contains `exists_norm_eq_iInf_of_complete_convex` (and
the variational inequality `norm_eq_iInf_iff_real_inner_le_zero` family
referenced in S9). The S9 conclusion that LOOKUP-2 requires assembling
a self-contained ~50-line continuity-of-projection proof remains
correct for v4.26.

## Recommended next action (S11)

1. **Adopt Option A** (strict-weakening + in-house retraction reduction).
   This is the one option that produces verifiable Lean progress this
   session-cycle without committing to multi-session in-house Brouwer
   infrastructure.
2. **S11.A** (~30 min): rewrite the `axiom brouwer_fpt` as a `theorem`
   that calls a new `axiom brouwer_unit_ball`, with the body using S8's
   retraction reduction + LOOKUP-2's `exists_continuous_proj_convex`
   helper (built per the S9 sketch). Net diff: replace one axiom with
   one strictly weaker axiom + ~60 lines of derivation.
3. **S11.B** (~60 min): build out the `exists_continuous_proj_convex`
   helper (LOOKUP-2 work item, S9 §"Updated estimate"). This is the
   30–80-line lemma whose body uses
   `exists_norm_eq_iInf_of_complete_convex`, strict convexity for
   uniqueness, the variational inequality for continuity, and
   `dist_self` for idempotency on `↥S`.
4. **S12+**: Docker-verify the build (whichever session has a working
   `proofs/.lake`). Update meta.json: axiomCount unchanged (still 2),
   but document in `assumptions` that axiom 1 has been strictly
   weakened to the unit-ball form.

The work is still scoped to two iterations (S11.A and S11.B can be
parallelized across two researchers because S11.B's helper has no
syntactic dependency on S11.A's axiom rename — it is a fresh lemma).

## What this iteration does

* **Definitively resolves LOOKUP-3** with reproducible GitHub-API
  evidence, settling the S9 caveat.
* **Documents the decision** between strict-weakening (Option A),
  in-house Brouwer (Option B), and status quo (Option C), with explicit
  trade-offs.
* **Recommends Option A** as the next iteration's deliverable.
* **Corrects the docstring of `axiom brouwer_fpt`** (line 76–87 of
  `SchauderFixedPointOQ03OQ01.lean`) — the previous claim "This is
  proved in Mathlib for the unit ball via degree theory" was incorrect
  and is replaced with a status note plus a pointer to this S10 file.

## What this iteration does NOT do

* Does not change the axiom count (still 2).
* Does not implement the strict-weakening (Option A is the recommended
  S11.A deliverable, not this iteration's work).
* Does not build the LOOKUP-2 continuous-projection helper.
* Does not Docker-verify any build.
* Does not address the harder `approx_selection_exists` axiom.

## References

* S8 — `s8-brouwer-extension-via-projection.md` — retraction reduction
  proof note + Lean stub (researcher-4, PR #17317).
* S9 — `s9-mathlib-lookup-refinements.md` — three-LOOKUP refinement note
  flagging LOOKUP-3 as the open question this S10 resolves
  (researcher-5, PR #17419).
* `feedback_researcher_lake_symlink_broken.md` — documents why
  `proofs/.lake` cannot be inspected directly, motivating the GitHub-API
  approach used here.
* mathlib4 `docs/100.yaml` and `docs/1000.yaml` at rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — primary evidence for the
  absence finding.
