# S5 ACT — higher-dim classification axiom (paste from S5 PREP recipe)

**Date**: 2026-06-10
**Researcher**: researcher-8
**Mode**: ACT (Lean file edit + Docker build-verify)
**Phase target**: S5 ACT — discharge the S5 PREP paste-ready axiom signature
**Predecessor**: S5 PREP (#22?, 2026-06-05, `sessions/2026-06-05-s5-prep-conjecture-refinement.md`)

## TL;DR

Pastes the S5 PREP §3.A–E recipe **verbatim** into
`proofs/Proofs/Erdos735OQ04.lean`, adding 4 new class predicates
(`IsCollinearD`, `IsGeneralPositionD`, `IsNearPencilD`,
`IsIncenterConfigD`) plus one `axiom oneflat_classification_higher_dim`.
File grows from 180 LOC to 243 LOC (+63).  Slug acquires its **first
axiom**, satisfying the gallery `status: "axiomatized"` requirement
for the eventual S7 entry.

This iteration's deliverable is the **lowest-risk remaining ACT** per
S5 PREP §7 (no new imports; all bearers already pinned at Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

## 1. Pre-flight checks

| Gate | Status | Notes |
|---|---|---|
| Origin/main commit | 98d1689ec26 | matches base of feature/researcher-8 |
| Disk free | 76 GiB on `/` | well above 1 GiB cascade-safety threshold |
| Docker daemon | alive (Server 29.5.3) | clean handshake |
| Worktree state | clean | no uncommitted edits prior to S5 ACT |
| Sibling activity | none on `Erdos735OQ04.lean` since #21732 (2026-05-31) | safe |
| Parent file stability | last touched #20896 (2026-05-29) | stable |
| Mathlib SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | pinned via lake-manifest |

All GREEN.  ACT proceeds without `(build pending)` qualifier.

## 2. File edits

### 2.1. Header docstring (lines 13-18 → +6 LOC effective)

Update the "This file declares..." summary to reflect the new axiom
and supporting predicates.  No semantic content removed; the previous
"three trivial-case targets" wording becomes "three trivial /
reduction theorems plus one S5 axiom."

### 2.2. New `def`s + `axiom` (insertion between `IsKFlatMagic` and
`zero_flat_magic_trivial`, +57 LOC)

Pasted verbatim from S5 PREP §3.A–E:

- `IsCollinearD`  — 3 LOC body
- `IsGeneralPositionD` — 4 LOC body
- `IsNearPencilD` — 4 LOC body
- `IsIncenterConfigD` — 6 LOC body, with **honest-framing docstring**
  flagging the skeleton-vs-tight-characterisation gap
- `oneflat_classification_higher_dim` — 3 LOC body (the disjunction),
  with full docstring (status, scope, parent-correspondence note)

### 2.3. Footer "future iterations will axiomatise it" → past tense

The header docstring previously said "future iterations will axiomatise
it"; updated to "this file's S5 ACT iteration ships the conjectural
classification."

### 2.4. Total file delta

| Metric | Pre-S5 ACT | Post-S5 ACT | Δ |
|--------|-----------|-------------|---|
| LOC | 180 | 243 | +63 |
| Theorems | 3 | 3 | 0 |
| Defs | 4 | 8 | +4 |
| Axioms | 0 | **1** | **+1** |
| Sorries | 0 | 0 | 0 |
| Imports | 5 | 5 | 0 |

(LOC delta slightly above PREP projection of +40, due to additional
docstrings on the new predicates — semantic delta matches PREP §7's
"+4 defs +1 axiom".)

## 3. Why this iteration is shippable

Per S5 PREP §10 risk register:

| Risk | This iteration's mitigation |
|---|---|
| `IsIncenterConfigD` skeleton is too loose | Documented in the def's own docstring + S5 PREP §3.D + §9; flagged as honest framing for the eventual gallery entry |
| Mathlib v4.26.0 drift before S5 ACT | Pinned SHA `2df2f0150c…` re-checked at ACT time; no drift since 2026-06-05 PREP |
| Parent file changes invalidate `oneflat_eq_parent` | Parent unchanged since #20896 (2026-05-29); S4 ACT untouched |
| `axiom` body fails to elaborate | All 4 disjuncts are `Prop`-valued defs over pinned bearers; no elaborator gymnastics expected |
| Sibling slug ships conflicting axiom | No sibling activity per §1 |

## 4. Docker build-verify

```bash
LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh Proofs.Erdos735OQ04
```

**Expected**: clean (no errors), 3060–3070 jobs (4 new defs are simple
`Prop` bodies; axiom contributes no proof obligations).

**Result**: **clean — 3062/3062 jobs built; 0 errors**.  Only the
pre-existing benign warning `Erdos735Problem.lean:142:5: unused
variable hp` (parent file, not introduced by this S5 ACT — same
warning observed in S4 ACT #21732 and S4 BUILD-VERIFY #20882).
Pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
unchanged.  Build completed in ~330s including cache download (7727
files).  `✔ [3062/3062] Built Proofs.Erdos735OQ04 (87s)` (the leaf
slug build itself was 87s).

## 5. Post-ACT gallery state

The slug's `meta.json` and `src/data/research/problems/erdos-735-oq-04.json`
should be updated in a follow-up iteration to:

- `axiomCount: 0 → 1`
- `assumptions: "1 axiom: oneflat_classification_higher_dim (extension of ABKPR 2008 to ℝᵈ, d ≥ 3, k = 1 case; research-level open).  S5 PREP §3 (2026-06-05) and S5 ACT (2026-06-10) document the structural skeleton vs tight characterisation gap on IsIncenterConfigD."`
- `status: "axiomatized"` (was: TBD pre-S7)
- `badge: "axiom"` (was: TBD pre-S7)

These mutations are part of S7 (gallery integration), out of scope for
this S5 ACT.  This iteration ships only the Lean delta + state.md
sync.

## 6. Next iteration candidates (post-S5 ACT)

Per S5 PREP §7 anti-targets + state.md "Next Action":

- **(b) S6a-ACT** — tetrahedron certificate (PREP at #18486,
  paste-ready, ~80–110 LOC).  Now that `IsKFlatMagic` is defined and
  the higher-dim classification axiom is in place, the tetrahedron
  k = 2 certificate can be cleanly stated.
- **(c) S6b/c-ACT** — octahedron + cube refutations (PREP at #18541).
- **(d) S6e** — general-position uniform-weight theorem for `1 ≤ k ≤ d − 1`
  in ℝᵈ.  Can reuse the new `IsGeneralPositionD` def, though it would
  need a `k`-parameterised variant.  ~40–60 LOC.
- **(e) S7** — gallery integration (`meta.json`, gallery JSON).
- **(f) `IsIncenterConfigD` tightening** — closes the skeleton gap;
  requires Mathlib `ℝᵈ` bisector / insphere API contribution.

**Recommendation**: S6a-ACT next.  It is the next leaf-only ACT with
fully designed PREP (#18486), reuses no new bearers beyond what S5 ACT
just pinned, and unblocks the slug's first concrete k = 2 certificate
demonstration.

## 7. Honesty

This S5 ACT iteration ships:

- 1 Lean file edit: `proofs/Proofs/Erdos735OQ04.lean` (180 → 243 LOC;
  +4 defs, +1 axiom, 0 new sorries)
- 1 new session log (this file)
- 1 state.md update (Phase line, Iteration count, S5 ACT section,
  PR table row)

The S5 axiom `oneflat_classification_higher_dim` is **research-level
open**: no published proof exists for the ℝᵈ extension of ABKPR 2008's
plane case to `d ≥ 3`.  The slug's eventual gallery entry must use
`status: "axiomatized"` (badge `axiom`).

The `IsIncenterConfigD` predicate is a **structural skeleton**, not a
semantically tight `ℝᵈ` characterisation.  This is documented in the
predicate's own Lean docstring, in S5 PREP §3.D, and again in §9 of
this memo.  The skeleton suffices for the S5 axiom to type-check; a
follow-up iteration can tighten it once Mathlib provides `ℝᵈ`
bisector / insphere API.

The conjectural higher-dim 4-class characterisation is the
**formaliser's natural guess**, lifted from ABKPR 2008's planar
result.  No published proof exists for `d ≥ 3` to this formaliser's
knowledge as of 2026-06-10.

## 8. References

- `problem.md` §"Formal Lean target signatures" — original S1 OBSERVE
  axiom sketch with `sorry`-placeholders.
- `sessions/2026-06-05-s5-prep-conjecture-refinement.md` — the
  paste-ready recipe this ACT discharges.
- `proofs/Proofs/Erdos735Problem.lean` lines 74–136 — parent file's
  `IsCollinear`, `IsGeneralPosition`, `IsNearPencil`,
  `IsIncenterConfig`, and `magic_classification` declarations.
- Ackerman, Buchin, Knauer, Pinchasi, Rote (2008), "There are not
  too many magic configurations" — the `d = 2, k = 1` proof
  (axiomatised in parent as `magic_classification`).
- Murty, U.S.R. (1971), "How many magic configurations are there?"
  — original ℝ² conjecture.
- Erdős-problems.com / problem #735 — parent source.
