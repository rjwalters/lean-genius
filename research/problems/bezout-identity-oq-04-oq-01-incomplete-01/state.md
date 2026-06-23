# Research State: bezout-identity-oq-04-oq-01-incomplete-01

## Current State
**Phase**: PREP (S3 complete — Mathlib bearer pinned, approach committed)
**Path**: Approach B' (`Submodule.smithNormalForm` bridge); Approach A (constructive Euclidean reduction) fallback
**Since**: 2026-06-10T~00:00Z (S3 PREP, researcher-3); 2026-05-31T06:50:00Z (S2 ORIENT, researcher-1); 2026-04-03T01:04:41-07:00 (scaffold)
**Iteration**: 3

## Current Focus
S3 PREP complete (this session, researcher-3, 2026-06-10, doc-only): cross-referenced
the in-repo audit trail (`MinpolyCharpolyOQ03.lean` lines 38–83 and
`bezout-identity-oq-04-oq-01-oq-01.json` insights) to **pin the Mathlib bearer for
Approach B**. The sibling slug's S11 PREP audit
(`research/problems/minpoly-charpoly-oq-03/sessions/2026-05-13-s11-prep-oq03-oq02-elementary-divisors-erratum.md`,
referenced from the OQ-03 file at line 58–63) already located:

* **`Submodule.smithNormalForm`** at `Mathlib/LinearAlgebra/FreeModule/PID.lean:541`
  — Smith Normal Form of a submodule of a finitely-generated free module over a PID.
* **`Basis.SmithNormalForm`** at the same module — the basis-side variant.
* **`Module.equiv_directSum_of_isTorsion`** at `Mathlib/Algebra/Module/PID.lean:233`
  (witness `p : ι → R` with `Irreducible (p i)` — prime-power decomposition, **not** invariant-factor chain).
* **`Module.equiv_free_prod_directSum`** at the same module — torsion-free splitting.

**Key unblock vs S2 ORIENT**: previously, S2 had Approach B framed as "Mathlib's
PID structure theorem bridge" with uncertain bearer (`Module.equiv_directSum_of_pid`
named speculatively). S3 PREP confirms a *named*, *Matrix-shaped* bearer
(`Submodule.smithNormalForm`) exists at our exact lake-manifest pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, removing the headline S2 blocker.

**The known Mathlib gap (load-bearing for this slug)**: per the OQ-03 audit at
`MinpolyCharpolyOQ03.lean:80–82`, **the diagonal entries of `Submodule.smithNormalForm`
are not certified to satisfy `a 0 ∣ a 1 ∣ ⋯ ∣ a (n-1)`** in Mathlib v4.26.0. Our
parent file's `SmithNormalForm m n` structure *requires* the chain (`hD_div` field,
lines 116–120 of `BezoutIdentityOQ04OQ01.lean`). So Approach B' splits into:

* **B1 (bridge, ~80–120 LOC)**: lift `Submodule.smithNormalForm` to the parent file's
  `SmithNormalForm m n` structure — extract `U, V` from the basis change,
  extract `D` from the certified diagonal entries, populate the `hD_diag` /
  `hU` / `hV` fields. The chain field `hD_div` left as a sub-sorry.
* **B2 (chain certification, ~100–150 LOC, shared gap with `MinpolyCharpolyOQ03`-OQ-02)**:
  prove (or *re-order*) the diagonal entries so they satisfy the chain. This is the
  **same Mathlib gap** that OQ-03 needs for elementary-divisors → invariant-factors
  regrouping. Cross-slug coordination opportunity.
* **B3 (bridge to `isDecompOf`, ~20–40 LOC)**: close the equation `A = U · D · V`.

**Total revised Approach B' LOC budget**: ~200–310 LOC (S2 had estimated ~150–200;
S3 PREP revises upward by accounting for the chain-certification sub-gap, but B1+B3
alone are ~100–160 LOC and viable as a first ACT cycle that leaves `hD_div` as a
single sorry).

**Approach A** remains the fallback (~500 LOC Euclidean reduction with no Mathlib
dependency). **Approach C** remains non-viable (no top-level `Matrix.SmithNormalForm`
at v4.26.0; only `Submodule.smithNormalForm`).

## Active Approach
**Approach B'** (Mathlib `Submodule.smithNormalForm` bridge, **committed by S3 PREP**, ~200–310 LOC total, ~100–160 LOC for first cycle):

* B1 (next S4 ACT cycle, ~80–120 LOC): scaffold a `theorem snf_exists_no_chain`
  bridging `Submodule.smithNormalForm` to `SmithNormalForm m n` with `hD_div`
  as `sorry`. Establishes the `U, D, V` triple and the `isDecompOf` equation
  unconditionally; isolates the divisibility-chain problem.
* B2 (S5 ACT or sibling slug, ~100–150 LOC): chain certification. Cross-slug
  coordination opportunity with `minpoly-charpoly-oq-03-oq-02` (same Mathlib gap).
* B3 (S6 ACT, ~20–40 LOC): combine B1+B2 to discharge the axiom.

**Approach A** (constructive Euclidean reduction, fallback, ~500 LOC):
unchanged from S2; activated only if Approach B' B2 proves intractable.

**Approach C** (defer to upstream Mathlib top-level SNF, ~50 LOC): **still not viable** —
v4.26.0 has `Submodule.smithNormalForm` (submodule-level) but no `Matrix.SmithNormalForm`
top-level theorem packaged for `Matrix (Fin m) (Fin n) ℤ`.

## Attempt Count
- Total attempts: 2 (S2 ORIENT doc-only; this S3 PREP doc-only)
- Current approach attempts: 0 (Approach B' B1 not yet attempted in Lean)
- Approaches tried: 0 Lean attempts; 2 doc surveys

## Blockers
* **Resolved (2026-06-10, S3 PREP)**: "Mathlib PID structure theorem bearer
  uncertain" — pinned to `Submodule.smithNormalForm` at
  `Mathlib/LinearAlgebra/FreeModule/PID.lean:541`.
* **Resolved (2026-05-31, S2 ORIENT)**: "missing problem statement" — recovered
  via parent file survey.
* **Active (load-bearing for B2)**: `Submodule.smithNormalForm` diagonal entries
  not certified to satisfy divisibility chain. Shared gap with
  `minpoly-charpoly-oq-03-oq-02`; both upstreamable to Mathlib.
* **Active (load-bearing for B1)**: bridge from `Submodule`-side
  `Basis.SmithNormalForm` to the parent file's `Matrix (Fin m) (Fin n) ℤ`-side
  `SmithNormalForm m n` structure requires non-trivial basis-coordinate plumbing
  (extract `U` from a basis change, extract `V` similarly). Concrete LOC unknown
  until first ACT cycle.

## What's Built (cumulative)

| Iteration | Deliverable | PR |
|---|---|---|
| S1 (2026-04-03) | Scaffold problem.md (placeholders), knowledge.md (placeholders), state.md, JSON | (unknown / unrecorded) |
| S2 ORIENT (2026-05-31, researcher-1) | Lineage recovery — problem.md rewrite + knowledge.md rewrite + state.md update + JSON update (doc-only) | #21372 |
| S3 PREP (2026-06-10, researcher-3) | Mathlib bearer pinned (`Submodule.smithNormalForm`, `Mathlib/LinearAlgebra/FreeModule/PID.lean:541`); Approach B' committed with B1/B2/B3 sub-steps; cross-slug coordination flagged (shared Mathlib gap with OQ-03-OQ-02); revised LOC budget; problem.md + knowledge.md + state.md + JSON updates (doc-only) | (this PR) |

## Next Action

**S4 ACT cycle 1** (next session, ~1–2 hours, ~80–120 LOC Lean):
1. Create a *new file* `proofs/Proofs/BezoutIdentityOQ04OQ01Snf.lean` (or extend
   the parent file — preference TBD by next session) declaring a helper theorem
   that bridges Mathlib's `Submodule.smithNormalForm` to the parent's
   `SmithNormalForm m n` structure. Goal: a theorem of shape

   ```lean
   theorem snf_exists_no_chain (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
       ∃ U : Matrix (Fin m) (Fin m) ℤ, ∃ D : Matrix (Fin m) (Fin n) ℤ,
       ∃ V : Matrix (Fin n) (Fin n) ℤ,
         IsUnimodular U ∧ IsUnimodular V ∧
         (∀ i j, i.val ≠ j.val → D i j = 0) ∧
         A = U * D * V
   ```

   that discharges everything except the `hD_div` chain field. Use
   `Submodule.smithNormalForm` on `LinearMap.range (Matrix.toLin' A)` (or the
   analogous domain-side construction).

2. If S4 ACT cycle 1 succeeds without `sorry`, the remaining work is **only** the
   `hD_div` chain — which can be either:
   - Discharged here via a re-sorting / re-grouping argument (~100–150 LOC; the
     B2 sub-step), or
   - Tracked as a sibling slug (`bezout-identity-oq-04-oq-01-incomplete-01-oq-01`?)
     so this slug delivers the partial result and the chain is closed separately.

**Race-safety re-check** (this S3 PREP session):
* `gh pr list -R rjwalters/lean-genius --search "bezout-identity-oq-04-oq-01-incomplete-01 in:title" --state open` → 0 open PRs.
* Sole active claim: this session's (researcher-33703).

**No Lean edits** this iteration. Doc-only S3 PREP.

## Session Log

### 2026-06-10 ~00:00 UTC — S3 PREP (researcher-3, doc-only)

* **Mode**: doc-only S3 PREP (zero `*.lean` edits). Files modified:
  `research/problems/bezout-identity-oq-04-oq-01-incomplete-01/problem.md`
  (Approach B → B' refresh with confirmed Mathlib bearer),
  `research/problems/bezout-identity-oq-04-oq-01-incomplete-01/knowledge.md`
  (Mathlib status table refreshed; B1/B2/B3 sub-step decomposition added),
  this `state.md` (S2 ORIENT → S3 PREP, iter 2 → 3),
  `src/data/research/problems/bezout-identity-oq-04-oq-01-incomplete-01.json`
  (`phase` ORIENT → PREP, `currentState.iteration` 2 → 3, blockers refreshed,
  insights and mathlibGaps updated with concrete Mathlib file/line refs).
* **Why**: S2 ORIENT left the Mathlib bearer for Approach B uncertain
  (`Module.equiv_directSum_of_pid` named speculatively). Without a confirmed
  bearer, S4 ACT can't begin. This S3 PREP closes that gap by cross-referencing
  the in-repo audit trail accumulated by other slugs.
* **Cross-reference evidence**:
  - `proofs/Proofs/MinpolyCharpolyOQ03.lean:38–83` — explicit module/line refs
    for the four Mathlib PID-side theorems, including the chain-certification
    gap (`a 0 ∣ a 1 ∣ ⋯` not provided).
  - `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean:240–242` —
    independent audit confirmation of the same three Mathlib theorems
    (`Module.equiv_directSum_of_isTorsion`, `Module.equiv_free_prod_directSum`,
    `Module.exists_ker_toSpanSingleton_eq_annihilator`).
  - `src/data/research/problems/bezout-identity-oq-04-oq-01-oq-01.json`
    `insights` and `nextSteps` — sibling slug (COMPLETED) confirms
    `Basis.SmithNormalForm` and `Submodule.smithNormalForm` are the
    relevant Mathlib API.
* **No Mathlib version drift risk**: lake-manifest pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is the same pin OQ-03's S11 PREP
  audit (2026-05-13) used, and our parent file's `mathlibDependencies` are
  consistent with that pin.
* **Approach commitment**: Approach B' (`Submodule.smithNormalForm` bridge)
  selected as the primary path. Decomposed into B1 (bridge, ~80–120 LOC),
  B2 (chain certification, ~100–150 LOC), B3 (`isDecompOf` close, ~20–40 LOC).
  Approach A remains fallback; Approach C remains non-viable.
* **Cross-slug coordination opportunity flagged**: B2 (divisibility chain
  certification) is the same Mathlib gap that `minpoly-charpoly-oq-03-oq-02`
  needs for elementary-divisors → invariant-factors regrouping. A successful B2
  is upstreamable as a single Mathlib contribution that unblocks both slugs.
* **Tractability re-calibration**: 4 → 5 (S2 → S3 PREP). The confirmed Mathlib
  bearer materially lowers the integration risk; the chain-cert sub-gap is
  bounded (~100–150 LOC) and well-understood (re-ordering / re-grouping).
* **No Lean edits**, no axiom changes, no Docker build, no `meta.json` edits.
* **Race / saturation**: 0 open slug PRs at PR-creation time (verified via
  `gh pr list`); sole active claim is this session's (researcher-33703,
  expires 2026-06-10T10:03:07Z UTC); no overlap risk on doc-only paths.
* **Honest scope**: this iteration converts the slug from "ORIENT — Mathlib
  bearer uncertain" to "PREP — Approach B' committed, B1 scaffold target
  identified". No mathematical advance; no Lean discharge attempted. Future
  S4 ACT cycle is the first Lean-touching session.

### 2026-05-31 ~06:50 UTC — S2 ORIENT (researcher-1, doc-only)

* **Mode**: doc-only S2 ORIENT (zero `*.lean` edits). Files modified:
  `research/problems/bezout-identity-oq-04-oq-01-incomplete-01/problem.md`
  (full rewrite, ~270 LOC; replaces 2026-04-03 scaffold placeholders),
  `research/problems/bezout-identity-oq-04-oq-01-incomplete-01/knowledge.md`
  (full rewrite, ~125 LOC), state.md (full rewrite from iter-1 OBSERVE to
  iter-2 ORIENT), JSON (phase OBSERVE → ORIENT, etc.).
* **Lineage recovery**: surveyed the parent gallery entry
  `bezout-identity-oq-04-oq-01`. Two axioms declared: `snf_exists` (line 146),
  `snf_solvability_criterion` (line 196). The slug name's `incomplete-01`
  suffix maps cleanly to the first axiom.
* **Approach survey**: A (constructive Euclidean reduction, ~500 LOC),
  B (PID structure theorem bridge, ~150–200 LOC, bearer uncertain),
  C (upstream Mathlib SNF dep, ~50 LOC — **not viable** at v4.26.0).
  Recommended: B first, A fallback.
* **Tractability re-calibration**: 6 → 4 reflecting Mathlib API absence and
  ~500 LOC budget.
* No Lean edits; PR #21372 merged.

### 2026-04-03 — S1 OBSERVE (scaffold creation, unknown author)

* Scaffold creation via the curator/seeker pipeline. `problem.md`,
  `knowledge.md`, `state.md`, slug JSON, and `literature/` directory
  all created with placeholder content. The originating prompt or
  user request was not recorded; the only trace is the slug name's
  `incomplete-01` suffix (interpreted in S2 ORIENT as referring to
  the parent file's `snf_exists` axiom).
* No further work between 2026-04-03 and 2026-05-31 (~58 days).

---

## Open Questions for Future Iterations

* **S4 ACT cycle 1**: does the bridge from `Submodule.smithNormalForm` to
  `Matrix.SmithNormalForm m n` (parent file structure) actually fit in
  ~80–120 LOC, or does the basis-coordinate plumbing balloon? Empirical
  answer after first ACT cycle.
* **S4 ACT / S5 ACT decision point**: should B2 (chain certification) be
  attempted in this slug or spun out to a sibling
  (`bezout-identity-oq-04-oq-01-incomplete-01-oq-01`)?
* **Cross-slug Mathlib upstream candidate**: if B2 succeeds, can the chain
  certification be PR'd to Mathlib as a strengthening of
  `Submodule.smithNormalForm` (with the divisibility-chain conclusion added)?
  This would unblock `minpoly-charpoly-oq-03-oq-02` simultaneously.
* **Post-S4-ACT (carried from S2 ORIENT)**: should the constructive proof be
  promoted to Mathlib? The parent file's docstring explicitly notes "~500 lines
  for a full constructive version", so a successful discharge is an upstream
  contribution candidate even via the bridge route.
