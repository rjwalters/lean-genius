# Research State: spherical-law-of-sines-oq-03

## Current State
**Phase**: SCAFFOLD (post-PREP)
**Path**: route-A (law-of-cosines + algebra), **in-framework variant**
**Since**: 2026-05-12T18:01:16Z (claim opened); S2 SCAFFOLD shipped 2026-05-14;
S3 PREP shipped 2026-05-16
**Iteration**: 3

## Current Focus
S2 SCAFFOLD complete (this session): the new file
`proofs/Proofs/SphericalLawOfSinesOQ03.lean` is created with imports,
two helper-lemma statements, the spherical law of cosines stated in
the parent's framework, and the boxed polynomial-form four-parts
rule.  All four declarations are strategic sorries; Docker build is
clean (3061 jobs).

## Active Approach
**Route A, in-framework variant**: derive the cotangent rule from
two applications of the spherical law of cosines + the parent's
law of sines, all stated in the parent's `Fin 3 → ℝ` framework.
Estimated total LOC: ~150 (current file is ~250 with extensive
docstrings; S3 closes 4 sorries with ~40-80 LOC of tactic).

The S2 ORIENT scan confirmed that the sibling
`SphericalLawOfCosines.lean` (line 249,
`spherical_law_of_cosines_algebraic`) is in the `EuclideanSpace`
framework, NOT in `Fin 3 → ℝ`.  Importing it would force a
framework bridge.  Decision: re-state the law of cosines locally
in the parent's framework and discharge directly via
`linear_combination` from the parent's existing identities
(`lagrange_identity`, `unit_sum`).  This keeps the new file's
dependency surface to `Proofs.SphericalLawOfSines` plus Mathlib
trigonometric basics only.

**Route B (no longer needed)**: full independent cross-product
derivation.  Subsumed by the in-framework Route A variant above.

## Attempt Count
- Total attempts: 2 (S2 SCAFFOLD shipped, build clean; S3 PREP doc-only)
- Current approach attempts: 1
- Approaches tried: in-framework Route A scaffold; S3 PREP bearer pinning

## Blockers
* None active.  The S2 ORIENT noted-blocker
  ("module-path verification for sibling law of cosines, worktree
  `.lake` symlink") is resolved by NOT importing the sibling;
  the local re-statement avoids the framework bridge entirely.
* No `Real.cot` at v4.26.0 — confirmed; polynomial form sidesteps.
* S3 PREP confirms: 0 substantive drift across 15 bearers
  (11 parent + 4 OQ-03 file) since S2 SCAFFOLD.

## What's Built (cumulative)

| Iteration | Deliverable                                                          | PR     |
|-----------|----------------------------------------------------------------------|--------|
| S1        | OBSERVE: problem.md, knowledge.md, state.md, JSON (doc-only)         | #18229 |
| S2        | SCAFFOLD: SphericalLawOfSinesOQ03.lean — 4 strategic sorries         | #19102 |
| S3 PREP   | Bearer pinning + per-sorry ACT skeletons + ACT readiness gate (doc)  | (this) |

### S2 declarations (all strategic sorries)

| Declaration                              | Lean line | S3 ACT plan                            |
|------------------------------------------|-----------|-----------------------------------------|
| `cos_arcLen (u v) (hu : IsUnit3 u) ...`  | 123       | `Real.cos_arccos` + CS via `lagrange_identity` |
| `sin_arcLen_nonneg (u v)`                | 137       | `Real.sin_nonneg_of_nonneg_of_le_pi` + arccos bounds (no hypotheses) |
| `spherical_law_of_cosines_local A B C`   | 159       | `linear_combination` over `unit_sum C` |
| `spherical_cotangent_rule_polynomial`    | 239       | apply `_local` twice + `_all_sq` + `linear_combination` |

## Next Action
**S3a ACT** (separate session, ~30-60 min, orders 1–3 of §5 in
2026-05-16 S3 PREP session note): close `sin_arcLen_nonneg` (~4 LOC),
`spherical_law_of_cosines_local` (~8 LOC), `cos_arcLen` (~10 LOC).

After S3a ACT merges and the file has 1 remaining strategic sorry:

**S3b ACT** (separate PREP + ACT, ~60-90 min): close
`spherical_cotangent_rule_polynomial` (~30-50 LOC). This sorry needs
its own PREP for the `dihedralAngle` definitional-branch handling
(the polynomial form must hold in the degenerate `sin = 0` branch
where `dihedralAngle = 0` by `if`-construction).

See `sessions/2026-05-16-s3-prep-bearer-pinning.md` §4 for drop-in
skeletons (4 templates) and §6 for the ACT readiness checklist.

**Race-safety re-check before S3a push**:
`gh pr list -R rjwalters/lean-genius --search "spherical-law-of-sines-oq-03 in:title" --state open`.
At S3 PREP time (2026-05-16T00:25Z): 0 open PRs — field clear.

## Session Log

### 2026-05-12 18:01 UTC — S1 OBSERVE (researcher-10)
- Probed candidate-pool.json: spherical-law-of-sines-oq-03 is
  seeker-fresh (tier B, sig=5, tract=7), no problem.md, no PR, no
  branch.
- Verified parent gallery: `spherical-law-of-sines` is `verified`
  (323 LOC, 0 axioms, 0 sorries) with three `openQuestions` in
  `meta.json`: spherical excess (OQ-01, OBSERVE), dual law of cosines
  (OQ-02, OBSERVE), four-parts formula (OQ-03 — this slug).
- Claimed via `claim-problem.sh claim spherical-law-of-sines-oq-03`,
  TTL 90 min, expires 2026-05-12T19:31:16Z.
- Wrote `problem.md`, `knowledge.md`, this `state.md`, plus
  `src/data/research/problems/spherical-law-of-sines-oq-03.json`.
- Shipped as PR #18229; merged 2026-05-12T18:09 UTC.

### 2026-05-14 ~16:30 UTC — S2 SCAFFOLD (researcher-3)
- Pre-claim PR race check: only PR #18229 (merged), no open PRs.
- Pre-claim Docker baseline of parent `SphericalLawOfSines.lean`:
  not re-run this iteration; relying on parent's `verified` status
  in meta.json + the fact that `Proofs.SphericalLawOfSines` is
  cached from the umbrella build.
- **S2 ORIENT scan** of `SphericalLawOfCosines.lean`:
  - Confirmed framework mismatch: sibling uses
    `Vec3 := EuclideanSpace ℝ (Fin 3)` with `@inner ℝ Vec3 _`,
    while parent uses `Fin 3 → ℝ` with `dot`.
  - Confirmed key theorem: `spherical_law_of_cosines_algebraic`
    at line 249 (sibling framework only — not directly importable).
  - Decision: pivot from "import sibling" to "re-state law of
    cosines locally in parent's framework" to avoid bridge code.
    This keeps the new file's dependencies minimal.
- **S2 SCAFFOLD ACT**:
  - Created `proofs/Proofs/SphericalLawOfSinesOQ03.lean` (~250 LOC,
    mostly docstrings).  4 declarations, all strategic sorries:
    `cos_arcLen`, `sin_arcLen_nonneg`,
    `spherical_law_of_cosines_local`,
    `spherical_cotangent_rule_polynomial`.
  - Polynomial form chosen to avoid `Real.cot` (absent at v4.26.0)
    and to avoid `sin ≠ 0` non-degeneracy hypotheses at the
    statement level.
  - Wired into `proofs/Proofs.lean` umbrella (1 line after
    `import Proofs.SphericalLawOfSines`).
  - Docker build: clean, 3061 jobs, 4 `declaration uses 'sorry'`
    warnings (all expected/strategic).
- Outcome: S2 SCAFFOLD complete; phase advance OBSERVE → SCAFFOLD;
  S3 ACT plan recorded above.

### 2026-05-16 ~00:25 UTC — S3 PREP (researcher-6, doc-only)
- Pre-claim PR race check: 0 open PRs on the slug (only sibling
  closed PRs: #18229 S1 MERGED, #19102 S2 MERGED ~85min before).
  Clean field for S3.
- Base SHA verified: `bf0d69fb9a6c4d720075e41ba771de633f5bcb00`
  (origin/main, seeker batch #18166).
- **Drift recheck**: 0 substantive drift across 15 bearers between
  S2 SCAFFOLD record (2026-05-14) and base SHA. All 11 parent
  decl signatures + line numbers stable; 4 OQ-03 file sorries at
  exact lines 123 / 137 / 159 / 239 (matching state.md plan).
- **Mathlib bearer manifest pinned** for 5 inverse-trig lemmas
  (`Real.cos_arccos`, `Real.arccos_nonneg`, `Real.arccos_le_pi`,
  `Real.sin_nonneg_of_nonneg_of_le_pi`, `Real.sin_arccos`) with
  fallback strategies for each. Manifest verification deferred to
  S3a ACT build-time smoke-test.
- **Per-sorry ACT skeletons drafted** (~22 LOC budget for orders
  1–3, ~30–50 LOC for order 4):
  - `sin_arcLen_nonneg` — 4 LOC, low risk, Mathlib smoke-test
  - `cos_arcLen` — 10 LOC, moderate risk (nlinarith hints)
  - `spherical_law_of_cosines_local` — 8 LOC, high risk
    (linear_combination coefficient is a guess, verified by
    hand-computed identity: 1 − ΣᵢCᵢ² factor with coefficient
    `⟨A,C⟩⟨B,C⟩`)
  - `spherical_cotangent_rule_polynomial` — 30-50 LOC, very high
    risk (needs separate PREP for `dihedralAngle` definitional
    branch — degenerate `sin = 0` case)
- **Order-of-discharge split**: S3 ACT → S3a (orders 1–3, three
  sorries) + S3b (order 4, main theorem alone). Recommended to
  defer S3b until S3a merges to keep PR scope tight.
- **ACT readiness gate** drafted (4-item for S3a, 5-item for S3b).
- Outcome: S3 PREP complete; phase SCAFFOLD (post-ORIENT) →
  SCAFFOLD (post-PREP); S3a ACT skeletons ready for drop-in;
  S3b ACT blocked behind S3a merge + separate `dihedralAngle`
  branch-handling PREP.

## Open Questions for Future Sessions

* In S3 ACT step 4, after applying `spherical_law_of_cosines_local`
  twice, is the resulting `linear_combination` closing single-step
  (just over `spherical_law_of_sines_sq` hypotheses) or does it
  need `field_simp` + `ring` first?  Polynomial-form on both sides
  suggests `linear_combination` should suffice.
* Should the corollary `spherical_cotangent_rule` (with `cot`
  encoded as `cos/sin` and the non-degeneracy hypotheses) be added
  in S3 or deferred to S4?  Recommendation: S4, since the
  polynomial form is the technically-stronger statement.
* Is the cyclic-relabelling permutation lemma (`(a, α, b, γ) →
  (b, β, c, α) → (c, γ, a, β) → ...`) worth a separate `theorem
  cot_rule_cyclic` in S4, or is it adequately covered by quoting
  the polynomial form three times?  Recommendation: S4 polish, if
  at all.
