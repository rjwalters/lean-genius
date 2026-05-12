# Current State — roth-theorem-oq-02

**Phase**: ACT (S2 ACT-A — companion-file axiom-form)
**Since**: 2026-05-12T11:55:00.000Z (S2 ACT-A, researcher-12)
**Iteration**: 2
**Researcher**: researcher-12 (S2); researcher-11 (S1)
**Mode**: ACT (S2 ACT-A companion file)

## Current Focus (S2 ACT-A)

Session 2 (S2 ACT-A, researcher-12, 2026-05-12) follows S1's
recommended path **S2-A** verbatim: create the companion file
`proofs/Proofs/RothTheoremOQ02.lean` with a single `axiom` capturing
the Bloom–Sisask 2020 bound on `rothNumberNat`, plus stable downstream
API names (`blasiConst`, `blasiConst_pos`, `rothNumberNat_le_blasi`)
and a one-line consistency-with-Mathlib export
(`bloom_sisask_consistent_with_isLittleO`, equal to
`rothNumberNat_isLittleO_id` from `Mathlib.Combinatorics.Additive.Corner.Roth`).

The file is ~95 lines (docstring + 5 declarations). The axiom statement
matches the conventions used in the parent gallery file
`Proofs/RothTheoremQuantitative.lean` (`bloom_sisask_bound`) modulo the
project-local `rothNumber` vs Mathlib's `rothNumberNat` — see the
companion-file docstring §"Why This Companion File (Path vs Editing the
Gallery)" for the design rationale.

Deliverables:
* `proofs/Proofs/RothTheoremOQ02.lean` — new file, 1 axiom, 4 supporting
  theorems / defs, 0 sorries.
* `proofs/Proofs.lean` — alphabetical insertion of
  `import Proofs.RothTheoremOQ02` between `RothTheoremAristotle` and
  `RothTheoremOQ03`.
* `src/data/research/problems/roth-theorem-oq-02.json` — iteration 1 → 2,
  status reflects axiomatized companion file.
* `research/problems/roth-theorem-oq-02/state.md` — this update.

## Prior Focus (S1 OBSERVE)

Establish a clean, fact-checked OBSERVE-phase scaffold for the
**Bloom–Sisask bound** `r₃(N) = O(N / (log N)^{1+c})` (arXiv:2007.03528,
2020).

This is a *literature/Mathlib-survey* iteration: it writes no Lean, but it
gives the next session a precise formal target, a Mathlib API snapshot at
pin `2df2f0150c275ad` (Mathlib v4.26.0), and a ranked list of infrastructure
gaps.

## Active Approach

Per the standard *"S1 OBSERVE fallback variant — no Lean changes"* recipe
(memory: `feedback_researcher_12_s22_session_summary.md`,
`feedback_researcher_12_session_summary.md`):

1. `problem.md` — full Plain-language / Formal-statement / Classification /
   Why-this-matters / References / Related-gallery-proofs.
2. `knowledge.md` — historical chronology, Mathlib state at pinned rev,
   missing infrastructure ranked by effort, single-iteration S2 candidates.
3. `state.md` — this file.
4. `src/data/research/problems/roth-theorem-oq-02.json` — gallery research
   entry matching the schema used by sibling
   `roth-theorem-k3-oq-02.json`.

## Mathlib Reality Check (pin `2df2f0150c275ad`, v4.26.0)

- **Exists**: `ThreeAPFree`, `addRothNumber`, `rothNumberNat`,
  `Behrend.box / sphere / map`, Plünnecke–Ruzsa, Ruzsa covering, additive
  energy, approximate subgroups.
- **Module docstring of `AP/Three/Defs.lean`** *explicitly names* the
  Bloom–Sisask target as the expected upper bound on `rothNumberNat`. No
  Lean theorem currently states or proves it.
- **Missing**: Bohr sets, quantitative Bogolyubov on Bohr sets, regularity
  of Bohr sets, density-increment iteration framework, AP3-specific Fourier
  level-set / energy lemmas, any quantitative upper bound on
  `rothNumberNat`.
- **Estimated full-proof Lean effort**: ~2,400 lines across 5–8 PRs (a
  multi-quarter epic, not a single-iteration session).

## Blockers

- **No Mathlib Bohr-set library.** All quantitative `r₃` upper bounds since
  Bourgain (1999) route through Bohr sets; Mathlib has only the
  approximate-subgroup language so far.
- **No quantitative Bogolyubov in Mathlib.** Mathlib has Plünnecke–Ruzsa
  but not the Bohr-set form needed for Sanders / Bloom–Sisask.
- **No density-increment iteration framework.** This is reusable
  infrastructure (k≥3 and beyond); building it is its own project.

These are *infrastructure blockers*, not contradictions — there is no
known obstacle to the Lean formalization, just a lot of prerequisite work.

## Next Action (S2 — choose one)

Per `feedback_researcher_s1_deferred_can_be_false.md`, the S2 plan must
audit any candidate against the cited Mathlib API. Three options ranked by
risk:

- **S2-A (recommended)** — Companion-file *statement only*, axiom-form.
  New file `proofs/Proofs/RothTheoremOQ02.lean` with:
  - imports `Mathlib.Combinatorics.Additive.AP.Three.Defs` and
    `Mathlib.Analysis.SpecialFunctions.Log.Basic`
  - a single `axiom rothNumberNat_bloom_sisask : ∃ c > 0, ∃ N₀, ∀ N ≥ N₀,
        (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c)`
  - a `theorem bloom_sisask_implies_qualitative` consequence: the axiom
    yields `rothNumberNat N / N → 0` (proven from the axiom, ~30 lines).
  - status `"axiomatized"`, badge `"axiom"`, sorries 0, axioms 1.
  Risk: low. Effort: ~80 lines Lean + gallery entry. Lasting value: gives
  the gallery a typed landmark and a target for future infrastructure PRs.

- **S2-B** — Companion-file *statement + Behrend lower-bound consistency
  check*. Same as S2-A plus a theorem
  `bloom_sisask_consistent_with_Behrend`: the asserted upper bound is
  consistent with Behrend's `rothNumberNat n ≥ n · exp(-c · √log n)`
  (i.e. the upper and lower bounds do not cross). About +60 lines.

- **S2-C** — Define `BohrSet T ρ` over `ZMod N`, prove `0 ∈ B(T, ρ)`,
  symmetry, and that `B(T, 1) = univ`. About +200 lines. Higher risk
  (Mathlib's `AddSubgroup`-style API conventions need careful matching);
  more lasting value if it lands cleanly.

Recommended: **start with S2-A**. It is shippable in one session, matches
the Mathlib docstring goal verbatim, and unblocks the next-iteration
plug-in (B → A → core).

## Next Action (S3)

S2 ACT-A shipped the typed axiom-form landmark. The remaining work is
ranked (smallest first):

- **S3-B (consistency check, suggested)** — Add a `bloom_sisask_consistent_with_Behrend`
  theorem stating the axiomatic upper bound is consistent with Behrend's
  lower bound on `rothNumberNat` (i.e. for sufficiently large N, the upper
  and lower bounds do not cross). ~60 lines, requires Behrend infrastructure
  in Mathlib (`Behrend.box / sphere / map` exist, but no explicit
  `rothNumberNat ≥ N · exp(-c · √log N)` theorem is yet packaged in
  Mathlib; would require either an axiom on Behrend or a partial
  derivation from `Behrend.map` injectivity).
- **S3-C (Bohr-set scaffold)** — Define `BohrSet T ρ` over `ZMod N` and
  prove basic structure (0 ∈ B, symmetry, B(T, 1) = univ). About +200
  lines. Higher risk; first step of the multi-quarter infrastructure
  build toward a non-axiomatic Bloom–Sisask.
- **S3-A (qualitative consequence, redundant)** — Derive
  `Tendsto (rothNumberNat N / N) atTop (𝓝 0)` from the S2 axiom.
  Redundant with Mathlib's existing `rothNumberNat_isLittleO_id` (which
  S2's `bloom_sisask_consistent_with_isLittleO` already exposes); not
  recommended.

Recommended: **S3-B**. The Behrend lower bound is already implicit in
Mathlib (`Mathlib.Combinatorics.Additive.AP.Three.Behrend`); making the
non-crossing check explicit is a useful sanity test and motivates the
gap-closing program (Kelley–Meka 2023's `N exp(-c (log N)^{1/12})`
brings the upper bound much closer to Behrend's `N exp(-c sqrt(log N))`).

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE markdown survey, S2 ACT-A companion file)
- Current approach attempts: 1 (companion file with axiom)
- Approaches tried: 1 (axiomatized companion file)

## Notes for Future Sessions

- **Race-safe behavior** — pristine tier-B slugs are not race-safe. Re-check
  `gh pr list --search "roth-theorem-oq-02"` immediately before any push.
- **Pool-file divergence** — live readers consume
  `.lean/state/candidate-pool.json`; the legacy
  `research/candidate-pool.json` is stale. After completing each iteration,
  update via `claim-problem.sh update roth-theorem-oq-02 in-progress`.
- **Do not** add `loom:review-requested` to math-research PRs (the deployer
  merges math PRs directly without Judge review). Content-only labels.
- The parent slug `roth-theorem` has no `openQuestions` array yet, but
  `roth-theorem-k3-oq-01` already *names* Bloom–Sisask as one of four
  formalization targets — a follow-on enrichment iteration could add
  `crossReferences` from there to this slug.
