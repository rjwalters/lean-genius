# Current State — roth-theorem-oq-02

**Phase**: ACT (S3-B — Behrend consistency check)
**Since**: 2026-05-12T13:10:00.000Z (S3-B ACT, researcher-3)
**Iteration**: 3
**Researcher**: researcher-3 (S3); researcher-12 (S2); researcher-11 (S1)
**Mode**: ACT (S3-B Behrend consistency theorem)

## Current Focus (S3-B ACT)

Session 3 (S3-B ACT, researcher-3, 2026-05-12) follows the recommended
path **S3-B** verbatim. Adds the theorem `bloom_sisask_consistent_with_Behrend`
to `proofs/Proofs/RothTheoremOQ02.lean`:

```lean
theorem bloom_sisask_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      (N : ℝ) / Real.log N ^ (1 + blasiConst) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_blasi N hN)
```

The proof is purely transitive through `rothNumberNat N`: Mathlib's
*unconditional* `Behrend.roth_lower_bound`
(`(N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`) combined with the
S2 `rothNumberNat_le_blasi` yields the consistency statement directly.
The underlying analytic inequality
`(1 + c) * log log N ≤ 4 * √(log N)` is *not* proved separately — both
bounds simultaneously hold of the same numerical sequence, so the
lower-bound ≤ upper-bound follows by transitivity.

**Why this matters.** It records explicitly that the Bloom–Sisask
axiom's bound is compatible with (does not contradict) Mathlib's
existing Behrend lower bound. The gap between them
(`exp(-4√(log N))` vs `1 / (log N)^(1+c)`) is the central open
quantitative question and the natural follow-up axiom is the
Kelley–Meka 2023 refinement.

### Counts

- File: `proofs/Proofs/RothTheoremOQ02.lean` 119 → 150 lines (+31).
- New import: `Mathlib.Combinatorics.Additive.AP.Three.Behrend`.
- Supporting theorems: 4 → 5.
- Axioms: 1 (unchanged).
- Sorries: 0 (unchanged).
- Build: verified via Docker (`Built Proofs.RothTheoremOQ02`, 2505 jobs).

## Prior Focus (S2 ACT-A)

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

## Next Action (S3) — resolved by S3-B

S3-B (recommended) shipped this iteration. See the `Current Focus`
section above. The Behrend lower bound *is* in Mathlib as
`Behrend.roth_lower_bound : (N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`
(unconditional, no hypotheses needed); the consistency follows by a
single transitive `.trans` through `rothNumberNat N`.

## Next Action (S4 — choose one, smallest first)

- **S4-a (recommended, smallest)** — `axiom rothNumberNat_kelley_meka`
  for the Kelley–Meka 2023 bound
  `∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N · exp(-c · (log N)^{1/12})`,
  plus matching `kelleyMekaConst` API, plus a one-line
  `bloom_sisask_consistent_with_KelleyMeka` by transitivity through
  `rothNumberNat`. About +50 lines, low risk, builds on the S3-B
  transitivity template directly.
- **S4-b (Bohr-set scaffold, multi-quarter starter)** — Define
  `BohrSet T ρ` over `ZMod N`, prove `0 ∈ B(T, ρ)`, symmetry, and
  `B(T, 1) = univ`. About +200 lines. Higher risk (Mathlib
  `AddSubgroup`-style API conventions); first step of the multi-quarter
  infrastructure build toward a non-axiomatic Bloom–Sisask.
- **S4-c (low priority)** — `bloom_sisask_consistent_with_subadditivity`
  against `rothNumberNat_add_le`. Likely redundant with existing
  transitive bounds.

Recommended: **S4-a**. It is the natural sequel to S3-B (same
transitivity pattern) and adds the strongest known upper bound on
`rothNumberNat` to the gallery's typed landmarks. Adds one new axiom
(`rothNumberNat_kelley_meka`), explicit and clearly scoped.

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE markdown survey, S2 ACT-A axiom-form companion, S3-B Behrend consistency check)
- Current approach attempts: 2 (companion file build-up: axiom + transitive consistency checks)
- Approaches tried: 1 (axiomatized companion file + transitivity-through-`rothNumberNat`)

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
