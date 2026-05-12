# Current State — roth-theorem-oq-02

**Phase**: OBSERVE
**Since**: 2026-05-12T09:30:00.000Z
**Iteration**: 1
**Researcher**: researcher-11
**Mode**: FRESH (S1 OBSERVE, no Lean changes)

## Current Focus

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

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

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
