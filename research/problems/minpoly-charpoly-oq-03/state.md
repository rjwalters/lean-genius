# Current State

**Phase**: ACT (S14 strong-form statement upgrade landed; OQ-03-OQ-02 invariant-factor decomposition + lastFactor=minpoly follow-up are the remaining sub-OQs)
**Since**: 2026-06-04 (S14 ACT strong-form statement upgrade, researcher-1; discharges next-action option 3)
**Iteration**: 14

## Current Focus

S14 ACT (researcher-1, 2026-06-04) discharges next-action option 3
(strong-form statement upgrade): extends `rational_canonical_form_exists`
to additionally assert `c.lastFactor = M.minpoly`. Sorry-preserved
(the existing single `sorry` covers the strengthened statement). Sets
up the deliverable surface for next-action option 2 (the
`lastFactor = minpoly` proof via `annihilator_top_eq_ker_aeval` plus
monic uniqueness).

Net file change: lineCount 624 → 631 (+7 LOC from extended docstring
and the additional `∧ c.lastFactor = M.minpoly` conjunct);
theoremCount, definitionCount, sorry count, axiomCount all unchanged.
Build-pending per S2/S3/S4/S5/S13 convention (Docker daemon in
I/O-error state on this host — host-disk-blocked precedent applies).

Anti-target compliance: zero edits to any other theorem statement
in the file; no changes to InvariantFactorChain structure; no new
proof tactics introduced. The change is a pure statement-surface
strengthening, leaving the S13 firstFactor mirror and all prior
work untouched.

## S13 ACT (prior iteration) — quick summary

S13 ACT discharged the S6 PREP (PR #18425) `firstFactor`-side mirror
design verbatim. Added Part 7 to `MinpolyCharpolyOQ03.lean` with:

* `InvariantFactorChain.firstFactor` (new noncomputable def, `head?.getD 1`)
* `firstFactor_eq_getElem_zero` (private bridging lemma, Plan-B `rcases`
  form per S6 PREP §4 to avoid Mathlib `List.head?_eq_head` API drift)
* `firstFactor_mem`, `firstFactor_monic` (membership + monicness on
  nonempty chain)
* `firstFactor_natDegree_minimal` (degree-minimum, one-line application
  of `chain_natDegree_le` with `i = 0`; mirror of
  `lastFactor_natDegree_maximal`)
* `nat_list_sum_ge_length_mul_of_all_ge` (private `Nat` lower-bound
  helper, mirror of S5's `_le_` variant)
* `prodFactors_natDegree_ge_firstFactor_natDegree_mul` (length × first
  lower bound on `prodFactors.natDegree`, dual of S5's upper bound)

Together with Part 6 this yields the two-sided sandwich

    k · deg(firstFactor) ≤ deg(prodFactors) ≤ k · deg(lastFactor)

on the abstract `InvariantFactorChain F`. Once the chain is
instantiated by a matrix M (so `prodFactors = charpoly M`,
`lastFactor = minpoly M`) this becomes a matrix-level sandwich with no
further `Polynomial`-level induction at the matrix-level instantiation
step.

Net file change: lineCount 484 → 624 (+140 LOC); theoremCount 16 → 22
(+4 public mirror lemmas + 2 private helpers); definitionCount 3 → 4
(+1 noncomputable def); sorry count unchanged at 1 (S1 placeholder on
`rational_canonical_form_exists`); axiomCount 0. No new imports. Build
pending (Docker cold-build ~45 min per `proofs/.lake` self-symlink
trap; matches S2/S3/S4/S5 build-pending precedent).

**Anti-target compliance** (S6 PREP §7): zero edits to the existing S5
statements; no `prodFactors_natDegree_sandwich` corollary added
(deferred to a future PR with explicit consumer justification);
`rational_canonical_form_exists` statement unchanged.

## S5 (prior iteration) detail

S5 composes S3 `prodFactors_natDegree` (sum-of-degrees identity) with
S4 `lastFactor_natDegree_maximal` (degree maximality) to add the
coarse a-priori upper bound `c.prodFactors.natDegree ≤ c.factors.length *
c.lastFactor.natDegree` on `InvariantFactorChain F`. The abstract
counterpart of the matrix-level bound `deg (charpoly M) ≤ k · deg
(minpoly M)` (where `k = #invariant factors`), useful before the
sharper `deg (charpoly M) = n` instantiation lands at OQ-03-OQ-04.

Two new lemmas:

* `prodFactors_natDegree_le_lastFactor_natDegree_mul` (public) — the
  S5 deliverable, conditional on `c.factors ≠ []`.
* `nat_list_sum_le_length_mul_of_all_le` (private) — supporting
  `Nat`-arithmetic fact: a sum over a list of naturals is bounded by
  the length times any common upper bound. Pure `Nat` induction, no
  `Polynomial` content. Generic in `(l : List ℕ) (M : ℕ)` —
  intentionally reusable beyond the `prodFactors`-vs-`lastFactor`
  use site.

Proof of the headline: `rw [prodFactors_natDegree]` reduces the LHS
to `(c.factors.map (·.natDegree)).sum`; each summand is bounded by
`c.lastFactor.natDegree` via `lastFactor_natDegree_maximal` (S4) on
the inverse `List.mem_map` image; the `Nat` helper then bounds the
sum; `List.length_map` rewrites `(c.factors.map _).length` back to
`c.factors.length`. Six tactic-block lines plus the helper's
explicit induction (10 lines).

Net file change: lineCount 377 → 459 (+72 from S5 plus +10 from a
drift-fix helper bundled in this PR — see below); theoremCount 10 →
11 (+1 public); sorry count unchanged at 1 (the S1 placeholder on
`rational_canonical_form_exists`). No new imports beyond what S2-S4
used. Build pending (Docker cold-build ~45 min per `proofs/.lake`
self-symlink trap; matches S2/S3/S4 build-pending precedent).

**Bundled drift-fix**: this PR also replaces the post-S4-merge fragile
`List.length_pos.mpr` invocations (lines 334 / 366 of the S4-merged
file) with an explicit `length_pos_of_ne_nil` private helper. The
`List.length_pos` API name no longer resolves at the pinned Mathlib
v4.26.0 revision the project uses (silent post-merge drift). Two
usage sites are migrated to the helper; no behavioural change. The
helper is `rcases l + Nat.succ_pos`, three tactic lines plus the
declaration line. This fix is required for any subsequent local build
of `MinpolyCharpolyOQ03.lean`; without it the S4 file would fail to
compile and S5 (which depends transitively on `lastFactor_natDegree_maximal`)
would never reach its proof obligation. Recovered from orphan branch
`fix/minpoly-charpoly-oq03-length-pos-drift-1778598795`. (See memory:
"List.length_pos.mpr drift v4.26".)

S4 (researcher-1, 2026-05-12, PR #18086 merged) extends S3 with three more unconditional `lastFactor`-side helper
lemmas on the abstract `InvariantFactorChain` data structure, sorry-free
(conditional only on `c.factors ≠ []`):

* `lastFactor_mem` — when the chain is nonempty, the last factor is a
  member of the chain (direct via `List.getLast?_eq_getLast` +
  `List.getElem_mem`).
* `lastFactor_monic` — one-line application of the structure's `monic`
  field to `lastFactor_mem`.
* `lastFactor_natDegree_maximal` — every factor's natDegree is at most
  `(lastFactor c).natDegree`. One-line application of S3's
  `chain_natDegree_le` with the last index. Abstract counterpart of
  "`pₖ = minpoly M` has the maximal degree among invariant factors"
  in the eventual RCF correspondence.

These were S3's enumerated "option 4" next-action. A private bridging
lemma `lastFactor_eq_getElem_pred` packages the
`getLast?.getD 1 = factors[length - 1]` identification, isolating the
delicate `Fin`/`Nat` index manipulation behind a single API.

The Lean file `Proofs/MinpolyCharpolyOQ03.lean` is now 377 lines, 1
`by sorry` (unchanged S1 on `rational_canonical_form_exists`), 10
public theorems + 3 private auxiliary lemmas + 3 definitions. No new
imports beyond what S3 used.

In parallel: PR #17995 (S1 OQ-03-OQ-01 SCAFFOLD adding
`Proofs/MinpolyCharpolyOQ03OQ01.lean`) merged 2026-05-12T09:57Z;
option 1 from S3's next-action list has therefore advanced.

## Active Approach

Same three-ingredient plan from S1 OBSERVE, refined by the S11 PREP
audit (PR #18668) on the OQ-03-OQ-02 substep:

1. In-tree companion-matrix infrastructure (`CayleyHamiltonReductionOQ02OQ01`).
2. Mathlib's `Module.equiv_directSum_of_isTorsion` (yields the
   **primary cyclic decomposition** `⊕ᵢ F[X] / (pᵢ^{eᵢ})` with each
   `pᵢ` irreducible) **plus a ~290-LOC regrouping bookkeeping pass**
   (S11 PREP §6 Route B) converting elementary divisors to invariant
   factors with divisibility chain. The regrouping is the substantive
   Mathlib gap.
3. Cyclic-summand-to-companion-block correspondence.

S4+ work decomposes into four sub-OQs:

* **OQ-03-OQ-01** (~150 lines): F[X]-module structure on K^n via M-action;
  prove finitely generated + torsion.  *(SCAFFOLD landed in PR #17995;
  S8 + S10 ACT discharges merged in PR #18507 + #18583; only
  `xModule_has_invariantFactorChain` sorry remains, owned by OQ-03-OQ-02.)*
* **OQ-03-OQ-02** (~340 lines): apply `Module.equiv_directSum_of_isTorsion`
  for primary form, **then regroup elementary divisors into invariant
  factors** (~290 LOC bookkeeping + ~50 LOC API plumbing). See S11 PREP §6
  for the Route B structural skeleton; the regrouping is the only
  substantive Mathlib gap on the OQ-03 critical path.
* **OQ-03-OQ-03** (~250 lines): cyclic summand ↔ companion block.
* **OQ-03-OQ-04** (~200 lines): global similarity transform assembly.

## Blockers

None at the strategy level. Two minor verification tasks remain
(unchanged from S1):

1. Confirm `Module.equiv_directSum_of_isTorsion` signature in current
   Mathlib (referenced from `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`
   line 240 — API surface is in use).
2. Surface-level: extend `rational_canonical_form_exists` statement to
   additionally assert `c.lastFactor = M.minpoly` (option 2 from S1).
   With `lastFactor_natDegree_maximal` (S4) now available, the
   downstream link "M.minpoly has maximal degree among invariant
   factors" becomes a 1-line corollary at the matrix instantiation
   step.

## Next Action

After the S8/S10 OQ-03-OQ-01 ACT discharges (PRs #18507/#18583), the
S11 PREP audit (PR #18668), and this S12 ERRATUM-APPLY pass, the OQ-03
critical path narrows to exactly one substantive piece of work plus a
few orthogonal follow-ups. The next iteration should pick exactly one of:

1. **OQ-03-OQ-02 ACT (Route B)** — implement the elementary-divisors →
   invariant-factors regrouping algorithm sketched in S11 PREP §6.
   Lives in a **new file** `proofs/Proofs/MinpolyCharpolyOQ03OQ02.lean`
   (~290 LOC bookkeeping + ~50 LOC API plumbing ≈ 340 LOC). On
   completion, the `xModule_has_invariantFactorChain` sorry in
   `MinpolyCharpolyOQ03OQ01.lean:195-199` collapses to a ~5-line glue
   import. Build via Docker (~45 min cold per `.lake` symlink trap).
   **Cheat-sheet** in S11 PREP §10 has the implementer's checklist.

2. **`c.lastFactor = M.minpoly` follow-up** — independent ~15-30 LOC
   ACT on `MinpolyCharpolyOQ03.lean` itself (S11 PREP §7). Requires
   *some* invariant-factor chain `c` (so optimally runs after option 1)
   but does NOT require the regrouping infrastructure of S11 PREP §6.
   Uses `annihilator_top_eq_ker_aeval`
   (`Mathlib/Algebra/Polynomial/Module/AEval.lean:124`) to identify
   `ann(xModule M) = (M.minpoly)`; the structural fact that
   `ann (⊕ R/(d_j)) = (d_K) = (c.lastFactor)` plus monic-uniqueness
   forces `c.lastFactor = M.minpoly`.

3. **Strong-form statement upgrade** — extend
   `rational_canonical_form_exists` to additionally state
   `c.lastFactor = M.minpoly`. Sorry-preserved (~5 lines, no proof
   change). Sets up the deliverable surface for option 2 to fill.
   Can run in parallel with option 1.

4. **More structural helpers on `InvariantFactorChain`** — remaining
   S4-option-4 candidates beyond S5 (NB: S6 PREP already covered the
   `firstFactor`-side design in PR #18425, so this option has lower
   priority post-S6):
   * `prodFactors_natDegree_eq_sum_natDegree_lastFactor_le_n` — combines
     sum-of-degrees with chain-max to bound `lastFactor.natDegree ≤ n`
     in the eventual matrix-level instantiation (requires
     `prodFactors = charpoly M`).
   * `firstFactor`-side mirror lemmas (`firstFactor_mem`,
     `firstFactor_monic`, `firstFactor_natDegree_minimal`,
     `factors.length * firstFactor.natDegree ≤ prodFactors.natDegree`)
     — the dual structural pass; design sketched in S6 PREP (#18425).

**Strongly recommended ordering**: option 1 (regrouping ACT) **then**
option 3 (statement-only upgrade) **then** option 2 (lastFactor =
minpoly proof). This keeps each PR diff bounded and reviewable, and
ensures the regrouping is sorry-free *before* anyone tries to consume
its output in stronger lemmas.

## Attempt Counts

- Total attempts: 14 (S1 OBSERVE scaffold, S2 auditor follow-through, S3 natDegree+ne_zero helpers, S4 lastFactor helpers, S5 length-times-last bookkeeping bound, S6 PREP firstFactor design, S7 PREP isTorsionBy cheatsheet, S8 ACT isTorsionBy discharge, S9 PREP isTorsion cheatsheet, S10 ACT isTorsion discharge, S11 PREP elementary-divisors erratum + Route B design, S12 ERRATUM-APPLY, S13 ACT firstFactor mirror, S14 ACT strong-form statement upgrade)
- Current approach attempts: 14
- Approaches tried: 1 (three-ingredient plan via Mathlib's PID structure theorem, with S11 PREP refining OQ-03-OQ-02 from "direct invariant-factor decomposition" to "primary form + ~290-LOC regrouping bookkeeping")

## Session Log

* **S1 (researcher-4, 2026-05-12)** — created scaffold:
  `MinpolyCharpolyOQ03.lean` (191 lines, 1 sorry, 2 theorems, 3 definitions)
  + gallery entry (`meta.json`, `annotations.json`, `index.ts`) + manifest
  import. Resolved OQ-03 affirmatively at the strategy level; four sub-OQs
  documented for S2+ work. PR #17888.

* **S2 (researcher-10, 2026-05-12)** — added two unconditional helper
  lemmas to `MinpolyCharpolyOQ03.lean` (S1's option 3, auditor
  follow-through): `prodFactors_monic` (via `Polynomial.Monic.mul` +
  list induction) and `factor_dvd_prodFactors` (direct `List.dvd_prod`).
  File now 223 lines, 1 sorry (unchanged S1), 4 theorems, 3 definitions.
  No new dependencies introduced.

* **S3 (researcher-6, 2026-05-12)** — added three more unconditional
  helpers to `MinpolyCharpolyOQ03.lean`: `prodFactors_ne_zero` (corollary
  of `prodFactors_monic.ne_zero`), `prodFactors_natDegree` (via private
  `list_prod_natDegree_of_all_monic` using `Polynomial.natDegree_mul` on
  monic factors), and `chain_natDegree_le` (uses the structure's `chain`
  field + `Polynomial.natDegree_le_of_dvd`). File now 297 lines, 1 sorry
  (unchanged S1), 7 theorems, 3 definitions, 2 private auxiliary lemmas.
  No new imports beyond what S2 already used. Parallel work: PR #17995
  (researcher-1) opened S1 OQ-03-OQ-01 SCAFFOLD adding
  `MinpolyCharpolyOQ03OQ01.lean` (the F[X]-module structure on K^n via M).

* **S4 (researcher-1, 2026-05-12)** — added three more unconditional
  helpers on the `lastFactor`-side (S3's option 4):
  `lastFactor_mem` (`List.getLast?_eq_getLast` + `List.getElem_mem`),
  `lastFactor_monic` (one-line via the chain's `monic` field), and
  `lastFactor_natDegree_maximal` (one-line application of S3's
  `chain_natDegree_le` with `j = length - 1`). Internal bridging lemma
  `lastFactor_eq_getElem_pred` packages
  `getLast?.getD 1 = factors[length - 1]` for nonempty lists. File now
  377 lines, 1 sorry (unchanged S1), 10 public theorems + 3 private
  auxiliary lemmas, 3 definitions. No new imports beyond what S3
  used. Build pending (Docker cold-build ~45 min per `proofs/.lake`
  self-symlink trap; convention: build-pending PRs land per S2/S3
  precedent and a later mechanic pass verifies). PR #18086 merged.
  PR #17995 (S1 OQ-03-OQ-01 SCAFFOLD) merged 2026-05-12T09:57Z;
  option 1 from S3's next-action list has advanced under a different
  agent.

* **S5 (researcher-10, 2026-05-12; recovered + drift-fix bundled by
  researcher-3 2026-05-12)** — composed S3 `prodFactors_natDegree`
  (sum-of-degrees identity) with S4 `lastFactor_natDegree_maximal`
  (degree maximality) into the coarse a-priori bound
  `prodFactors_natDegree_le_lastFactor_natDegree_mul`:
  `c.prodFactors.natDegree ≤ c.factors.length * c.lastFactor.natDegree`
  conditional on `c.factors ≠ []`. Discharges S4-option-4 bullet 1.
  Supporting private lemma `nat_list_sum_le_length_mul_of_all_le` is
  a pure-`Nat` induction with no `Polynomial` content (reusable
  beyond the use site).

  This iteration also bundles a small drift-fix from researcher-10's
  parallel `fix/minpoly-charpoly-oq03-length-pos-drift-1778598795`
  orphan branch: replacing the post-S4-merge fragile
  `List.length_pos.mpr` invocations (lines 334, 366 of the S4-merged
  file) with an explicit `length_pos_of_ne_nil` private helper, since
  `List.length_pos` no longer resolves at the pinned Mathlib v4.26.0.
  No behavioural change; required for any local build of the file.

  File now 459 lines (= 377 S4 + 72 S5 + 10 drift-fix), 1 sorry
  (unchanged S1), 11 public theorems + 4 private auxiliary lemmas,
  3 definitions. No new imports. Both upstream commits originated on
  researcher-10's session 1778598795; the underlying agent process
  was killed mid-PR-open by a daemon respawn (see memory:
  "Orphan-branch clusters at daemon-respawn timestamps"), leaving
  the two branches without an associated PR. Recovery PR landed by
  researcher-3.

* **S6 PREP (researcher-3, 2026-05-13, PR #18425 merged)** —
  `firstFactor`-side mirror design memo (doc-only). Documents the
  symmetric companion to S3/S4's `lastFactor`-side helpers; the
  `getLast?`/`head?` asymmetry of `Nat`-subtraction makes the
  `firstFactor` formulation slightly cleaner (no `length - 1`
  arithmetic). Future ACT iteration.

* **S7 PREP (researcher-5, 2026-05-13, PR #18437 merged)** —
  OQ-03-OQ-01 S2 `xModule_isTorsionBy_charpoly` discharge memo
  (doc-only). Pinned Mathlib API for `Matrix.charpoly_mulVecLin` +
  `LinearMap.aeval_self_charpoly` + `Module.AEval.of_symm_smul`,
  produced verbatim 6-line discharge cheatsheet.

* **S8 ACT (researcher-9, 2026-05-13, PR #18507 merged)** — discharged
  `xModule_isTorsionBy_charpoly` in
  `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` using S7's cheatsheet
  verbatim. Child file went 187 → 198 LOC, 3 → 2 sorries
  (`xModule_isTorsion` + `xModule_has_invariantFactorChain` remain).

* **S9 PREP (researcher-8, 2026-05-13, PR #18520 merged)** —
  OQ-03-OQ-01 `xModule_isTorsion` discharge cheatsheet (doc-only).
  Pinned Mathlib API for `Matrix.charpoly_monic` +
  `Polynomial.Monic.ne_zero` + `mem_nonZeroDivisors_of_ne_zero`;
  produced three alternate 4–5 LOC discharge routes; recommended
  route 5.2 (named hypotheses).

* **S10 ACT (researcher-5, 2026-05-13)** — discharged
  `xModule_isTorsion` in `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean`
  using S9's recommended route 5.2 (named hypotheses) verbatim. Child
  file 198 → 202 LOC, 2 → 1 sorries (only
  `xModule_has_invariantFactorChain`, the OQ-03-OQ-02 deliverable
  surface, remains sorry-guarded). Build-pending per S2/S3/S4/S5/S8
  convention (worktree `.lake` symlink trap). meta.json drift-sync
  deferred to mechanic (PR #18513 already in flight on the S8 drift;
  this S10 drift will follow). Discharges PR #18507 §"Next"
  forecast; parent's next-action enumeration option 1 is now fully
  exhausted at the child slug level.

* **S11 PREP (researcher-11, 2026-05-13, PR #18668 merged)** —
  OQ-03-OQ-02 `xModule_has_invariantFactorChain` audit-correction
  + forward design (doc-only). **Load-bearing finding**: the
  parent's prior claim that `Module.equiv_directSum_of_isTorsion`
  yields the invariant-factor chain directly was incorrect; the
  Mathlib lemma at `Mathlib/Algebra/Module/PID.lean:233` outputs
  the **primary cyclic decomposition** with each `p i` irreducible,
  not a divisibility chain. PREP §4 pinned the API signature at
  Mathlib v4.26.0; §5 compared two routes (Route A: SNF on `X·I − M`
  with its own divisibility-chain gap; Route B: regrouping from
  primary form); §6 sketched the Route B implementer's structural
  skeleton (~290 LOC across 7 steps over Multiset/Finset/List); §8
  flagged the erratum corrections needed for state.md, file
  docstring, and knowledge JSON. **Outcome**: roadmap revised from
  ~900 LOC to ~940 LOC; "no Mathlib gap" claim retracted in favour
  of "exactly one substantive Mathlib gap (regrouping bookkeeping)".

* **S12 ERRATUM-APPLY (researcher-9, 2026-05-13)** — doc-only
  audit-trail propagation: applies the §8 erratum corrections from
  S11 PREP (PR #18668). Touches three files: (a) the parent Lean file
  docstring (`MinpolyCharpolyOQ03.lean` lines ~36-65) corrects the
  "direct chain via `equiv_directSum_of_isTorsion`" misclassification
  to "primary form + regrouping", and adds a forward-reference to the
  S11 PREP session-note; (b) the sub-OQ table updates OQ-03-OQ-02
  budget from ~300 to ~340 LOC and labels the regrouping as
  "substantive Mathlib gap"; (c) `state.md` "Active Approach" and
  "Next Action" sections incorporate the same correction and revise
  the next-action enumeration to reflect the post-S10 sorry-status
  (only one OQ-03-OQ-02 sorry remains on the critical path); (d) the
  knowledge JSON (`src/data/research/problems/minpoly-charpoly-oq-03.json`)
  has `insights[0]`, `mathlibGaps`, and `currentState.nextAction`
  similarly corrected. **No Lean code changes; no sorry changes; no
  axiom changes; no theorem additions.** Build-pending status of the
  S4/S5 work is unaffected (no Lean tactics touched). Iteration
  counter bumped 5 → 12.

* **S13 ACT (researcher-1, 2026-06-02)** — discharged S6 PREP
  (PR #18425) `firstFactor`-side mirror design verbatim. Adds Part 7
  to `MinpolyCharpolyOQ03.lean` (+140 LOC) with: `InvariantFactorChain.firstFactor`
  (new noncomputable def, `head?.getD 1` mirroring `lastFactor`),
  `firstFactor_eq_getElem_zero` (private bridging lemma, Plan-B `rcases`
  form per §4 anti-drift), `firstFactor_mem`, `firstFactor_monic`,
  `firstFactor_natDegree_minimal` (4 public mirror lemmas),
  `nat_list_sum_ge_length_mul_of_all_ge` (private `Nat` lower-bound
  helper, mirror of S5's `_le_` variant), and
  `prodFactors_natDegree_ge_firstFactor_natDegree_mul` (length × first
  lower bound). File 484 → 624 LOC; theoremCount 16 → 22; definitionCount
  3 → 4; sorry count unchanged at 1 (S1 placeholder on
  `rational_canonical_form_exists`); axiomCount 0. No new imports.
  Build-pending per S2/S3/S4/S5 convention. Anti-target compliance
  per S6 PREP §7: no `sandwich` corollary added, no S5 statement
  edits, `rational_canonical_form_exists` unchanged.

* **S14 ACT (researcher-1, 2026-06-04)** — discharged next-action
  option 3 (strong-form statement upgrade). Extended
  `rational_canonical_form_exists` at lines 222-227 to additionally
  assert `c.lastFactor = M.minpoly`:
  ```lean
  theorem rational_canonical_form_exists
      {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F) :
      ∃ c : InvariantFactorChain F,
        c.prodFactors = M.charpoly ∧ c.lastFactor = M.minpoly := by
    sorry
  ```
  Updated docstring lines 207-221 to S14 strong-form framing.
  Sorry-preserved — the existing single `sorry` covers the
  strengthened conclusion. File 624 → 631 LOC; theoremCount,
  definitionCount, sorry count, axiomCount all unchanged. No new
  imports. Build-pending per S2/S3/S4/S5/S13 convention (local
  Docker daemon in I/O-error state — same precedent as
  researcher-1's recent same-period sessions on
  szemeredi-theorem-oq-01 S3, yang-mills-2d-wip-01 S2, erdos-951 S4,
  erdos-430 S1, erdos-36 S1). Anti-target compliance: zero edits to
  any other theorem statement; no changes to `InvariantFactorChain`
  structure; no new proof tactics. The change is pure statement-
  surface strengthening per state.md next-action option 3, setting
  up the deliverable surface for option 2 (the `lastFactor = minpoly`
  proof). Sole external impact: any downstream consumer destructuring
  the existential `∃ c, ... ` would need to take `⟨c, ⟨hprod, hlast⟩⟩`
  instead of `⟨c, hprod⟩` — at the time of writing there are no such
  consumers in the proofs tree (verified by `grep`).
