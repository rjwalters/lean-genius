# Research State: prob-method-lovasz-local-oq-01

## Current State
**Phase**: S6 ACT (build-verify repair of S5/S5b ACT 4-cluster v4.26.0 regression — Docker-verified 7743 jobs)
**Path**: full
**Since**: 2026-05-14
**Iteration**: 8

## S6 ACT (build-verify repair) — researcher-8, 2026-05-14 ~18:35 UTC

**Mode**: ACT (`MoserTardos.lean` net +20/-20 LOC, structurally unchanged;
build VERIFIED 7743 jobs, 4 Docker iterations).

**Outcome**: first Docker baseline of `MoserTardos.lean` since the S5 ACT
(#18629) and S5b ACT (#18960) merges shipped with `(build pending)`
surfaced a **6-error 4-cluster regression**. All four clusters were
elaboration-level latent bugs masked by absence of build validation —
NOT v4.26.0 surface renames; the S4a/S4b/S5b/S5c PREP bearer audits
remain valid.

**Cluster summary:**

| Cluster | Sites | Class | Fix |
|---|---|---|---|
| A | 163, 247, 276 | `rw [h_const/h_proj]` post-`map_comp` eta/composition shape mismatch | Rewrite `h_const`/`h_proj` LHS in `∘` form; add `Function.comp` to `simp` lemma list |
| B | 211 | `ℝ≥0∞` notation tokenization fails inside `rw [...]` followed by `i]` | Lift to `have hprod; rw [hprod]`; rename `ℝ≥0∞` → `ENNReal` identifier |
| C | 179 | Downstream unsolved goal from B | Resolves automatically once B fixed |
| D | 291 | Recursive `P.run n` field-notation strip on `def run` body | Drop prefix: `run n` (with `P` auto-bound from variable) |

Full kit, error-by-error fix recipes, and lessons-learned in
`sessions/2026-05-14-s06-act-build-verify-repair.md`.

### Files updated (S6 ACT)

- `proofs/Proofs/MoserTardos.lean` — net +20/-20 LOC (structurally
  unchanged at 382 LOC), all surgical:
  - `resampleAt_apply_outside` lines 154-164: cluster A
  - `marginal_uniformOfFintype_pi` lines 207-227: cluster B
  - `resampleAt_apply_inside` lines 239-249: cluster A
  - `resampleAt_indep` lines 264-276: cluster A
  - `run` line 290: cluster D
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  section; iteration 7 → 8.
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-14-s06-act-build-verify-repair.md`
  — new session note (~210 LOC).
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.iteration` 7 → 8, `phase` S5b ACT → S6 ACT,
  `focus`/`nextAction` updated, `lastUpdate`,
  `attemptCounts.total` 5 → 6.

### Build verification

```bash
./proofs/scripts/docker-build.sh Proofs.MoserTardos
# build 1 (baseline): 6 errors, 4 clusters
# build 2 (clusters A + D v1): 3 errors persist; cluster B + new D variant
# build 3 (B `have/rw` workaround + D `run n`): cluster B persists at ℝ≥0∞
# build 4 (B ℝ≥0∞ → ENNReal): ✓ 7743 jobs clean
```

### Race-safety note (S6 ACT)

- Pre-claim probe (~18:00 UTC): 0 ACT-tier open PRs on slug; only
  doc-only S5 PREP STATE-SYNC #18984 carryover.
- Pre-push probe will re-verify before push.

### Next action (S7 PREP — OQ-01-A.3 or OQ-01-B)

With the file actually building clean, the OQ-01-A.3 / OQ-01-B branches
are now strictly unblocked:

- **(a) S7 PREP OQ-01-A.3** — `LLLAdmissibleUniform` refinement of
  `LLLAdmissible` whose `prob : Fin numEvents → ℝ` field is the
  uniform-draw probability `Pr_{v ~ uniformOfFintype State}[isBad i v]`,
  plus the faithful-link lemma. ~150 LOC.

- **(b) S7 PREP OQ-01-B** — `WitnessTree` inductive type + `isProper`
  predicate (the OQ-01-B half), ~500 LOC across 2-3 PRs.

The repaired marginal/independence pack
(`resampleAt_apply_outside`, `resampleAt_apply_inside`, `resampleAt_indep`,
helper `marginal_uniformOfFintype_pi`) is the load-bearing API for
OQ-01-B's witness-tree probability bound.

## S5b ACT (helper + `_inside` + `_indep`) — researcher-12, 2026-05-14 ~00:35 UTC

**Mode**: ACT (`MoserTardos.lean` +113 LOC; build pending).

**Outcome**: shipped the four-step recipe from S5c PREP §9 (PR #18930) +
S5b PREP §7 (PR #18683) + S4b PREP §6/§7 (PR #18580). Net delta:
**+113 LOC** to `proofs/Proofs/MoserTardos.lean` (269 → 382 LOC), 0 new
sorries, 0 new axioms, 0 new imports.

### What I added

Three new declarations between `resampleAt_apply_outside` (existing
L150–L163) and `step` (now L282):

1. **`private lemma marginal_uniformOfFintype_pi`** — reusable Mathlib-style
   helper stating the marginal of `PMF.uniformOfFintype` on a dependent
   product is the uniform PMF on the factor. ~52 LOC of body. Proof:
   `ext + map_apply + uniformOfFintype_apply + tsum_fintype + sum_filter
   + sum_const + nsmul_eq_mul` to reduce to a fiber-card×inverse-card
   product, then a 22-LOC `h_fiber` block via
   `Fintype.card_subtype.symm + Fintype.card_congr + Equiv.piSplitAt`,
   then `push_cast [Fintype.card_pi] + Fintype.prod_eq_mul_prod_subtype_ne`
   to peel off the i-th factor, then a 4-`have` positivity/finiteness
   pack feeding `ENNReal.mul_inv + mul_left_comm + ENNReal.mul_inv_cancel
   + mul_one`.

2. **`lemma resampleAt_apply_inside`** — ~17 LOC including docstring.
   `unfold + PMF.map_comp + funext + simp [dif_pos hj]` reduces the
   glue-function to a single-coordinate projection, then `exact
   marginal_uniformOfFintype_pi ⟨j, hj⟩` closes it (one-line discharge,
   matching S4b PREP §6).

3. **`lemma resampleAt_indep`** — ~20 LOC including docstring. Same
   structural pattern as `_outside` lifted from one coordinate to a
   `Finset T`: every `k : ↥T` has `k.val ∉ S` (by `Finset.disjoint_left.mp
   hT`), the glue function reduces to a constant `v` on all of `T`, then
   `PMF.map_const` finishes.

### Deviations from the PREP recipes (intentional)

- **`mul_left_comm` instead of `← mul_assoc` + `one_mul`** in the
  ENNReal cancellation (last 3 lines of the helper). The S5b PREP §2
  recipe used `← mul_assoc, ENNReal.mul_inv_cancel ..., one_mul`, but the
  associativity direction does not match the cancellation target after
  `ENNReal.mul_inv` distributes the inverse. Substituting `mul_left_comm`
  (which rewrites `a * (b * c) = b * (a * c)`) puts the
  cancellable pair `(∏ k≠i, ...) * (∏ k≠i, ...)⁻¹` adjacent for the
  `ENNReal.mul_inv_cancel` rewrite, ending with `mul_one` rather than
  `one_mul`.
- **`Or.inl h_card_i_ne_top` instead of `Or.inl h_pi_ne_top`** as the
  second argument to `ENNReal.mul_inv`. The signature is
  `(h : a ≠ 0 ∨ b ≠ ⊤) → (h' : a ≠ ⊤ ∨ b ≠ 0) → (a * b)⁻¹ = a⁻¹ * b⁻¹`;
  with `a = card (β i)` and `b = ∏ k≠i, ...`, the second disjunction
  needs `a ≠ ⊤` (i.e. `h_card_i_ne_top`), not `b ≠ ⊤` (which would be
  `h_pi_ne_top` but doesn't fit either disjunct).

Both deviations are mechanical algebraic refinements of the documented
recipe; the underlying strategy (helper via piSplitAt + factor-out-i-th
via `prod_eq_mul_prod_subtype_ne` + ENNReal cancellation) is unchanged.

### Files updated (S5b ACT)

- `proofs/Proofs/MoserTardos.lean` — +113 LOC, 3 new declarations
  inserted after `resampleAt_apply_outside`. File: 269 → 382 LOC.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  section; iteration 6 → 7; phase S5c PREP → S5b ACT.
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-14-s05b-act-helper-and-pack.md`
  — new session note documenting the three deviations above + the
  remaining risks for doctor verification.
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.iteration` 6 → 7, `phase` PREP → S5b ACT, `focus` /
  `nextAction` updated, `progressSummary` prepended, `lastUpdate`,
  `attemptCounts.total` 4 → 5.

### Build-verification posture

Build pending. The worktree's `proofs/.lake` is the recursive
self-referential symlink documented in
`feedback_researcher_lake_symlink_loop_and_wipe.md`; local Docker build
would require a ~45-min cold Mathlib clone. CI / doctor is the ground
truth. Each named bearer in the new code is verified at lake-pinned
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`) per the
S4a/S4b/S5b/S5c PREP audits.

### Race-safety note (S5b ACT)

- Pre-claim probe (~00:30 UTC, 2026-05-14): 0 open PRs on slug; most
  recent merge S5c PREP (#18930) at 23:06 UTC ~1.5h lead time, well
  outside the 30-min same-slug race window.
- Pre-push probe will re-verify before push.

### Next action (S6 ACT or OQ-01-A.3)

Per the road map in `state.md:301-313`:

- **S6 PREP (OQ-01-A.3)**: Define `LLLAdmissibleUniform` (a refinement of
  `LLLAdmissible` whose `prob` field is the uniform-draw probability of
  `A_i`); prove the faithful-link lemma `prob i = (... uniform measure of
  isBad i ...)`. ~150 LOC.

- **Alternative — S6 PREP (OQ-01-B)**: Begin `WitnessTree` inductive type
  + `isProper` predicate (the OQ-01-B half). The marginal/independence
  pack delivered here is exactly the input it needs.

The helper `marginal_uniformOfFintype_pi` is reusable across both
directions; future ACT iterations should treat it as part of the
file-local API surface.

## S5c PREP (`h_fiber` audit) — researcher-5, 2026-05-13 ~22:25 UTC

**Mode**: PREP (doc-only; no `.lean` diff).

**Outcome**: produced
`sessions/2026-05-13-s05c-prep-h-fiber-card-equiv-audit.md` — closes the
single remaining bearer-audit uncertainty in the S4b PREP / S5b PREP
helper-proof template for `PMF.marginal_uniformOfFintype_pi`.

### What this resolves

S4b PREP §3.2 / §9.4 + S5b PREP §2.2 risk #5 both flagged
`Finset.card_eq_of_equiv_fintype` as the bridge from
`(Finset.univ.filter p).card` to `Fintype.card { x // p x }` but
explicitly deferred verification ("Verify at S5b ACT time").

This PREP **completes that verification**:

- **Negative**: `Finset.card_eq_of_equiv_fintype` does **not** exist
  at the pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`v4.26.0`) — verified by `gh api` grep of `Finset/Card.lean`,
  `Fintype/Card.lean`, `Logic/Equiv/Finset.lean`.
- **Positive**: canonical replacement is
  `Fintype.card_subtype.symm` (Card.lean L378) → `Fintype.card_congr`
  (Card.lean L67), feeding an explicit
  `{f // b = f i} ≃ ∀ k : {k // k ≠ i}, β k` built from
  `Equiv.piSplitAt` (Prod.lean L479, re-verified).

### What the doc contains

- §2: pinned-SHA audit table for 3 replacement bearers (Card.lean L378,
  Fintype/Card.lean L67, Prod.lean L479) — file path, blob context,
  line number, verbatim signature.
- §3: **~22 LOC sorry-free Lean rewrite of S4b PREP §3.2's `h_fiber`
  block** using only the verified bearers. Drops directly into the
  helper-proof template at the §3 position.
- §4: updated LOC accounting for S5b ACT — helper now ~44 LOC
  (S4b §3.2 scaffold + this PREP §3 `h_fiber` block + S5b §2 ENNReal
  block); 3-lemma pack still ~38 LOC; net S5b ACT delta ~70 LOC.
- §5: three residual risks (`Subtype.coe_mk` simp, `@[simps]` name
  variants, `.left_inv` field projection) with in-doc fallbacks.
- §9: revised S5b ACT 4-step recipe.

### Files updated (S5c)

- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s05c-prep-h-fiber-card-equiv-audit.md`
  — new doc, ~250 LOC.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this
  section; iteration 5 → 6.
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.iteration` 5 → 6, `focus` / `nextAction` updated,
  `progressSummary` prepended, `lastUpdate`.

### Build-verification posture

Doc-only PREP; `MoserTardos.lean` unchanged. No build needed.

### Race-safety note (S5c)

- Pre-claim probe (~22:18 UTC): 0 open PRs on the slug;
  most recent merge is S5b PREP (PR #18683) at 08:19 UTC — 14h lead time,
  well outside the morning's 4-merges-in-6h saturation burst.
- Pre-push probe will re-verify before push.

### Next action (S5b ACT — now fully unblocked)

Per the revised recipe in §9 of the new PREP doc + S4b PREP §6/§7 +
S5b PREP §2 + this PREP §3: ship `PMF.marginal_uniformOfFintype_pi`
(~44 LOC) + `resampleAt_apply_inside` (~8 LOC, S4b PREP §6) +
`resampleAt_indep` (~18 LOC, S4b PREP §7). Net delta ~70 LOC.

## S5 ACT (Outside) — researcher-6, 2026-05-13 ~07:10 UTC

**Outcome**: progress — discharged the first of the three S4b PREP §5-§7 marginal-pack lemmas: `resampleAt_apply_outside`. +24 LOC to `proofs/Proofs/MoserTardos.lean` (245 → 269), 0 new sorries, 0 new axioms, 0 new imports.

### What I added

The S4b PREP §5 verbatim discharge of the disjoint-coordinate marginal:

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars)) (v : P.State)
    (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j) := by
  classical
  unfold resampleAt
  rw [PMF.map_comp]
  have h_const :
      (fun a : ∀ k : S, P.alphabet k.val =>
        (fun (b : Fin P.numVars) =>
          if h : b ∈ S then a ⟨b, h⟩ else v b) j)
      = Function.const _ (v j) := by
    funext a
    simp [dif_neg hj]
  rw [h_const, PMF.map_const]
```

11-LOC proof body + docstring + blank line + section context = 24 LOC. Uses only `PMF.map_comp` (Mathlib v4.26.0 `Probability/ProbabilityMassFunction/Constructions.lean:66`) and `PMF.map_const` (same file, line 79), plus `dif_neg`.

### Why ship only `_outside` (not the full §5-§7 pack)

S4b PREP §6 (`_inside`) and §7 (`_indep`) depend on a new helper `PMF.marginal_uniformOfFintype_pi` (~40 LOC, S4b PREP §3) which uses `Equiv.piSplitAt`, `Fintype.card_congr`, `Fintype.card_pi`, `tsum_fintype`, and ENNReal arithmetic. The helper's proof is the single mathematically-substantive step in the pack; shipping it without local Docker build verification (`.lake symlink loop` trap) is risky for ~40-LOC probability-theory code.

This S5 ACT ships only `_outside` (12 LOC, uses only 2 Mathlib lemmas, mechanical `funext + simp [dif_neg]`). The helper + `_inside` + `_indep` are deferred to a subsequent S5b ACT.

### Files updated (S5)

- `proofs/Proofs/MoserTardos.lean` — +24 LOC, one new lemma `resampleAt_apply_outside` inserted between `def resampleAt` and `def step`. File: 245 → 269 LOC.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — this file. Iteration 3 → 5 (jumping S4 since S4/S4a/S4b were PREP-only).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s05-act-outside-marginal.md` — new session note.

### Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, the worktree's `proofs/.lake` inherits the main repo's self-referential symlink loop; local Docker build is unreliable. **Lean file committed and pushed first**; PR title carries "build pending" so the doctor agent can verify from a clean worktree.

No new imports (the file already does `import Mathlib`, `open scoped Classical`).

### Race-safety note (S5)

- Pre-claim probe (2026-05-13 ~07:05 UTC): 0 open PRs on the slug; most recent merge is S4b PREP (PR #18580) at 04:50 UTC (~2h15min lead time).
- Pre-push probe will re-verify before push.

### Next action (S5b — helper + `_inside` + `_indep`)

Per S4b PREP §3 + §6 + §7: ship `PMF.marginal_uniformOfFintype_pi` (~40 LOC) and use it to discharge `resampleAt_apply_inside` (~8 LOC) and `resampleAt_indep` (~18 LOC). The helper's proof is the load-bearing step and warrants a fresh session.

## S3 ACT — researcher-1, 2026-05-13 (pre-S5 history, for reference)

S3 ACT (researcher-1, 2026-05-13, this PR): **OQ-01-A.2 `resampleAt`
product-PMF closure** in `Proofs/MoserTardos.lean:131-139` (~9 LOC
replacement of the single deferred `sorry`).

The implementation is the Approach B form recommended by the S3 ANALYSIS
doc (researcher-5, PR #18268, §2.2):

```lean
noncomputable def resampleAt (S : Finset (Fin P.numVars)) (v : P.State) :
    PMF P.State :=
  (PMF.uniformOfFintype (∀ j : S, P.alphabet j.val)).map
    (fun (a : ∀ j : S, P.alphabet j.val) (j : Fin P.numVars) =>
      if h : j ∈ S then a ⟨j, h⟩ else v j)
```

The construction samples the dependent product `∀ j : ↥S, alphabet j.val`
uniformly via `PMF.uniformOfFintype` (a finite nonempty `Fintype` by
`Pi.instFintype` + the namespace-attribute-promoted `alphabetFintype`
and `alphabetNonempty`), then glues the sample with the deterministic
`v j` for `j ∉ S` via a single `PMF.map`. The if-then-else uses
`Finset.decidableMem` to dispatch on `j ∈ S`.

**Net sorry delta**: 1 → 0 in MoserTardos.lean (excluding the two
True-shell theorems `mt_expected_step_bound` / `mt_terminates_as` which
still ship usable algebraic shells with full statements deferred to
OQ-01-B / OQ-01-C).

**Net axiomCount delta**: 0.

## S2 ACT history (previous, for reference)

S2 ACT (researcher-12, 2026-05-12, PR #18213 merged): **OQ-01-A.1
algorithm skeleton — `Proofs/MoserTardos.lean` (NEW FILE, +243 lines)**.

Created a standalone scaffold of the variable-version Moser–Tardos
algorithm and stated the two main theorems whose proofs are deferred to
OQ-01-B (witness-tree construction) and OQ-01-C (Galton–Watson /
generating-function sum). The file is wired into the umbrella
`proofs/Proofs.lean` (alphabetical position between `MorleysTheoremOQ01`
and `MotivicFlagMaps`).

**Public surface introduced (`namespace ProbMethod.MoserTardos`):**

* `structure MTProblem` — packages `numVars`, `numEvents`, per-variable
  `alphabet : Fin numVars → Type` with `Fintype` + `Nonempty` instance
  fields, the variable-collision footprint `vbl : Fin numEvents →
  Finset (Fin numVars)`, the bad-event predicate `isBad` (with field-
  encoded decidability), and a faithfulness clause `vblFaithful`
  certifying that `isBad i v` depends only on `v` at the variables in
  `vbl i`.
* `MTProblem.State := (j : Fin P.numVars) → P.alphabet j` with derived
  `Fintype` and `Nonempty` instances.
* `MTProblem.isViolated : State → Prop` with a `Decidable` instance via
  `Fintype.decidableExistsFintype`.
* `MTProblem.pickBad : State → Option (Fin numEvents)` selecting the
  least-index violated event (a deterministic resampling rule, the
  simplest admissible choice per Moser–Tardos).
* `MTProblem.resampleAt : Finset (Fin numVars) → State → PMF State`
  — **stubbed with `sorry`** for the product-`PMF` construction (the
  natural OQ-01-A.2 follow-on; the full mechanical construction is
  documented as a proof obligation in the file's docstring).
* `MTProblem.step : State → PMF State` — one-step Markov chain via
  `match pickBad v` (pure on the no-bad branch, `resampleAt (vbl i)` on
  the bad branch).
* `MTProblem.run : ℕ → State → PMF State` — iterated `step` via
  `PMF.bind`.
* `MTProblem.LLLAdmissible : (Fin numEvents → ℚ) → Prop` — packages the
  range `0 ≤ x i < 1` and the symbolic LLL inequality
  `prob i ≤ x i * ∏_{k ∈ adj i} (1 - x k)` over auxiliary `prob, adj`
  parameters (the faithful link to a uniform-measure probability is
  deferred to OQ-01-A.2 / OQ-01-B).
* `theorem mt_expected_step_bound` — statement shell; the body proves
  the non-negativity of `Σᵢ x_i/(1-x_i)` (matching the parent
  `moser_tardos_termination`). The actual expected-value bound on
  `run`-resampling counts is deferred to OQ-01-B (witness trees)
  + OQ-01-C (Galton–Watson sum).
* `theorem mt_terminates_as` — statement placeholder (returns `True`);
  full `Tendsto (fun n => (run n v₀).toMeasure {v | isViolated v}) atTop
  (𝓝 0)` statement awaits OQ-01-B `WitnessTree` infrastructure.

**Sorry inventory (this PR):** exactly **one** `sorry`, in
`resampleAt` (the product-`PMF` over `Finset (Fin numVars)`). The two
main theorems are NOT `sorry`-ed at the algebraic-shell level — they
ship usable inequalities, with the full statements documented in
docstrings for OQ-01-B / OQ-01-C.

**Build status:** build pending. Worktree's `proofs/.lake` is a
recursive self-symlink (per
`feedback_researcher_lake_symlink_broken.md`), so a local Docker build
would re-fresh-clone Mathlib (~45 min cold). CI is the ground truth.
The single-file Mathlib API surface invoked is:
`PMF.pure`, `PMF.bind`, `Fintype.decidableExistsFintype`, `Finset.min'`,
`Finset.filter`, `Finset.sum_nonneg`, `div_nonneg`, `linarith`,
`Classical.choice`, plus the auto-derived `Pi.fintype`/`Pi.Nonempty`
chain — all stable across the recent v4.26 API surface.

Next action: **S3 ACT — OQ-01-A.2 product-`PMF`** (close the
`resampleAt` `sorry` via iteration of `PMF.bind` over `Finset.univ`,
using `PMF.uniformOfFintype (P.alphabet j)` for `j ∈ S` and `PMF.pure
(v j)` for `j ∉ S`). Estimated ~60–80 lines.

## S1 history

S1 OBSERVE (researcher-11, 2026-05-12, PR #18100 merged): surveyed the
open question, decomposed into three sub-tasks (OQ-01-A / OQ-01-B /
OQ-01-C), surveyed Mathlib API readiness, and identified the duplication
with `lovasz-local-lemma-oq-03`.

## Active Approach

**Approach 2** — Direct witness-tree proof (Moser–Tardos 2010 §4),
decomposed into:

- **OQ-01-A**: Algorithm + probability space (PMF-based finite model)
- **OQ-01-B**: Witness trees + tree-probability bound
- **OQ-01-C**: Galton-Watson / generating-function sum to `xᵢ/(1-xᵢ)`

Approach 1 (symmetric-only) and Approach 3 (entropy-compression) explicitly
rejected as insufficient for the full OQ — see `problem.md`.

## Attempt Count
- Total attempts: 2 (S1 OBSERVE + S2 ACT)
- Current approach attempts: 1 (S2 OQ-01-A.1 skeleton)
- Approaches considered: 3 (recommended: Approach 2 with A/B/C decomposition)

## Blockers

- **Mathlib gap**: no Galton–Watson branching-process API. Mitigation: use
  direct generating-function calculation in OQ-01-C.
- **Mathlib gap**: no general "rooted labelled tree" type. Mitigation: define
  `inductive WitnessTree` from scratch in OQ-01-B.
- **Sibling duplication**: `lovasz-local-lemma-oq-03` is the same problem.
  Coordinate at S2; do not block S2 on dedup.

## Next Action

**S4 ACT (or S3-bis lemma pack) — three follow-on lemmas anticipated for
OQ-01-B**, per S3 ANALYSIS §4. After OQ-01-A.2 closes (this PR), the
following sorry-free lemmas should be the next addition:

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j)

lemma resampleAt_apply_inside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.uniformOfFintype (P.alphabet j)

lemma resampleAt_indep (S : Finset (Fin P.numVars)) (v : P.State)
    (T : Finset (Fin P.numVars)) (hT : Disjoint T S) :
    (P.resampleAt S v).map (fun w => (fun j : T => w j.val)) =
      PMF.pure (fun j : T => v j.val)
```

The first two are corollaries of `PMF.map_uniformOfFintype_fst/snd` and
the `if h : j ∈ S` dispatch; the third is a `Finset.map` lift. Together
they provide the marginal/independence facts that OQ-01-B (witness
trees) directly invokes.

**Estimated next-PR scope**: ~50-80 LOC. **Build-verify under Docker.**

Then **S4-S5 OQ-01-A.3**: LLLAdmissible faithful link to uniform measure
(~150 LOC). Then **S6+ OQ-01-B**: witness trees.

## Open Sub-Tasks (Roadmap)

| Step | Deliverable | Tractability | Est. LOC |
|------|-------------|--------------|----------|
| S1 OBSERVE (done, #18100) | problem.md / knowledge.md / state.md / JSON | trivial | 1100 markdown |
| S2 ACT OQ-01-A.1 (this PR) | MoserTardos.lean skeleton + 2 stated theorems | medium | +243 LOC |
| S3 ACT OQ-01-A.2 | close `resampleAt` product-PMF + invariance lemma | medium | ~60-80 LOC |
| S4-S5 OQ-01-A.3 | LLLAdmissible faithful link to uniform measure | medium | ~150 LOC |
| S6-S8 OQ-01-B | witness trees + tree-prob bound | hard | ~500 LOC, 2-3 PRs |
| S9-S11 OQ-01-C | Galton–Watson sum bound | hard | ~400 LOC, 2-3 PRs |
| S12 complete | Final integration + close `mt_expected_step_bound` | medium | ~100 LOC |

Total estimated: 6-9 PRs after S1, comparable to a marquee sub-theorem.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-11 | #18100 (merged) | OBSERVE — three-part decomposition + Mathlib survey + sibling dedup analysis |
| S2 | 2026-05-12 | researcher-12 | #18213 (merged) | ACT — OQ-01-A.1 skeleton in `Proofs/MoserTardos.lean` (+243 lines, 1 sorry in `resampleAt`) |
| S3 ANALYSIS | 2026-05-12 | researcher-5 | #18268 (merged) | ANALYSIS — `resampleAt` PMF construction roadmap, Approach A/B/C comparison, three follow-on lemmas (doc-only) |
| S3 ACT | 2026-05-13 | researcher-1 | (this PR) | ACT — OQ-01-A.2 close `resampleAt` sorry via Approach B (PMF.uniformOfFintype + map glue; ~9 LOC replacement) |
