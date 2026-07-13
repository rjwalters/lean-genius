# S5b ACT — `marginal_uniformOfFintype_pi` helper + `_inside` + `_indep` (build pending)

**Date**: 2026-05-14 (~00:35 UTC)
**Author**: researcher-12
**Phase**: ACT (`MoserTardos.lean` +113 LOC; build pending)
**Iteration**: 7
**Predecessors**: PR #18100 (S1), #18213 (S2), #18268 (S3 ANALYSIS), #18400 (S3 ACT `resampleAt` close), #18420 (S4 PREP WitnessTree), #18477 (S4a PREP marginal audit), #18580 (S4b PREP `piSplitAt`), #18629 (S5 ACT `_outside` lemma), #18683 (S5b PREP ENNReal cancellation), #18930 (S5c PREP `h_fiber` audit).
**Build status**: pending. Worktree's `proofs/.lake` is the recursive
self-symlink loop documented in
`feedback_researcher_lake_symlink_loop_and_wipe.md`; local Docker build
requires a ~45-min cold Mathlib clone. CI / doctor verifies via
`./proofs/scripts/docker-build.sh Proofs.MoserTardos` from a clean
worktree.

## 1. Scope

Three new declarations added to `proofs/Proofs/MoserTardos.lean` between
the existing `resampleAt_apply_outside` (L150-L163) and `step` (now L282):

1. `private lemma marginal_uniformOfFintype_pi` (~52 LOC of body) —
   reusable Mathlib-style statement: the marginal of `PMF.uniformOfFintype`
   on a dependent product `∀ k, β k` at coordinate `i` is the uniform PMF
   on `β i`.
2. `lemma resampleAt_apply_inside` (~17 LOC incl. docstring) — applies
   the helper at `⟨j, hj⟩ : ↥S` to close the `j ∈ S` marginal lemma.
3. `lemma resampleAt_indep` (~20 LOC incl. docstring) — disjoint-coordinate
   independence, structurally identical to `resampleAt_apply_outside`
   lifted from one coordinate to a `Finset T` via
   `Finset.disjoint_left.mp hT`.

Net delta: **+113 LOC** (269 → 382). Zero new sorries, zero new axioms,
zero new imports.

## 2. Recipe vs. shipped: two intentional deviations

### 2.1. `mul_left_comm` instead of `← mul_assoc + one_mul`

S5b PREP §2 (PR #18683) wrote the closing ENNReal cancellation as:

```lean
rw [ENNReal.mul_inv (Or.inl h_card_i_ne_zero) (Or.inl h_pi_ne_top),
    ← mul_assoc, ENNReal.mul_inv_cancel h_pi_ne_zero h_pi_ne_top, one_mul]
```

Trace of the LHS after `ENNReal.mul_inv` distributes the inverse:

```
LHS = A * (B⁻¹ * A⁻¹)    where A = ∏ k≠i, card (β k.1), B = card (β i)
```

Applying `← mul_assoc` to this term rewrites
`a * (b * c) ← (a * b) * c`, yielding `(A * B⁻¹) * A⁻¹`. But
`ENNReal.mul_inv_cancel` has signature `a * a⁻¹ = 1`; the cancellable
pair `(A, A⁻¹)` is not adjacent in `(A * B⁻¹) * A⁻¹`, so the next `rw`
fails to fire.

The fix: use `mul_left_comm` (signature
`a * (b * c) = b * (a * c)`), which rewrites
`A * (B⁻¹ * A⁻¹) = B⁻¹ * (A * A⁻¹)`, putting the cancellable pair
adjacent. Then `ENNReal.mul_inv_cancel` rewrites the inner `(A * A⁻¹)`
to `1`, leaving `B⁻¹ * 1`, and `mul_one` (not `one_mul`) finishes.

```lean
rw [ENNReal.mul_inv (Or.inl h_card_i_ne_zero) (Or.inl h_card_i_ne_top),
    mul_left_comm,
    ENNReal.mul_inv_cancel h_pi_ne_zero h_pi_ne_top, mul_one]
```

### 2.2. `Or.inl h_card_i_ne_top` instead of `Or.inl h_pi_ne_top`

S5b PREP §2 wrote the second arg to `ENNReal.mul_inv` as
`Or.inl h_pi_ne_top`. The signature is

```
ENNReal.mul_inv : (h : a ≠ 0 ∨ b ≠ ⊤) → (h' : a ≠ ⊤ ∨ b ≠ 0) → (a * b)⁻¹ = a⁻¹ * b⁻¹
```

With `a = card (β i)` and `b = ∏ k≠i, card (β k.1)`, the second
disjunction is `card (β i) ≠ ⊤ ∨ ∏ k≠i ≠ 0`. The PREP cited
`h_pi_ne_top : ∏ k≠i ≠ ⊤`, which does not fit either disjunct: the
left disjunct asks for `a ≠ ⊤` (about `card (β i)`), and the right asks
for `b ≠ 0` (the `∏` is non-zero, not non-top). Substituting
`h_card_i_ne_top : (card (β i) : ℝ≥0∞) ≠ ⊤` selects the left disjunct
correctly. Equivalently `Or.inr h_pi_ne_zero` (right disjunct) also
works; `Or.inl h_card_i_ne_top` is the shorter form.

### 2.3. Why these are mechanical (not architectural)

Both deviations preserve the strategy of the recipe — helper via
`Equiv.piSplitAt` for the bijection, `Fintype.prod_eq_mul_prod_subtype_ne`
to peel off the `i`-th factor, then ENNReal cancellation. Only the
exact final-tactic chain changes. The four positivity/finiteness
`have`s, the bridge through `Fintype.card_subtype.symm`, the
`Fintype.card_congr` application, and the `push_cast [Fintype.card_pi]`
all match the recipe verbatim.

## 3. Residual risks for doctor / build verification

| Risk | Severity | In-doc fallback |
|---|---|---|
| `simp [Equiv.piSplitAt]` for the subtype proof `b = ((piSplitAt i β).symm ⟨b, g⟩) i` may not auto-fire if the `@[simps]`-generated names differ from what `simp` expects. Used `simp [Equiv.piSplitAt]` (unfold by-def) for maximum robustness. | Low | Replace with `simp [Equiv.piSplitAt, Equiv.coe_fn_symm_mk, dite_eq_left_iff]`. |
| `left_inv` step uses `rw [hf, ← hfi, Prod.mk.eta]`. The `Prod.mk.eta` rewrite may need a different name (`Prod.mk_eta` or `Prod.eta`). | Low | Replace with `congr 1` or rewrite explicitly via the structure projections. |
| `push_cast [Fintype.card_pi]` may not normalize the Nat-cast across the product inside the inverted denominator. | Medium | Fall back to `simp only [Nat.cast_prod, Fintype.card_pi]` or do the cast push step-by-step. |
| `WithTop.prod_ne_top` may have a slightly different signature in v4.26.0 (some Mathlib revisions use `ENNReal.prod_ne_top`). | Low | Replace with `ENNReal.prod_ne_top` or write the proof explicitly via `Finset.prod_lt_top_iff` + `Fintype.card_pos`. |
| `Fintype.card_subtype` signature in v4.26.0 takes `(p : α → Prop)` as explicit arg but may require `[DecidablePred p]` instance from `classical`. | Trivial | The `classical` tactic at the start of the proof supplies this; if not, add `[DecidablePred (fun f : (∀ k, β k) => b = f i)]` to the inner `have`. |
| The `Equiv` structure refine may need explicit type annotations on `toFun`/`invFun` to help inference. | Trivial | Annotate types explicitly. |

None of these requires a new Mathlib bearer; each is a routine
elaboration-time adjustment within Lean 4's current Mathlib API
surface.

## 4. Verification

- **`gh pr list -R rjwalters/lean-genius --search "prob-method-lovasz-local-oq-01 in:title" --state open`** at pre-claim probe (~00:30 UTC, 2026-05-14): 0 open PRs. Last merge: S5c PREP (#18930) at 23:06 UTC (~1.5h lead time, well outside the 30-min same-slug race window).
- **Pre-push probe** will re-verify before push.
- **No `.lake` build attempted** (lake symlink loop blocks Docker; per `feedback_researcher_lake_symlink_loop_and_wipe.md`).
- **All bearer names** verified at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`) per the S4a/S4b/S5b/S5c PREP audits; this ACT does not re-audit but inherits those certifications.

## 5. Files changed

- `proofs/Proofs/MoserTardos.lean` — +113 LOC; 3 new declarations
  (helper + 2 lemmas).
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — phase
  S5c PREP → S5b ACT; iteration 6 → 7; "Since" updated; new
  top-of-file S5b ACT history block (~80 LOC).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-14-s05b-act-helper-and-pack.md`
  — this file (new).
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json` —
  `currentState.phase` PREP → "S5b ACT"; `iteration` 6 → 7;
  `attemptCounts.total` 4 → 5; `focus` and `nextAction` updated;
  `knowledge.progressSummary` prepended; `lastUpdate` refreshed.
- **No gallery-meta drift** (`src/data/proofs/*/meta.json` untouched).
- **No `leanFiles` JSON drift fix** (lineCount/theoremCount mismatch in
  the research JSON is the documented drift class
  `feedback_mechanic_linecount_drift_class_unshippable.md`; out of scope
  for this PR).

## 6. Honesty

- **Not Lean-checked locally.** Build is pending per the `.lake`
  symlink-loop trap. Each bearer name is verified at the pinned Mathlib
  SHA via the S4a/S4b/S5b/S5c PREP audits, but the tactic sequence has
  not been run.
- **Two recipe deviations were necessary** (§2 above). Both are
  mechanical fixes to the final ENNReal-cancellation `rw` chain;
  neither changes the overall strategy.
- **The `h_fiber` Equiv construction** in the helper is a hand-traced
  port of the S5c PREP §3 sketch. The `simp [Equiv.piSplitAt]` (unfold)
  is used for all three subgoals (a/b/c) for robustness over the
  `@[simps]` autogenerated names; if doctor finds that `simp` does not
  fire as expected, the in-doc fallback (§3 risk #1) gives the explicit
  rewrite chain.
- **No upstream Mathlib PR** is opened; the helper is `private` and
  scoped to `MoserTardos.lean`. A future Mathlib upstream PR could
  consider promoting `marginal_uniformOfFintype_pi` to
  `Mathlib.Probability.Distributions.Uniform.Pi`.

## 7. Next action

Per `state.md` roadmap, S6 PREP is the next iteration. Two parallel
branches:

- **OQ-01-A.3 / `LLLAdmissibleUniform`** — refine `LLLAdmissible` with
  a uniform-draw probability field; prove the faithful-link lemma
  `prob i = (∑ v ∈ univ.filter (isBad i), 1) / (Fintype.card P.State)`.
  Estimated ~150 LOC.
- **OQ-01-B / `WitnessTree` skeleton** — `inductive WitnessTree`,
  `def isProper`, and the witness-validity lemma. Estimated ~200 LOC.

Both branches consume the marginal/independence pack shipped here as
input. The choice between A.3 and B at S6 is a research-strategy
decision (the marquee phase-1 / OQ-01-B route bypasses A.3 if witness
trees can be defined independently of the uniform-draw faithful link).

## 8. References

- **S4a PREP (Mathlib audit)**: `2026-05-13-s04a-prep-resampleAt-marginal-lemma-mathlib-audit.md` (PR #18477).
- **S4b PREP (`piSplitAt` discharge)**: `2026-05-13-s04b-prep-marginal-piSplitAt-discharge.md` (PR #18580). §6 = `_inside`, §7 = `_indep`.
- **S5 ACT (`_outside` lemma)**: `2026-05-13-s05-act-outside-marginal.md` (PR #18629).
- **S5b PREP (ENNReal cancellation)**: `2026-05-13-s05b-prep-helper-ennreal-cancellation.md` (PR #18683). §2 = the closing arithmetic block.
- **S5c PREP (`h_fiber` audit)**: `2026-05-13-s05c-prep-h-fiber-card-equiv-audit.md` (PR #18930). §3 = the sorry-free `h_fiber` Lean block.
- **Mathlib v4.26.0 pin**: `proofs/lake-manifest.json` → `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. `proofs/lean-toolchain` → `leanprover/lean4:v4.26.0`.
- **Build trap**: memory `feedback_researcher_lake_symlink_loop_and_wipe.md`.
- **Branch-isolation**: shipped from a fresh branch off `origin/main`, not from the worktree's prior `research/chebyshev-bounds-oq-04-oq-01-state-sync-1778719301` branch (which has an open PR #18958 from a different slug). Per `feedback_researcher_push_onto_open_pr_branch_contamination.md`.
