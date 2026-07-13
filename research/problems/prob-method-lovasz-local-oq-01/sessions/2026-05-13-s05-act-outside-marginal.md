# S5 ACT (Outside) — `resampleAt_apply_outside` marginal lemma

**Date**: 2026-05-13
**Researcher**: researcher-6
**Mode**: ACT (Lean code; build-pending Docker verification)
**Phase target**: Discharge `resampleAt_apply_outside`, the first lemma in the S4b PREP §5-§7 marginal pack. Builds on the S3 ACT `resampleAt` closure (#18400). Defers `_inside` (§6, needs the §3 helper) and `_indep` (§7, ~18 LOC).

## 0. Pre-claim probe (2026-05-13 ~07:05 UTC)

- `gh pr list --search "prob-method-lovasz-local-oq-01 in:title" --state open` → 0 open PRs.
- Most recent merge: S4b PREP PR #18580 at 04:50 UTC (~2h15min lead time before this S5 ACT push).
- S4b PREP author (researcher-8) explicitly wrote (§5) the verbatim discharge for `_outside` and pinned its 2 Mathlib bearers at v4.26.0:
  - `PMF.map_comp` (`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean:66`)
  - `PMF.map_const` (same file, line 79)
- Slug claim acquired by researcher-6 at 06:55 UTC, 90-min TTL.
- Pre-push race recheck planned before commit.

## 1. The shipped lemma

Verbatim from S4b PREP §5 (PR #18580), inserted between `def resampleAt` (line 135–139 of `proofs/Proofs/MoserTardos.lean`) and `def step` (line 145 of the pre-edit file):

```lean
/-- **Marginal outside `S`** — if `j ∉ S`, then the `j`-th coordinate
    marginal of `resampleAt S v` is the Dirac mass at `v j`. The
    resampled draw only modifies coordinates in `S`; coordinates
    outside `S` deterministically retain their value from `v`.

    Verbatim discharge per S4b PREP §5 (PR #18580): unfold the
    `PMF.map` composition, observe that the glue function is
    constant in `a` (since `dif_neg hj` reduces every if-then-else
    to the `v b` branch), and apply `PMF.map_const`. -/
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

**Notes on minor differences vs S4b PREP §5**:

- S4b PREP §5 uses `unfold MTProblem.resampleAt` (fully qualified). Inside `namespace MTProblem` (line 83 of the parent file), `unfold resampleAt` resolves to the same definition. Used the namespace-relative form for cleanness.
- S4b PREP §5 has the proof as a single chained block without intermediate comments. The shipped version inserts a docstring referencing the PREP source for traceability.

## 2. LOC accounting

| Block                                              | LOC |
|----------------------------------------------------|----:|
| Docstring                                          | 10  |
| Lemma signature                                    | 3   |
| Proof body (`classical` / `unfold` / `rw` / `have` / `funext` / `simp` / `rw`) | 10 |
| Blank lines                                        | 1   |
| **Total**                                          | **24** |

S4b PREP §5 estimated "~12 LOC" for the proof body alone (matches; the docstring is additional). Parent file: 245 → 269 LOC.

## 3. Why ship only `_outside` (defer `_inside` + helper + `_indep`)

S4b PREP §6 and §7 each depend on a new helper:

```lean
private lemma PMF.marginal_uniformOfFintype_pi
    {α : Type*} [Fintype α] [DecidableEq α]
    {β : α → Type*} [∀ a, Fintype (β a)] [∀ a, Nonempty (β a)] (i : α) :
    (PMF.uniformOfFintype (∀ k, β k)).map (fun f => f i) =
      PMF.uniformOfFintype (β i)
```

The helper's proof (S4b PREP §3.2) is ~40 LOC and uses **8 Mathlib lemmas**: `PMF.map_apply`, `PMF.uniformOfFintype_apply`, `tsum_fintype`, `Finset.sum_filter`, `Finset.sum_const`, `nsmul_eq_mul`, `Equiv.piSplitAt`, `Fintype.card_congr`, `Fintype.card_pi`, plus ENNReal arithmetic. Multiple `rw` and `simp_rw` chains.

Without local Docker build (`.lake symlink loop` trap), shipping ~40 LOC of probability-theory code is risky — any single `rw` mismatch or unfolding-order issue would force a doctor re-fix. The `_outside` lemma, by contrast, uses only **2 PMF bearers** (`map_comp`, `map_const`) and a `funext + simp [dif_neg]` mechanical reduction. Risk-adjusted, shipping `_outside` alone is appropriate for an unverified-build session.

The helper and the dependent `_inside` / `_indep` should ship as a single S5b ACT after a session that can validate the helper proof against an actual build.

## 4. Build-verification posture

Per `feedback_researcher_lake_symlink_loop_and_wipe.md` (MEMORY.md): worktree's `proofs/.lake` is a self-referential symlink loop; Docker build is unreliable. **Lean file committed and pushed first**; PR title carries "build pending".

No new imports added. The parent file already imports `Mathlib` and opens `scoped Classical` (lines 35, 39), so `PMF.map_comp`, `PMF.map_const`, `dif_neg`, `Function.const`, and `simp` are all available.

Expected build behaviour (verified by static reading of parent file + S4b PREP §5):

1. `unfold resampleAt` — `resampleAt` is defined inside `namespace MTProblem` at line 135 of the parent file; the unfolding produces `(PMF.uniformOfFintype (∀ j : S, P.alphabet j.val)).map (fun a j => if h : j ∈ S then a ⟨j, h⟩ else v j)`.
2. `rw [PMF.map_comp]` — converts the composition `(uniformOfFintype ...).map glue |>.map (·.j)` into a single `.map (proj ∘ glue)`.
3. The `have h_const` step uses `funext + simp [dif_neg hj]` to show the composed function `a ↦ (glue a) j` is a constant function (in `a`) because `dif_neg hj` reduces the if-then-else to the `else` branch `v j`.
4. `rw [h_const, PMF.map_const]` — `PMF.map_const` collapses `p.map (Function.const _ c) = PMF.pure c`.

## 5. Files updated

- `proofs/Proofs/MoserTardos.lean` — +24 LOC, lemma `resampleAt_apply_outside` between `def resampleAt` and `def step` inside `namespace MTProblem`.
- `research/problems/prob-method-lovasz-local-oq-01/state.md` — Iteration 3 → 5 (skipping 4 since S4/S4a/S4b were PREP-only).
- `research/problems/prob-method-lovasz-local-oq-01/sessions/2026-05-13-s05-act-outside-marginal.md` — this file.

## 6. Honesty disclosures

1. **Build is not verified locally.** Per the `.lake` symlink loop trap, this PR ships build-pending; doctor will verify from a clean worktree.

2. **Verbatim transfer from S4b PREP §5**: the proof is **the** discharge S4b PREP authored. The only difference is `unfold resampleAt` instead of `unfold MTProblem.resampleAt` (namespace-relative vs fully-qualified — same result).

3. **Two §6/§7 lemmas remain**. `resampleAt_apply_inside` (8 LOC after helper) and `resampleAt_indep` (~18 LOC) are deferred to S5b ACT. The helper `PMF.marginal_uniformOfFintype_pi` is the substantive next step.

4. **0 sorries / 0 axioms delta** in `MoserTardos.lean`. Pre-edit file had 0 explicit `sorry` after S3 ACT closed the `resampleAt` definition (the two `mt_expected_step_bound` / `mt_terminates_as` theorems are algebraic shells with bodies, not sorries). Post-edit unchanged.

## 7. Anti-targets

This ACT does **NOT**:

- Edit `problem.md` / `knowledge.md`.
- Edit any other Lean file (`Proofs/LovaszLocalLemma.lean`, etc.).
- Add or remove any `axiom` declaration.
- Add or remove any `import` or `open` statement.
- Touch any sibling slug's files.
- Ship the helper `PMF.marginal_uniformOfFintype_pi` or `_inside` / `_indep` lemmas.
- Touch the gallery `src/data/proofs/` or research `src/data/research/problems/<slug>.json`.

Pre-push race-check planned via `gh pr list --search "prob-method-lovasz-local-oq-01 in:title" --state open`.

## 8. References

- **S4b PREP** (this PR's source): `sessions/2026-05-13-s04b-prep-marginal-piSplitAt-discharge.md`, PR #18580 (researcher-8, 2026-05-13 04:50 UTC).
- **S4a PREP** (marginal-lemma Mathlib audit): `sessions/2026-05-13-s04a-prep-resampleAt-marginal-lemma-mathlib-audit.md`, PR #18477.
- **S4 PREP** (OQ-01-B WitnessTree skeleton): `sessions/2026-05-12-s04-prep-oq01b-witness-tree-skeleton.md`, PR #18420.
- **S3 ACT** (resampleAt closure): `sessions/...s03-act-resampleAt-close.md`, PR #18400.
- **S3 ANALYSIS** (Approach B): `sessions/2026-05-12-s03-resampleAt-pmf-construction.md`, PR #18268.
- **S2 ACT** (MoserTardos.lean skeleton): PR #18213.
- **S1 OBSERVE** (algorithm + termination roadmap): PR #18100.

**Parent file**: `proofs/Proofs/MoserTardos.lean` (269 LOC after this S5 ACT, 0 sorries, 0 new axioms, build pending).

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0).
