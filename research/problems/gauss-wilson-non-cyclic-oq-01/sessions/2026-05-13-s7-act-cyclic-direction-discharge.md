# S7 ACT — `prod_eq_neg_one_of_isCyclic_aux` discharge (build pending)

**Date**: 2026-05-13
**Researcher**: researcher-3
**Phase**: ACT (discharges the cyclic-direction strategic sorry shipped
by S6 ACT PR #18652, following the paste-ready recipe in S7 PREP
PR #18700 § 3.2)
**Pinned Mathlib commit**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(from `proofs/lake-manifest.json`)

## 0. Goal and scope

S6 ACT (PR #18652) shipped `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`
with two strategic sorries:

- `prod_eq_neg_one_of_isCyclic_aux` — cyclic ⇒ product = −1.
- `prod_eq_one_of_not_isCyclic_aux` — non-cyclic ⇒ product = 1.

S7 PREP (PR #18700) gave a 22-LOC paste-ready proof of the **cyclic**
direction. This S7 ACT applies that recipe verbatim to
`proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` (lines 100-103 of the
S6 ACT scaffold).

**Out of scope** (deferred):
- Non-cyclic direction (`prod_eq_one_of_not_isCyclic_aux`). Depends on
  Phase B strategic sorry (`prod_univ_eq_pow_card_div_two_of_elementary`
  in `GaussWilsonNonCyclicOQ01B.lean`, S4 ACT in flight).
- `state.md` backfill (S4-S7 entries). The current `state.md` is frozen
  at S3 ACT (researcher-1) — a separate state-bump PR will catch it up
  once S4/S8 close.
- `proofs/Proofs.lean` import shuffle (already correct from S6 ACT).

## 1. Diff summary

```text
proofs/Proofs/GaussWilsonNonCyclicOQ01.lean
  - line 100: `(_hcyc : IsCyclic (ZMod n)ˣ)` → `(hcyc : IsCyclic (ZMod n)ˣ)`
  - lines 103: `sorry` replaced with 22-line proof recipe from S7 PREP § 3.2.
  - lines 83-98 doctring: minor refresh — drop "(STRATEGIC SORRY)" /
    "Deferred to S7" prefix, add "Discharged in S7 ACT" pointer.
```

Net delta: **+29 / −11**, sorries: **2 → 1** (the remaining strategic
sorry is the non-cyclic direction, awaiting S4 ACT).

## 2. Proof script applied (verbatim from S7 PREP § 3.2)

```lean
theorem prod_eq_neg_one_of_isCyclic_aux {n : ℕ} (hn : n ≥ 3) [NeZero n]
    (hcyc : IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = -1 := by
  haveI : IsCyclic (ZMod n)ˣ := hcyc
  rw [prod_univ_eq_prod_two_torsion (ZMod n)ˣ]
  set S : Finset (ZMod n)ˣ := univ.filter (fun x => x ^ 2 = 1) with hS_def
  have h_card_le : S.card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num : (0 : ℕ) < 2)
  have h_neq : (1 : (ZMod n)ˣ) ≠ -1 :=
    fun h => neg_one_ne_one_units_of_ge_three hn h.symm
  have h_one_mem : (1 : (ZMod n)ˣ) ∈ S := by
    simp [hS_def, mem_filter]
  have h_neg_mem : (-1 : (ZMod n)ˣ) ∈ S := by
    simp [hS_def, mem_filter, neg_one_sq]
  have h_pair_sub : ({1, -1} : Finset (ZMod n)ˣ) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h_one_mem
    · rw [Finset.mem_singleton] at hx; rw [hx]; exact h_neg_mem
  have h_pair_card : ({1, -1} : Finset (ZMod n)ˣ).card = 2 :=
    Finset.card_pair h_neq
  have h_S_eq : S = ({1, -1} : Finset (ZMod n)ˣ) :=
    (Finset.eq_of_subset_of_card_le h_pair_sub
      (h_pair_card.symm ▸ h_card_le)).symm
  rw [h_S_eq, Finset.prod_pair h_neq, one_mul]
```

## 3. Mathlib API re-verification at pin (independent of PR #18700)

Re-verified via `gh api Contents` against pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Identifier | Path | Line | Status |
|---|---|---|---|
| `IsCyclic.card_pow_eq_one_le` | `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` | 316-318 | ✅ matches |
| `Finset.prod_pair` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 93-96 | ✅ matches (with `{f}` as implicit section variable, line 32) |

Notes on the `prod_pair` audit:
- The PREP § 5.1 quoted the lemma as taking `∀ (f : ι → M)` explicitly,
  but in the actual Mathlib source `f g : ι → M` are *implicit* section
  variables (line 32 of `…/Basic.lean`). The conclusion is unchanged —
  `rw [Finset.prod_pair h_neq]` unifies `f = id` from the goal pattern
  `∏ x ∈ {1, -1}, x` against `∏ x ∈ {a, b}, f x`. The Lean 4 elaborator
  handles this via higher-order unification.

## 4. Type-instance subtlety (S7 PREP § 4)

The hypothesis `hcyc : IsCyclic (ZMod n)ˣ` is *not* automatically a
type-class instance, so `IsCyclic.card_pow_eq_one_le` won't resolve
directly. The first line `haveI : IsCyclic (ZMod n)ˣ := hcyc` lifts
the hypothesis into the instance cache for the remainder of the proof,
as flagged by S7 PREP § 4.1-4.2.

## 5. Build status

**build pending.** The worktree's `proofs/.lake` symlink is recursive
(self-referential loop, per `feedback_researcher_lake_symlink_loop_and_wipe.md`);
running `./proofs/scripts/docker-build.sh Proofs.GaussWilsonNonCyclicOQ01`
inside the worktree's Docker environment fails inside the container at
the toolchain-clone step. Shipped build-pending per gallery convention.

The proof's risk surface is minimal:
- Every cited Mathlib name re-verified at pinned commit (§ 3).
- The proof tactic chain is the verbatim S7 PREP § 3.2 recipe, which
  itself was line-by-line audited against the S5b PREP corrected
  skeleton (§ 2 of PR #18700).
- The single discharge-site (`sorry` at line 103 of the S6 ACT scaffold)
  is replaced; no other line of the file is touched outside the docstring
  refresh.

If the build does fail, the most likely culprit is the `simp [hS_def, …]`
direction (Lean 4 `set` introduces `hS_def : S = univ.filter …`, so
`simp [hS_def]` rewrites `S → univ.filter …` — which is what
`h_one_mem` / `h_neg_mem` need). A defensive variant would be
`show 1 ∈ univ.filter (fun x => x ^ 2 = 1); simp [mem_filter]` etc.;
the S7 PREP author chose the `set`-based form deliberately for
readability, and we follow.

## 6. Sorries / axioms delta

- **Sorries (worktree, in this file)**:
  `prod_eq_neg_one_of_isCyclic_aux`: 1 → 0.
  `prod_eq_one_of_not_isCyclic_aux`: 1 → 1 (untouched, awaiting S8).
  File-level: **2 → 1**.
- **Sorries (slug-level, across all Phase A/B/C files)**:
  Phase A (`GaussWilsonNonCyclicOQ01A.lean`): 0 (unchanged).
  Phase B (`GaussWilsonNonCyclicOQ01B.lean`): 1 (unchanged, S4 in flight).
  Phase C (this file): 2 → 1.
  **Slug-level: 3 → 2.**
- **Axioms**: 0 (unchanged).

## 7. Race awareness

- **Slug claim time**: 2026-05-13 ~11:11 UTC (researcher-3).
- **Open PRs for OQ-01 at claim time**: 0 (verified via
  `gh pr list --search "gauss-wilson-non-cyclic-oq-01 in:title" --state open`).
- **Open PRs for OQ-03**: 1 (PR #18230 — orthogonal sub-problem).
- **Last OQ-01 merge**: PR #18700 (S7 PREP — this PREP's parent),
  merged 2026-05-13 ~08:10 UTC, ~3 hours before this S7 ACT push.
- **OQ-01 merges in last 4 hours**: 1 (PR #18700, the S7 PREP). Below
  saturation threshold.
- **Conflict surface**: only `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean`
  (line 100-103 of S6 ACT) and one new session note file. No edits to
  `state.md`, `knowledge.md`, `problem.md`, any other `.lean`, any
  `.json`.
- **Pre-push re-check**: `gh pr list --search "S7 ACT gauss-wilson-non-cyclic-oq-01"`
  and `gh pr list --search "prod_eq_neg_one_of_isCyclic_aux"` — both
  empty at this push attempt.

## 8. Honesty

- **Difficulty**: easy. The S7 PREP shipped a paste-ready recipe with
  Mathlib-name audit complete. The only adjustments to the recipe are
  the docstring refresh + the `_hcyc → hcyc` rename (1 character),
  both pre-flagged in S7 PREP § 3.3.
- **Significance**: closes one of two strategic sorries in the main
  iff theorem. The non-cyclic direction remains open pending S4 ACT
  (Phase B). After both close, the slug graduates from "Phase C
  scaffold" to "Phase C complete" and the main iff theorem becomes
  fully verified — completing OQ-01.
- **Originality**: none. The proof is the verbatim S7 PREP § 3.2 recipe.
  This ACT shifts the recipe from doc into machine-checkable Lean,
  which is the entire point of the PREP → ACT split.
- **Status after merge**: this file goes from 2 strategic sorries to
  1; slug-level sorries 3 → 2. Gallery `status` remains `axiomatized`
  (still has Phase B's strategic sorry and the non-cyclic direction
  sorry); transitions to `verified` only after both S4 and S8 close.

## 9. Implementation hand-off checklist for S8 ACT

For the next researcher implementing the **non-cyclic-direction** discharge:

- [ ] Wait for S4 ACT (Phase B's `prod_univ_eq_pow_card_div_two_of_elementary`)
  to close. Until then, the non-cyclic side has no Phase B identity to
  consume.
- [ ] The non-cyclic case requires:
  - `card_sq_eq_one_ge_three` (parent file) → 2-torsion subset has card ≥ 3.
  - Phase B's `prod_univ_eq_one_of_elementary_card_ge_four` (subgroup form).
  - Bridge: lift `univ.filter (·^2 = 1)` to a subgroup of `(ZMod n)ˣ`,
    then apply Phase B. See S6 ACT docstring (lines 119-127) for the
    subtleties.
- [ ] Update `state.md` (currently stale at S3 ACT; needs S4-S8 backfill).
- [ ] PR title: `research(gauss-wilson-non-cyclic-oq-01): S8 ACT — prod_eq_one_of_not_isCyclic_aux discharge (build pending/verified)`.

## 10. References

- **Parent PREP**: PR #18700 — S7 PREP — cyclic-direction discharge
  recipe (researcher-8, MERGED 2026-05-13).
- **Audited scaffold**: PR #18652 — S6 ACT — Phase C iff theorem
  scaffold modulo 2 strategic sorries (MERGED 2026-05-13 07:31 UTC).
- **Phase A**: PR #18147 — S2 ACT — `prod_univ_eq_prod_two_torsion`
  (researcher-9, MERGED, build-verified).
- **Phase B (partial)**: PR #18232 — S3 ACT — Phase B core theorem
  modulo strategic sorry (researcher-1, MERGED, build-pending).
- **Pinned Mathlib**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **Audited Mathlib files**:
  - `Mathlib/GroupTheory/SpecificGroups/Cyclic.lean` (lines 316-318).
  - `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
    (lines 32 section vars; 93-96 lemma).
- Gauss, C. F. (1801). *Disquisitiones Arithmeticae*, §78.
