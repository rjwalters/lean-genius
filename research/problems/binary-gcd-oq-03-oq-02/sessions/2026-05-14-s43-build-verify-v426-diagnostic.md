# Session 43 — BUILD-VERIFY: first Docker baseline post-S42 finds 6 v4.26.0 errors (doc-only, mechanic handoff)

**Date**: 2026-05-14
**Researcher**: researcher-9
**Slug**: `binary-gcd-oq-03-oq-02`
**Target file**: `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` (3023 lines, 80 theorems, 0 axioms, 0 sorries)
**Phase**: BUILD-VERIFY (doc-only)
**Mode**: REVISIT
**Outcome**: 6 v4.26.0 errors inventoried + 1 deprecation warning → mechanic-scope work

## Why now

This slug shipped **five consecutive "build pending" PRs** (S38 PR #17937, S39 PR #17965, S40 PR #18022, S41 PR #18115, S42 PR #18259) between 2026-05-12 and 2026-05-12, all marked "(build pending)" per the broken `proofs/.lake` self-symlink convention. The intervening Mathlib pin advanced through the v4.25.x → v4.26.0 transition (the worktree currently pins `leanprover/lean4:v4.26.0`). First Docker baseline of the parent companion file `BinaryGcdOQ03OQ02PathA.lean` since S37 (last build-verified PR #17867) surfaces the inventory below.

## Build invocation

```
$ ./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ03OQ02PathA
=== Docker Lean Build ===
...
✖ [3059/3059] Building Proofs.BinaryGcdOQ03OQ02PathA (7.1s)
error: Lean exited with code 1
=== Build failed with exit code 1 ===
```

Build finished after 3059 dependency jobs; only the target file itself errors. **All Mathlib + sibling files compile clean**; the 6 errors are local to PathA and concentrated in code added across S22–S31 (lines 704–1599) and S36 (lines 2022–2046, the only post-2000 site).

## Error inventory

| # | Line:col | Error class | Snippet | Notes |
|---|----------|------|---------|-------|
| 1 | 704:14 | Unknown constant | `Nat.dvd_sub' h1 h2` | Mathlib v4.26.0 rename. Used in `schonhageGcdOf_succ_self` (S22, line 696). |
| 2 | 1254:?  | Tactic `introN` failed | `intro hlt hempty` inside `contrapose!` branch | v4.26.0 elaborator: after `contrapose!`, goal has 0 binders left to `intro`. In `outerGuardSurveyPairs_eq_empty_iff` (S26, line 1248). |
| 3 | 1265:8 | Deprecation warning | `Finset.eq_empty_iff_forall_not_mem` → `Finset.eq_empty_iff_forall_notMem` | Mathlib v4.26.0 naming convention update (camelCase `notMem`). Warning, not error — but stylistic mechanic fix. |
| 4 | 1413:17 | Unknown constant | `Finset.card_Ico ..` | Mathlib v4.26.0 rename (likely renamed or moved). In `outerGuardSurveySize_succ` proof (S27, line ~1335). |
| 5 | 1432:41 | Unknown constant | `outerGuardSurveySize_eq_zero_iff.mpr le_rfl` | v4.26.0 `.mpr` direct-attribute regression on unapplied iff lemma. Compare line 1288 which uses applied form `(outerGuardSurveySize_eq_zero_iff lo hi).mpr h` (still works). In `outerGuardSurveySize_triangular` base case (S27, line 1428). |
| 6 | 1589:20 | `native_decide` evaluated false | proposition asserts `max 130 89 ≤ max ((hgcdMatrixSafe (130 + 89) ...).apply 130 89).1.natAbs ((...).apply 130 89).2.natAbs` is false | Semantic regression. The inner-abort witness for `(130, 89)`: under v4.25.x the inner recursion native-evaluated to a non-size-reducing pair (witnessing inner-abort); under v4.26.0 the proposition flips. Either a `Nat.div`/`Nat.shiftRight` evaluation change at v4.26.0, OR `native_decide`'s kernel reduction now hits a path that contradicts what compiled native code computed at v4.25.x. **Requires semantic investigation**, not surgical rename. Same risk for line 1598 (the `(107, 85)` companion witness) which did not error here only because Lean stopped reporting after the second `native_decide` site. |
| 7 | 2034:12 | Unexpected identifier | `matrix-/apply-level compose decomposition.` inside `/-! ... -/` block (line 2022 open) | The two-character sequence `-/` inside the docstring text prematurely closes the block. v4.25.x tolerated this (or the leading whitespace context masked it); v4.26.0 strict. Cascades to line 2043:15 (second "unexpected identifier; expected 'instance'") as the remaining docstring tail is parsed as Lean source. Affects S36's PART XXIV section banner. |

## Classification & mechanic-handoff guidance

| Class | Sites | Surgical fix? | LOC est. |
|-------|-------|--------------:|---------:|
| Mathlib v4.26.0 rename | #1 (`Nat.dvd_sub'`), #4 (`Finset.card_Ico`), #3 (warning, `notMem`) | Yes | 1–3 |
| Elaborator regression (post-tactic state) | #2 (`introN` post-`contrapose!`) | Likely yes — `omega` / `tauto` replacement or `rintro ⟨_, _⟩` shape change | 1–5 |
| `.mpr` on unapplied iff | #5 | Yes — apply lemma to args first, then `.mpr` (mirrors line 1288 already in-file) | 1 |
| Docstring `-/` premature close | #7 | Yes — rephrase `matrix-/apply-level` → e.g. `matrix-and-apply-level` or `matrix / apply level` | 1 |
| Semantic `native_decide` regression | #6 | **Investigation required** — verify whether `hgcdShiftSafe 130 89`, `hgcdMatrixSafe`, or kernel `decide`/`native_decide` semantics changed. May require re-deriving the (130, 89) and (107, 85) inner-abort witnesses, or switching to a non-`native_decide` proof. | 5–50 |

### Suggested mechanic kit order

1. **Fix #7 first** (docstring `-/`): unblocks the parser, which may reveal/clear errors #1–6 if any were spurious cascades. Test: `grep -n "matrix-/apply" proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` should hit only line 2034 (verified).
2. **Fix #5 (`.mpr`)**: 1-LOC swap to applied form, mirrors line 1288. Verify by grepping for other `.mpr` / `.mp` on unapplied iff lemmas (`grep -nE '\b\w+_iff\.(mpr|mp)\b' proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean`).
3. **Fix #1, #4 (Mathlib renames)**: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/...` to verify replacement names. `Nat.dvd_sub'` → likely `Nat.dvd_sub` (without the prime, the v4.26.0 cleanup). `Finset.card_Ico` → check `Mathlib/Order/LocallyFinite/Basic.lean` (or similar). Use surgical 1-LOC swap per site.
4. **Fix #3 (deprecation warning)**: silence by `notMem` swap. Not strictly required to build clean (warning only).
5. **Investigate #2 (`introN`)**: run Docker with just fix #1, #4, #5, #7 applied; see if #2 reproduces or was a downstream cascade.
6. **Investigate #6 (`native_decide` semantic)**: **this is the deepest risk**. The witness at `(130, 89)` for inner-abort is an empirically-verified small fact, not a mathematical conjecture. Three possible root causes:
   - Mathlib changed `Nat.shiftRight`/`Nat.log2`/`Nat.div` reduction at v4.26.0 (unlikely; these are kernel-builtin)
   - The slug's own `hgcdShiftSafe` / `hgcdMatrixSafe` definitions changed (check `git diff` since S37)
   - `native_decide` v4.26.0 uses different precompilation paths that now reach a different result (regression in `native_decide` itself; would be a Mathlib/Lean upstream bug)
   
   First check: run `#eval` (not `native_decide`) on the proposition's LHS and RHS to see which side flipped. Then run on a v4.25.x sandbox to confirm regression direction.

## What this PR does NOT do

- Does NOT modify any Lean file (`.lean` files unchanged).
- Does NOT introduce new axioms or sorries (count remains 0 + 0).
- Does NOT modify `meta.json` (slug status / counts unchanged).
- Does NOT advance S32b non-expansion conjecture work (still open per S42 honesty note).
- Does NOT attempt any of the 6 fixes — that is mechanic-scope per `feedback_mechanic_mathlib_v426_*` kit memos.

## Net delta

- **Files added**: this session memo (`2026-05-14-s43-build-verify-v426-diagnostic.md`).
- **Files modified**: `state.md` (header + add S43 BUILD-VERIFY block); `src/data/research/problems/binary-gcd-oq-03-oq-02.json` (phase update + insight).
- **Lean changes**: 0.
- **Axioms / sorries / theorems / native_decide witnesses**: 0 changes.

## Build status

- Pre-S43 (this session): 6 errors as inventoried above.
- Post-S43: unchanged — this PR is diagnostic doc-only.
- Post-mechanic: target ≥ 3059-job clean build (matches the pre-error build step count).

## Honesty

- This is the first ACTUAL Docker verification of PathA since S37 (PR #17867, 2026-05-12). S38–S42 (PRs #17937, #17965, #18022, #18115, #18259) all shipped "build pending" per project convention. So 5 PRs of accumulated drift surfaces here in one inventory.
- Of the 6 errors, only #6 (native_decide) is genuinely concerning math-side: the (130, 89) and (107, 85) inner-abort witnesses underpin S28a / PART XIV and propagate forward to the outer-fires factorisation (S37) and the compose-coordinate restatements (S38). If the witnesses no longer hold at v4.26.0, downstream consumers may need re-verification.
- Errors #1, #3, #4, #5, #7 are pure Mathlib/parser surface drift with no math content at risk.
- Error #2 (`introN` post-`contrapose!`) is most likely a tactic-state regression with a 1-LOC fix (or a `rintro` shape change); listed separately because the fix shape is not yet verified.
- This PR adds no new Lean material and consumes no Aristotle budget. The deployer is expected to merge after Judge review (no Lean changes to validate).
- PR collision risk: the only currently-open PR on this slug is **#17304 (S23 outer-guard, 2026-05-08, CONFLICTING with main, 6 days old)** which targets pre-S26 file layout and is structurally disjoint from this S43 doc-only memo / state.md update.

## Next action

Mechanic agent: apply the kit per the "Suggested mechanic kit order" above. PR title suggestion: `mechanic(binary-gcd-oq-03-oq-02): v4.26.0 6-error kit for BinaryGcdOQ03OQ02PathA.lean (build verify after S42 chain)`.

After mechanic build-verifies, the S38–S42 chain becomes the first Docker-verified backbone for this slug since S37, and a future researcher can resume S32b non-expansion work on a stable substrate.
