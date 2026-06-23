# S4 statement correction + mechanic PR #19072 build-verification

**Author:** researcher-12
**Date:** 2026-05-14 (~22:55 UTC)
**Phase:** ACT (S4 statement-fix sub-step; full S4 ACT proof still deferred)
**Slug:** `cramers-rule-oq-01-oq-02-oq-01-oq-01`
**Branch:** `research/cramers-oq01020101-s4-stmt-fix-...`
**Scope:** **slug-Lean + state.md + JSON + session doc.** No parent-file edits (those are mechanic PR #19072's scope).

## 0. Why this session and what it changes

Three load-bearing PREPs (S4b §7, S4c §3, S4e §6) all locked the same conclusion: the strategic sorry in `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` Part VI

```lean
theorem qdetN_step_eq_qdetF {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) F) (i j : Fin (n+1))
    (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹ = qdetF A i j := by  -- ← FALSE for i+j odd
  sorry
```

is **mathematically false for off-diagonal pivots**. S4c PREP §2 verified this by direct arithmetic on `A = ⟦1 2; 3 4⟧` at all four `(i,j)` pivot positions in `Fin 2 × Fin 2`:

| pivot | `qdetF` | `qdetN_step(M⁻¹)` | ratio | `(-1)^(i+j)` |
|-------|---------|-------------------|-------|--------------|
| (0,0) | −1/2    | −1/2              | +1    | +1           |
| (0,1) | −2/3    | +2/3              | −1    | −1           |
| (1,0) | −1      | +1                | −1    | −1           |
| (1,1) | −2      | −2                | +1    | +1           |

The correction is to carry an explicit `(-1)^(i+j)` factor on the RHS:

```lean
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j
```

The original statement merged in PR #18214 (S3 SCAFFOLD, 2026-05-12) and the four follow-on PREPs S4 / S4b / S4c / S4d / S4e (PRs #18346 #18409 #18525 #18563 #18751) progressively locked this correction, but the Lean file itself was never updated; this session lands that correction in the slug file. The strategic `sorry` remains (still S4 ACT's full-proof target per the ~55-LOC plan of S4e PREP §2/§3).

This session also **build-verifies the slug** by applying mechanic PR #19072's parent-file patches locally and running Docker — confirming both (a) that the mechanic PR's repair is sufficient to unblock the slug, and (b) that the corrected statement type-checks.

## 1. Pre-claim Docker baseline (confirmed parent-file blocker)

Pre-claim build of the slug from origin/main:

```
./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01
...
error: Proofs/CramersRuleOQ01OQ02OQ01.lean:241:35: unsolved goals
error: Proofs/CramersRuleOQ01OQ02OQ01.lean:249:49: unsolved goals
error: Proofs/CramersRuleOQ01OQ02OQ01.lean:273:52: Tactic `rewrite` failed:
   Did not find an occurrence of the pattern ?m.69⁻¹ * ?m.69
   in the target expression (A.det⁻¹ * A.det) • b = b
error: Lean exited with code 1
error: build failed
=== Build failed with exit code 1 ===
```

The parent-file blocker per PR #19036's inventory still reproduces on today's `origin/main` (commit `2afb1b79c0a`). The slug file never elaborates because `Proofs.CramersRuleOQ01OQ02OQ01` fails to compile. **Mechanic PR #19072 (open, awaiting deploy/merge) has the repair and was not yet merged at session start.**

## 2. Local mechanic-PR-overlay build verification

To verify (a) PR #19072's parent fix is sufficient and (b) the statement correction type-checks on top, the session applied PR #19072's diff as a transient overlay in the worktree, then made the slug change, then Docker-built:

```bash
gh pr diff 19072 --repo rjwalters/lean-genius > /tmp/researcher-12-mechanic-19072.patch
git apply /tmp/researcher-12-mechanic-19072.patch    # mechanic parent fixes
# … apply slug statement correction in proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean
./proofs/scripts/docker-build.sh Proofs.CramersRuleOQ01OQ02OQ01OQ01
```

**Build result (combined): ⚠ [3060/3060] Built Proofs.CramersRuleOQ01OQ02OQ01OQ01 (2.7s) — Build completed successfully (3060 jobs).** The only `warning: declaration uses 'sorry'` is `Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean:282:8` (the corrected `qdetN_step_eq_qdetF` strategic sorry, still S4 ACT's target). No `error:` lines. All `block3_*_det` / `block3_*_*` linter warnings are pre-existing in the parent file under the mechanic patch (and are inherited from `[Field F]` not exercising the `[DivisionRing D]` variable). Slug file is fully clean under the mechanic-overlay + corrected statement.

The mechanic patches were then reverted before committing this session's work, so the PR diff is slug + docs only (no overlap with PR #19072).

## 3. The statement correction itself

Diff against `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` Part VI:

- Theorem statement: RHS changed from `qdetF A i j` to `(-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j`.
- Header docstring (~line 45): "recovers `qdetF A i j = det(A) / det(M)`" → "recovers `(-1)^(i+j) * qdetF A i j = det(A) / det(M)` up to the cofactor sign factor".
- Main-results table entry (~line 58): now annotates "signed-RHS form `(-1)^(i+j) * qdetF`".
- Theorem docstring (~line 244–264): expanded with the S4c PREP §2 four-pivot verification reasoning, an explicit "why the `(-1)^(i+j)` factor" paragraph, and a pointer to the S4e PREP §2 `Matrix.det_eq_sum_mul_adjugate_row` proof strategy.

The strategic `by sorry` is unchanged; this is purely a statement-type correction. The `qdetN_step_zero_minv` companion theorem is unaffected (its `Minv = 0` base case does not fire the field-consistency identity; the sign factor only appears when `M⁻¹ = (minorIJ).⁻¹` is supplied, per S4c PREP §3.2).

## 4. Why this is real progress (not cosmetic)

A strategic `sorry` is a placeholder for a *true* lemma. If the statement is false, the `sorry` is a trap: a future agent could "close" it with an incorrect proof, or rely on the false statement in a downstream proof, propagating the falsity. By correcting the statement before S4 ACT, this session:

- **Removes the latent error** from the slug file.
- **Aligns the Lean code with the verified mathematics** (S4c PREP §2's four-pivot quadrant check + S4e PREP §6's algebraic cross-check).
- **Makes the strategic sorry actually provable** — under the old statement, `qdetN_step_eq_qdetF` is unprovable for any off-diagonal pivot (the LHS and RHS differ in sign).

Without this correction, even a fully-implemented S4 ACT proof would have to either fail or work around the false statement. Net: this is an upstream blocker for the ~55-LOC S4 ACT proof that S4e PREP §3 itemises.

## 5. Race-safety / PR scope

**Diff scope (committed):**

- `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` (statement + docstring updates; ~10 LOC effective)
- `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/state.md` (phase + iter + lastUpdate refresh)
- `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-14-s4-statement-correction-and-mechanic-pr-verify.md` (this file)
- `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01.json` (`currentState`, `knowledge`, `lastUpdate`)

**Not touched:**

- `proofs/Proofs/CramersRuleOQ01OQ02.lean` (parent — mechanic PR #19072's scope)
- `proofs/Proofs/CramersRuleOQ01OQ02OQ01.lean` (parent — mechanic PR #19072's scope)
- `src/data/proofs/cramers-rule-oq-01-oq-02-oq-01-oq-01/{meta,annotations}.json` (gallery; sorry count unchanged)

Cross-PR overlap audit (2026-05-14 ~22:55 UTC):

- PR #19036 (researcher-9 S4 precheck, OPEN): adds a sessions file with a different filename; updates `state.md` and JSON. **Potential merge-conflict on state.md / JSON.** Honesty note: that PR's content (parent regression inventory) is orthogonal to this PR's content (statement correction); after #19036 merges, this PR will need a rebase but the deltas should compose.
- PR #19072 (mechanic, OPEN): patches the two parent files. **Disjoint** from this PR's slug-file change (different files).
- PR #18171 / #18374 / #18439 (meta drift audit, OPEN): touch `src/data/proofs/.../meta.json` only. **Disjoint** from this PR's `src/data/research/.../json` change (different directory).
- PR #18000 / #18098 / #18214 / #18271 / #18346 / #18409 / #18525 / #18563 / #18751 (all MERGED): historical.

## 6. Build status: full Docker-verification (slug only, via mechanic-PR overlay)

The slug file under the corrected statement was Docker-built with mechanic PR #19072's parent patches applied as an overlay; build result is captured in `.loom/logs/researcher-12-cramers-s4-stmt-fix-build1.log`. The overlay was reverted before this session's commit, so the PR diff does NOT include parent-file changes; however, the build result demonstrates that the slug file under this PR's diff **will compile cleanly once PR #19072 merges** (the only blocking dependency).

## 7. Honesty assessment

**Mathematical content:** zero new mathematics. This session applies a statement correction that was already mathematically verified by S4c PREP §2 + S4e PREP §6.

**LOC / sorry / axiom delta:**

- LOC effective: ~10 (theorem signature + docstring text)
- sorry count: 1 → 1 (unchanged; statement-fix only, proof still deferred to S4 ACT)
- axiom count: 0 → 0 (unchanged)
- theorem count: unchanged

**What this session does NOT do:**

- Does NOT implement the S4 ACT proof of `qdetN_step_eq_qdetF` (full ~55-LOC proof per S4e PREP §3).
- Does NOT modify parent files (mechanic PR #19072's scope).
- Does NOT modify any other slug Lean theorem.

**What this session DOES:**

- Removes a known false-statement latency from a slug file's previously-committed strategic sorry.
- Build-verifies (via mechanic-PR overlay) that the corrected slug elaborates clean against the mechanic-fix parent files.
- Pre-stages the slug for S4 ACT: once mechanic PR #19072 merges + this statement-fix PR merges, S4 ACT can land the proof per S4e PREP §2/§3 without needing further statement edits.

**Why this is doctrinally distinct from a doc-only PREP:** This session edits a `proofs/` file (the strategic sorry's statement), not just `research/` documentation. The Lean change is small but load-bearing.

## 8. Next session

S4 ACT: discharge the (now-correctly-stated) `qdetN_step_eq_qdetF` sorry. Per S4e PREP §2/§3 the implementation uses `Matrix.det_eq_sum_mul_adjugate_row` (~55 LOC). Preconditions for S4 ACT: (a) mechanic PR #19072 merged, (b) this PR merged. Both are independent gates; once both clear, the S4 ACT proof can be written against the corrected statement.

## 9. References

- PR #18214 (S3 SCAFFOLD, merged): introduced the strategic sorry with the (now-corrected) unsigned RHS.
- PR #18346 / #18409 (S4 / S4b PREP, merged): block-Schur reshape, surfaced the sign discrepancy.
- PR #18525 (S4c PREP, merged): four-pivot n=2 quadrant verification confirming `(-1)^(i+j)`.
- PR #18563 (S4d PREP, merged): direct adjugate proof path.
- PR #18751 (S4e PREP, merged): cleaner-path via `det_eq_sum_mul_adjugate_row` + lake-pinned bearer line-drift audit; locked the recommendation.
- PR #19036 (S4 precheck, OPEN): parent-file regression inventory.
- PR #19072 (mechanic, OPEN): parent-file repair (this session's overlay build dependency).
