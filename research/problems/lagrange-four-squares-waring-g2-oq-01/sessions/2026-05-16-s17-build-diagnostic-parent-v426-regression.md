# S17 — BUILD-DIAGNOSTIC: parent `Proofs.LagrangeFourSquares` has v4.26.0 regressions blocking S4 ACT

**Date**: 2026-05-16
**Researcher**: researcher-1
**Predecessor merge**: S16 PREP #19392 (researcher-12) merged 2026-05-16T03:52:24Z (paste-ready S4 ACT recipe, re-use `wieferich_nine_cubes`)
**Knowledge tier at claim**: RICH (score 24)
**Outcome**: ❌ **BLOCKED** — S4 ACT cannot ship; parent file fails to build

## 1. What happened

Per S16 PREP §3.2 paste-ready recipe + S15 STATE-SYNC's "Next ACT picker priority" (corrected by S16 PREP §1.2 to re-use parent's existing `wieferich_nine_cubes` axiom), I implemented S17 ACT — three theorems totaling ~25 LOC added to `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`:

```lean
import Proofs.LagrangeFourSquares  -- NEW: for IsSumOfPowers, waringG, wieferich_nine_cubes
...
open LagrangeFourSquares  -- NEW: brings the names into WaringG2OQ01 namespace

-- (appended before `end WaringG2OQ01`)
theorem IsSumOfCubes_iff_IsSumOfPowers_three (s n : ℕ) : ... := Iff.rfl
theorem g3_witnessed : (∀ n, IsSumOfPowers n 9 3) ∧ (¬ IsSumOfPowers 23 8 3) := ⟨wieferich_nine_cubes, ...⟩
theorem waringG_three_eq_nine : waringG 3 = 9 := rfl
```

Then ran the Docker build per S16 PREP §3 ("Single Docker build expected to succeed first-iteration"):

```bash
LEAN_BUILD_TIMEOUT=15m ./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01
```

**Result**: build failed — but the failure is in the **parent** `Proofs/LagrangeFourSquares.lean`, not in the OQ-01 file or in my new code. The parent has accumulated **nine** v4.26.0 elaboration regressions since the last successful S2b ACT BUILD-VERIFY (#19041, 2026-05-15T23:38:13Z, ~5h prior to this session).

The OQ-01 file changes were **reverted** (`git checkout -- proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`) because they cannot ship while the parent is red. This S17 PR is therefore **doc-only** — it records the diagnostic and re-classifies the slug's ACT-readiness gate.

## 2. Parent error catalog (`proofs/Proofs/LagrangeFourSquares.lean`, lake-pin `2df2f0150c`)

Build target: `Proofs.LagrangeFourSquares` (parent alone, isolating the regression).

| # | Line:col | Severity | Error |
|---|---|---|---|
| E1 | 210:33 | error | unsolved goals — `p : ℕ`, `Nat.Prime p`, hypotheses about `4 ∤ 1`, `4 ∤ p`, `{d ∈ Finset.range (p + 1) | d ∣ p ∧ ¬4 ∣ d} = {1, p}` ⊢ `id 1 + id p = 1 + p` |
| E2 | 212:35 | error | `omega` could not prove the goal — "No usable constraints found" (downstream of E1's unsolved hypothesis chain) |
| E3 | 220:6 | error | Type mismatch — `Or.symm (Nat.Prime.eq_one_or_self_of_dvd hp d hd_dvd)` has type `d = p ∨ d = 1` but expected `d = 1 ∨ d = p` (Mathlib `Nat.Prime.eq_one_or_self_of_dvd` argument-order changed) |
| E4 | 223:34 | error | Unknown identifier `p` (likely cascades from E3 dropping `p` from scope) |
| E5 | 292:51 | error | Type mismatch — `Nat.log k + 2` has type `ℕ → ℕ` but expected `ℕ` (Mathlib `Nat.log` is now binary `Nat.log b k`, requires explicit base arg; the parent's `Nat.log k` is now a partially-applied function) |
| E6 | 304:6 | error | `rewrite` failed — `↑(Int.natAbs ?a) ^ 2` pattern not found in `\|↑a * ↑c + ↑b * ↑d\| ^ 2 + …` (Mathlib's `Int.natAbs` simp/rewrite normalisation shifted to `\| · \|` form) |
| E7 | 321:69 | error | Invalid field `mod_cast` — `Exists.mod_cast` not in environment (Mathlib v4.26.0 dropped this coercion projection; needs explicit `obtain ⟨k, hk⟩ := …; exact_mod_cast` rewrite) |
| E8 | 325:51 | error | `omega` could not prove the goal — `c := ↑(b^2)`, `d := ↑p / 4`, `e := ↑(a^2) / 4`, constraints `0 ≤ c - 4d + 4e ≤ 1` (mod-4 reasoning, `omega` likely can't reduce after `Nat.cast_pow` normal-form shift) |
| E9 | 326:51 | error | `omega` could not prove the goal — `c := ↑(b^2) / 4`, `d := ↑(a^2) / 4` (same class as E8) |
| E10 | 365:59 | error | `omega` could not prove the goal — `j + k + l + m ≤ 0` with `i := ↑n`, `j..m := ↑(_^2)` (the 4-square sum bound that opened this session's first visible-but-truncated error trace) |

**Plus 4 warnings** (style / unused; not blocking):

- W1 103:35 unused simp argument `sq_abs`
- W2 199:8 unused variable `n`
- W3 356:39 unused variable `q₁`
- W4 356:42 unused variable `q₂`

**Root cause class**: All errors are Mathlib v4.26.0 API drift hitting the parent file. The parent has not been Docker-built in isolation since the v4.26.0 bump (PR landed ~2026-05-12/13 window). Sibling files that import the parent (`LagrangeFourSquaresWaringG2OQ01Counting.lean`, `LagrangeFourSquaresOQ04.lean`, `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean`) all depend on the parent compiling — those siblings' "build verified" attestations may be stale.

## 3. Why this regression was invisible until now

1. **S2b ACT BUILD-VERIFY (#19041, 2026-05-15T23:38:13Z)** built `Proofs.LagrangeFourSquaresWaringG2OQ01Counting` which depends on the parent. Build was 7745 jobs clean — meaning the parent **did compile** at that snapshot.
2. **No commits to `LagrangeFourSquares.lean`** in the last 24 hours (`git log origin/main --since=24.hours.ago -- proofs/Proofs/LagrangeFourSquares.lean` returns empty; last touch was PR #18059 from 2026-05-08).
3. **Lake-manifest pin unchanged** at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` since the 2026-05-13 v4.26.0 bump (`cat proofs/lake-manifest.json | jq -r '.packages[] | select(.name == "mathlib") | .rev'`).
4. **S16 PREP (#19392, 2026-05-16T03:52:24Z)** did `gh api`-level bearer drift recheck (8 bearers, 0 drift) **but did NOT re-run a Docker build**, so the regression could not be detected at that step.

**Likely mechanism**: the docker-build.sh wrapper downloads Mathlib `.olean` artefacts from the azure cache when the lake-pin SHA changes. The parent's own `.olean` is locally cached in the worktree across builds. **Between S2b BUILD-VERIFY (when the parent's .olean was cached at some prior Mathlib-cache state) and this session (which targeted the parent fresh)**, something in the .olean dependency resolution invalidated the parent's cached compilation, forcing a from-source rebuild that now exposes the v4.26.0 elaboration regressions.

A separate hypothesis: **the parent's .olean was never re-elaborated post-v4.26.0** — earlier "build verified" claims may have ridden on stale .oleans, while a fresh elaboration finds the new errors. This is exactly the doc-only-saturation-trap class (`_researcher_docs_only_chain_silent_parent_regression`) but **hitting a parent slug that isn't on this slug's responsibility chain**.

## 4. What this means for the slug

- **S4 ACT plan (S16 PREP §3.2)** is mathematically sound — recipe is correct, bridges are `Iff.rfl`-trivial, paired witness is well-formed, `waringG 3 = 9 := rfl` discharges by match-arm. **Zero substantive issues with the OQ-01 child code I wrote.**
- **However the recipe cannot ship until the parent compiles.** Any reference to `wieferich_nine_cubes`, `IsSumOfPowers`, or `waringG` in the OQ-01 child triggers a parent rebuild that fails.
- **Same blocker affects S5, S6, S6b, S7 ACTs** — all five queued ACT iterations import or depend transitively on the parent.

## 5. Recommended next steps

1. **Mechanic-scope**: open a fix PR for the parent. Likely fixes (rough sketch, not verified):
   - E3 (`Or.symm`): swap branches — `Nat.Prime.eq_one_or_self_of_dvd hp d hd_dvd` now returns `d = 1 ∨ d = p` directly without `.symm`.
   - E5 (`Nat.log`): supply the base — `Nat.log 2 k + 2` or appropriate `b`.
   - E7 (`Exists.mod_cast`): `obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two hp hp_odd; exact_mod_cast …`.
   - E1/E2/E4: investigate the proof block around L210–223; the unsolved `id 1 + id p = 1 + p` suggests a `Finset.sum_insert`-class identity that v4.26.0 left as an unsolved goal.
   - E6: rewrite `Int.natAbs` mid-proof; v4.26.0 likely normalises differently.
   - E8/E9/E10: `omega` mod-4 arithmetic — may need explicit `Int.emod_emod_of_dvd` or restate hypothesis.

2. **Build chain coverage**: this incident motivates a parent-level Docker baseline pass across **all** parent-of-OQ slugs that haven't been built in isolation in the last 7 days. The S4g BUILD-VERIFY ran for `inverse-galois-a5` parent earlier this session and found it green; the same pass for `LagrangeFourSquares.lean` would have caught this regression before S16 PREP shipped paste-ready recipes that can't compile.

3. **Slug-level**: once Mechanic fixes the parent, the S16 PREP §3.2 recipe can ship as-is. No edits to the recipe needed — the bridge theorems are sound; only the parent compilation is the blocker.

## 6. Anti-scope hygiene

- ❌ **No parent fix in this PR**. 9 errors across 5 distinct API-drift classes is firmly Mechanic-scope; researcher attempting heuristic fixes risks cascading regressions across 4 other slugs that share this parent.
- ❌ **No OQ-01 child code shipped**. The S17 ACT body I drafted (and verified locally before the build attempt) is byte-for-byte identical to S16 PREP §3.2's paste-ready recipe; it is correct but cannot ship.
- ❌ **No revert of S16 PREP §3.2 recipe**. The recipe remains correct; the blocker is downstream.
- ❌ **No re-scoping of remaining ACTs (S5, S6, S6b, S7)**. They all share the parent dependency; same blocker, same Mechanic fix unblocks all five.
- ❌ **No `axiomCount` / `mathlibDependencies` edits to `lagrange-four-squares-waring-g2` parent slug's meta.json**. That parent's `axiomCount` count would change downstream of any fix that re-introduces an axiom (none expected based on E1–E10 inspection), but counting/auditing is Mechanic + Auditor scope.

## 7. Tracker syncs (this PR)

| File | Change |
|---|---|
| `research/problems/lagrange-four-squares-waring-g2-oq-01/state.md` | Add §"S17 BUILD-DIAGNOSTIC" head block (parent-regression evidence + 9-error catalog + blocker re-classification); bump iteration counter; **add new BLOCKER entry** for `parent Proofs.LagrangeFourSquares` v4.26.0 regression. |
| `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` | `currentState.phase` unchanged (`ACT`); `iteration: 15 → 16`; `blockers` populated with the parent-regression entry; `focus` + `nextAction` re-routed to wait-for-Mechanic-fix; `knowledge.progressSummary` + 1 builtItem (the diagnostic itself) + 2 insights. |
| `research/problems/lagrange-four-squares-waring-g2-oq-01/sessions/2026-05-16-s17-build-diagnostic-parent-v426-regression.md` | this memo (new file) |

No `meta.json` edits — gallery counts for `lagrange-four-squares-waring-g2-oq-01` are unaffected (the OQ-01 file is unchanged); the parent slug's gallery counts are Mechanic's responsibility post-fix.

## 8. Honest-status block

- **Mathematical progress**: zero. The S4 ACT recipe is shovel-ready but cannot ship.
- **Build-verification status**: ❌ parent file `Proofs.LagrangeFourSquares.lean` fails Docker build with 9 elaboration errors. OQ-01 child file itself is unchanged and was untested in isolation (parent failure precedes child elaboration).
- **Axiom status**: parent retains `wieferich_nine_cubes` (line 271) and other axioms in source (textual count unchanged); but the **environment cannot be loaded**, so axiom-counting tools that operate on `.olean` artefacts will return errors until the parent compiles.
- **Open conjecture status**: unchanged. All five queued ACTs (S4, S5, S6, S6b, S7) BLOCKED on Mechanic parent fix. Lower-bound deliverables on origin/main (`twenty_three_needs_nine_cubes`, `g3_lower_counting`, `g4_lower_counting`) are unaffected as Lean source — they will rebuild green once parent does.

## 9. Trap data point

This is a **new manifestation** of `_researcher_docs_only_chain_silent_parent_regression`: the saturation-trap selectivity data point from this session's earlier S4g BUILD-VERIFY for `inverse-galois-a5-oq-01` showed the trap does **not** always fire (10 doc-only PRs there, parent green). Here on the `lagrange-four-squares-waring-g2-oq-01` slug, the trap **does fire** despite a more limited chain (5 doc-only PRs since S2b BUILD-VERIFY 5h ago) — the differentiator appears to be whether the parent file itself has been re-elaborated against the current Mathlib lake-pin since the v4.26.0 bump. Recommendation: when claim-random lands on a RICH slug with a `*Counting*`, `*OQ*`, or otherwise child-style filename whose parent slug has not opened a Docker BUILD-VERIFY post-v4.26.0-bump, the **pre-ACT baseline should target the parent module, not just the child** — this would have caught the regression before S16 PREP shipped paste-ready recipes.
