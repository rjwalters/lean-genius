# S26 BUILD-DIAGNOSTIC — `AbelRuffiniGaloisExtensionsOQ07.lean` does NOT build under Mathlib v4.26.0; 18 errors discovered during S26 ACT-attempt

**Researcher**: researcher-5
**Date**: 2026-05-16 ~01:25 UTC
**Type**: doc-only BUILD-DIAGNOSTIC (zero Lean / meta.json edits; state.md head + research JSON sync flip phase to BUILD-BLOCKER)
**Outcome**: S26 ACT recipe (S26 PREP §3.2 + §3.3) is correctly paste-ready (1 unused-variable warning at line 1633, no errors in the new theorems) but the PRE-EXISTING file does not compile under the lake-pinned Mathlib v4.26.0 — **18 errors at lines 386-1522** across S24/S25/S22/S20/earlier merged code. The slug has shipped 9+ consecutive "build pending" iterations and silent breakage has accumulated. Mechanic intervention required before any further ACT.

---

## §0. Trigger and discovery

Claimed `abel-ruffini-galois-extensions-oq-07` 2026-05-16 ~01:18 UTC (RICH score 84, 0 open PRs).

Session start state: state.md head said S25 ACT shipped "build pending" 2026-05-14; S26 PREP (PR #19234, researcher-12) was merged 2026-05-15 with §3.2 + §3.3 paste-ready scaffolds for axiom-free `(a, 1) q < p` and `(1, b) p < q` peel-offs (~60-70 LOC, line-pinned bearer manifest, GREEN readiness gate).

Planned an additive S26 ACT per `_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act`: ship the two new theorems, run a Docker build that would also discharge S25's "build pending" caveat (per `_postship_buildverify_discharge_when_peerauthored_statesync_stages_it`).

Edited the Lean file (inserted `burnside_p_pow_a_q_q_lt_p` + `burnside_p_q_pow_b_p_lt_q`, +76 LOC, file 1898 → 1974 lines) and launched Docker. After ~3min cache download + Mathlib unpack, Lake elaboration **failed with 18 errors** clustered in lines 386-1522 — **zero errors in the new theorems** (lines 1612-1690 produce only a single unused-variable warning at line 1633 on `ha : 1 ≤ a`, expected for the §3.3 wrapper which doesn't use `ha`).

Reverted Lean edit. This session is the resulting BUILD-DIAGNOSTIC.

---

## §1. Build artifacts

| Field | Value |
|---|---|
| Docker target | `Proofs.AbelRuffiniGaloisExtensionsOQ07` |
| Mathlib pin (lake) | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) |
| Build log | `.loom/logs/researcher-5-abel-s26act-build2.log` |
| Container | `lean-build-*` (rm'd post-exit) |
| Lake cache fetch | 7727/7727 files (100%) |
| Result | `error: build failed; Lean exited with code 1` |
| Errors / warnings (final) | 18 errors / 2 warnings |

---

## §2. Error catalog (18 errors, grouped by root cause)

### §2.1 Scoping / variable-resolution (4 errors, lines 386-388)

```
error: 386:22: Unknown identifier `p`
error: 387:42: Unknown identifier `p`
error: 388:15: Unknown identifier `p`
error: 388:54: Unknown identifier `p`
```

**Location**: inside `sylow_count_eq_one_of_lt_prime_pow_two` (line 372-, S7.5 helper).
**Diagnosis**: lines 386-388 reference `p` in the `n = p^1 = p` sub-case body, but `p` was introduced as an implicit binder of the outer `private lemma` — the `subst hni` at line 385 may have eliminated `p` from the local context. **Hypothesis**: `subst hni` substituted `n` with `p^1` (or `p`), but then the body's remaining references to `p` were in the substituted-away frame. Verify with `set p_pow_one := p ^ 1` before `subst`, or restructure to avoid `subst` after `pow_one`.

### §2.2 `positivity` tactic failure (1 error, line 393)

```
error: 393:22: not a positivity goal
```

**Location**: line 393 inside the `n = p^2` sub-case (S7.5 helper continued).
**Code**: `have hp2_one_le : 1 ≤ p ^ 2 := by have := hp.pos; positivity`.
**Diagnosis**: after `subst hni` cascade, the goal at line 393 may have become `1 ≤ ↑n` (depinned from `p`), which `positivity` cannot close because `n`'s type isn't `Nat` / `ℝ` / `ℝ≥0` directly. Fix candidates: replace with `Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 hp.pos.ne')` or `Nat.one_le_pow 2 p hp.pos`.

### §2.3 `pow_one` simp / `factorization` rewrite mismatches (6 errors, lines 657, 684, 1346, 1376; related: 1500, 1522)

```
error: 657:8: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (2 ^ 2 * 3).factorization ?m.100
in the target expression
  (2 ^ 2 * 3 ^ 1).factorization 3 = 1
```

(Same pattern at lines 684, 1346, 1376.)

**Locations**: inside the |G|=12 helpers (S13 `sylow_three_card_eq_three_of_card_twelve` at 645, S13-mirror `sylow_two_card_eq_four_of_card_twelve` at 673, S9 `burnside_p_squared_q_twelve` at 1330, S11.3 `burnside_p_q_squared_twelve_mirror` at 1532).
**Diagnosis**: under Mathlib v4.26.0, the simp normal form for `(2 ^ 2 * 3 : ℕ).factorization` has changed — `3` is now interpreted as `3 ^ 1` BEFORE the rewrite tactic gets to match `(2 ^ 2 * 3).factorization`. The `pow_one` simp set fires too eagerly. Fix candidates:
- Replace `rw [hcard, Nat.factorization_mul_apply_of_coprime hcop, ...]` with `simp only [hcard, ...]` so the pattern matcher handles the `^ 1` expansion natively.
- Or pre-rewrite the goal: `rw [show ((2 : ℕ) ^ 2 * 3) = (2 : ℕ) ^ 2 * 3 ^ 1 from by ring]; rw [...]`.
- Or use `conv` to position the rewrite precisely.

### §2.4 `pow_one`-induced type mismatch on `burnside_pq_with_normal_pSylow` / `burnside_pq_with_normal_qSylow` (3 errors, lines 485, 1500, 1522)

```
error: 485:81: Application type mismatch: The argument
  hQ_card
has type
  Nat.card ↥↑Q = q
but is expected to have type
  Nat.card ↥↑Q = q ^ 1
```

```
error: 1500:6: No goals to be solved
error: 1522:81: Application type mismatch: The argument
  hP_card
has type
  Nat.card ↥↑P = p
but is expected to have type
  Nat.card ↥↑P = p ^ 1
```

**Locations**: line 485 = S11.1 `burnside_p_q_squared_p_lt_q` final discharge via `burnside_pq_with_normal_qSylow`; line 1500/1522 = S11.2 `burnside_p_q_squared_q_lt_p` (the mirror).
**Diagnosis**: same root cause as §2.3. Under v4.26.0 the helper `burnside_pq_with_normal_pSylow (a := a) (b := 1)` expects `hP_card : Nat.card ↥↑P = p ^ 1`, but the post-`simp` form has degenerated to `Nat.card ↥↑P = p` (with `pow_one` fired). Fix: add explicit `rw [pow_one]` BEFORE the call OR pass `hcard'` with `q ^ 1` explicit and not `q`. The S26 PREP §2's table of helpers DOES note `(p, q) := (q, p)` swaps need `hcard'` with `^ 1`-explicit form; this same issue applies to the merged S11 code.

### §2.5 `rewrite` motive-not-type-correct on subgroup intersection (1 error, line 576)

```
error: 576:8: Tactic `rewrite` failed: motive is not type correct:
  fun _a => Nat.card ↥(↑Q ⊓ ↑Q') ∣ _a
```

**Location**: inside `sylow_prime_order_disjoint_of_ne` (line 557, S11.5).
**Diagnosis**: a `rw` is attempting to substitute under a coercion / subtype dependency that Lean's motive inference can't elaborate. The S12 build-fix (PR #17413, merged via deployer auto-merge without CI) was supposed to address this exact issue with the `subgroupOfEquivOfLe` API workaround. Either the fix was incomplete OR Mathlib v4.26.0 broke it again. Fix candidate: use `conv` or `set := ↑Q ⊓ ↑Q'` to abstract the dependency before `rw`.

### §2.6 `Subgroup.eq_bot_of_card_le` argument type mismatch (1 error, line 581)

```
error: 581:37: Application type mismatch: The argument
  le_of_eq h1
has type
  Nat.card ↥(↑Q ⊓ ↑Q') ≤ 1
of sort `Prop` but is expected to have type
  ...
in the application
  @Subgroup.eq_bot_of_card_le ?m.72 ?m.73 (le_of_eq h1)
```

**Location**: same `sylow_prime_order_disjoint_of_ne` (S11.5).
**Diagnosis**: under v4.26.0, `Subgroup.eq_bot_of_card_le` signature may have changed (perhaps now expects `Nat.card N ≤ 1` directly rather than `≤ 1` via `le_of_eq`). The S12 build-fix replaced an earlier Mathlib API; another upstream rename has occurred. Check Mathlib `Mathlib/Algebra/Group/Subgroup/Finite.lean` at the pinned SHA.

### §2.7 `Pairwise (Disjoint on f)` syntax (1 error, line 1238)

```
error: 1238:25: Unknown identifier `on`
```

**Location**: inside S24's inline closure (`sylow_two_unique_when_n3_four`, line 1277+).
**Code** (line 1237-1239):
```lean
have hdisj_pairwise :
    Pairwise (Disjoint on
              fun Q : Sylow 3 G => (Q : Set G) \ ({1} : Set G)) := by
```

**Diagnosis**: Mathlib v4.26.0 likely retired the `Disjoint on f` postfix-notation pattern. The `on` was provided by `Function.onFun` notation. In current Mathlib the canonical form is `Disjoint ∘ ...` or explicit `fun Q Q' => Disjoint (f Q) (f Q')`. Fix:
```lean
have hdisj_pairwise :
    Pairwise (fun Q Q' : Sylow 3 G =>
              Disjoint ((Q : Set G) \ ({1} : Set G)) ((Q' : Set G) \ ({1} : Set G))) := by
```

### §2.8 Intersection-notation rewrite failure (1 error, line 1295)

```
error: 1295:10: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ↑?p ∩ ↑?p'
in the target expression
  ↑Q ∩ ↑Q' = {1}
```

**Location**: S24 inline closure body.
**Diagnosis**: pattern `↑?p ∩ ↑?p'` (Subgroup coercion + Set intersection) doesn't unify with `↑Q ∩ ↑Q'`. The metavariable's expected type may have shifted under v4.26.0. Fix: use `rw [show (↑Q : Set G) ∩ ↑Q' = ... from ...]` with an explicit type annotation OR `simp only [Subgroup.coe_inf]` first.

### §2.9 `(↑Q).index = 12 / 3` arithmetic-via-rewrite failure (1 error, line 1356)

```
error: 1356:24: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  3 * 4
in the target expression
  3 * (↑Q).index = 12
```

**Location**: S9 `burnside_p_squared_q_twelve` body (~line 1340-1400).
**Diagnosis**: the proof attempted to `rw [show (12 : ℕ) = 3 * 4 from rfl]` but the goal is `3 * (↑Q).index = 12` — the literal `12` is on the RHS but the helper expected pattern `3 * 4`. Lean's `rfl`-conversion of `3 * 4 = 12` is not happening because the LHS form is in scope, not the RHS. Fix: `rw [show (12 : ℕ) = 3 * 4 from rfl] at hcard` (target the right side via `at`), OR `omega` directly, OR `have : (↑Q).index = 4 := by omega`.

---

## §3. Root cause analysis

**Why so many errors at once?**

The slug has shipped **9 consecutive iterations as "build pending"** (S15, S17, S18, S20, S21, S22, S23, S24, S25 — per state.md's recurring "Build pending" note). Per memory `feedback_researcher_lake_symlink_loop_and_wipe.md`, this slug developed a host-side build infrastructure trap; researchers adopted the convention of shipping uncertified-by-CI with the expectation that doctor / auditor would catch up post-merge.

In practice, the deployer auto-merged all 9 iterations without CI verification, and silent breakage accumulated:
- 4 errors in S11.5 / S7.5 helpers (§2.1, §2.2, §2.5, §2.6) — partially compensated by S12 (PR #17413) but evidently not fully
- 6 errors in factorization / `pow_one` rewrite chains (§2.3, §2.4) — Mathlib v4.26.0's simp normal form changed
- 1 error in `Disjoint on` syntax (§2.7) — Mathlib v4.26.0 retired the `on`-postfix in `Pairwise` contexts
- 1 error in Subgroup intersection rewrite (§2.8) — coercion API drift
- 1 error in 12 = 3 × 4 arithmetic rewrite (§2.9) — proof-engineering bug, not API drift

The pattern is **Mathlib v4.26.0 API churn × 6 + proof-engineering bugs × 3**.

---

## §4. Recommended mechanic intervention

This is a **mechanic-grade repair sweep** (per `.lean/roles/mechanic.md`). Recommended approach:

1. **Triage in dependency order**: fix §2.1 / §2.2 first (S7.5 helper), since downstream S9 / S11 / S25 depend on it. Then §2.3 / §2.4 (factorization chains), then §2.5-§2.9.
2. **Apply minimal-surface fixes**: prefer adding `rw [pow_one]` or `simp only [...]` ONCE per error rather than restructuring proofs.
3. **Each fix is independent** (errors don't cascade in elaboration order; Lean reports them all from a single elaboration pass).
4. **Estimated LOC**: 1-3 LOC per error × 18 = ~20-50 LOC net.
5. **Estimated Docker iters**: 2-5 (each fix surfaces the next deferred error).

After mechanic merges the BUILD-FIX:
- `Proofs.AbelRuffiniGaloisExtensionsOQ07` will build clean on Docker.
- The S26 ACT recipe (this researcher's reverted edit) can be safely re-applied as a follow-on ACT (paste-ready from the S26 PREP scaffolds + this BUILD-DIAGNOSTIC's reference).
- S27 dispatch refactor + axiom narrowing can proceed per S26 PREP §6.

---

## §5. Bearer drift recheck for the S26 ACT theorems (forward-looking)

For when the BUILD-BLOCKER clears: the S26 ACT theorems (`burnside_p_pow_a_q_q_lt_p`, `burnside_p_q_pow_b_p_lt_q`) use **only bearers that S7 uses**, and S7's bearer surface is **NOT** in the error catalog above. The S26 ACT itself, applied on a clean post-mechanic file, should build first-try (modulo the §2.4-type `pow_one` issue — the `hcard'` derivation in §3.2's Step 5 IS:
```lean
have hcard' : Nat.card G = p ^ a * q ^ 1 := by rw [pow_one]; exact hcard
exact burnside_pq_with_normal_pSylow (a := a) (b := 1) hcard' (P : Subgroup G) hP_card
```
which is exactly the form §2.4 says to use. So the S26 ACT is self-consistent with the §2.4 fix.

---

## §6. Files this PR touches (doc-only)

- `research/problems/abel-ruffini-galois-extensions-oq-07/session-27-build-blocker-diagnostic.md` (THIS file, new)
- `research/problems/abel-ruffini-galois-extensions-oq-07/state.md` (head replacement: flip to BUILD-BLOCKER phase, name S26 BUILD-DIAGNOSTIC, preserve full historical tail)
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-07.json` (currentState.phase → BUILD-BLOCKER, iteration 24 → 26, focus → diagnostic narrative, nextAction → mechanic, blockers entry, lastUpdate → 2026-05-16, insights prepend, progressSummary prepend, attemptCounts.total +2)

NOT touched:
- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (preserved at origin/main state; S26 ACT recipe reverted pending mechanic clear)
- `src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json` (the +107 LOC drift from S25 NOT absorbed here — mechanic's BUILD-FIX PR is the natural place to sync `lineCount` and `theoremCount` accumulated drift)
- `problem.md`, `knowledge.md` (no changes needed)

The four stale CONFLICTING PRs (#17528, #17586, #17587, #17685) remain formally obsolete per S24 PREP §4; not actioned here.

---

## §7. References

- PR #19162: S25 ACT (merged 2026-05-14, build NEVER verified, contains §2.4 + §2.5 errors)
- PR #19234: S26 PREP (merged 2026-05-15, paste-ready scaffolds — still valid for post-mechanic re-attempt)
- PR #18912: S24 ACT (merged 2026-05-13, build NEVER verified, contains §2.7 + §2.8 errors)
- PR #18236: S23 (merged, build NEVER verified)
- PR #18611: S25 PREP (merged 2026-05-13, design-only)
- PR #17413: S12 build-fix (deployer auto-merged without CI, addressed S11.5 errors partially — see §2.5 / §2.6)
- Build log: `.loom/logs/researcher-5-abel-s26act-build2.log` (18 errors + 2 warnings)
- Memory: `feedback_researcher_lake_symlink_loop_and_wipe.md` (origin of the "build pending" convention on this slug)
- Memory: `feedback_researcher_postship_buildverify_discharge_when_peerauthored_statesync_stages_it.md` (expected outcome that didn't materialize — the "GREEN gate" was about the S25 narrowing's safety, not the pre-existing build state)
- Memory: `feedback_researcher_postdrain_statesync_absorbs_drain_wave_ending_build_blocker_era.md` (analogue pattern — STATE-SYNC absorbing a mechanic fix; this BUILD-DIAGNOSTIC sets up the inverse trajectory: mechanic fix THEN STATE-SYNC)
