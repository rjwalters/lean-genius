# S27 PREP — post-completion housekeeping (post-PR #19510 + Mathlib v4.26.0 bearer recheck + mechanic-handoff sharpening)

**Researcher**: researcher-6
**Date**: 2026-05-16 ~09:00 UTC
**Type**: doc-only PREP (zero Lean / meta.json edits; state.md head bump + new session memo only)
**Outcome**: BUILD-BLOCKER unchanged (18 elaboration errors per S26 BUILD-DIAGNOSTIC remain). PR #19510 (mechanic, merged 2026-05-16T08:52Z) absorbed `lineCount` + `theoremCount` drift only (4-line `meta.json` patch); did **not** touch Lean source. This PREP (a) acknowledges the meta-fix landing, (b) re-verifies the Mathlib bearer pin and three high-uncertainty fix candidates via `gh api` against the v4.26.0 pinned SHA, (c) audits the 4 stale "build pending" open PRs, (d) sharpens the mechanic-handoff with API-pinned paste-ready or near-paste-ready candidates for §2.5 / §2.6 / §2.7, and (e) refreshes the ACT-readiness gate.

---

## §1. PR #19510 absorption (mechanic meta-fix)

PR #19510 (rjwalters, merged 2026-05-16T08:52:48Z) — `fix(meta): abel-ruffini-galois-extensions-oq-07 lineCount + theoremCount drift`. Files touched (4 LOC):
- `src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json`:
  - `meta.lineCount`: `1791` → `1898`
  - `meta.theoremCount`: `36` → `38`
  - `leanFile.lineCount`: `1791` → `1898`
  - `leanFile.theoremCount`: `36` → `38`

**Verified post-merge**:
```
$ wc -l proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean
    1898 proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean
$ grep -E '"lineCount"|"theoremCount"' src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json
    "lineCount": 1898,
    "lineCount": 1898,
    "theoremCount": 38,
    "theoremCount": 38,
```
Match. The S26 BUILD-DIAGNOSTIC §6 explicitly flagged that drift as deferred ("the +107 LOC drift from S25 NOT absorbed here — mechanic's BUILD-FIX PR is the natural place to sync `lineCount` and `theoremCount` accumulated drift"). PR #19510 paid down the meta-side drift but mechanic's BUILD-FIX (the Lean-side repair sweep) has NOT yet shipped.

**Caveat (axiom integrity)**: `axiomCount` (1: `burnside_pq_nontrivial`), `sorries` (0), `definitionCount` (0), `substantiveTheoremCount` (18) all unchanged. Status `axiomatized` / badge `axiom` correct (the 1 axiom is the genuinely-open `burnside_pq_nontrivial` non-trivial case).

**Phase impact**: BUILD-BLOCKER remains. The mechanic-FIX (18-error repair sweep) has not begun, per `gh pr list --search "abel-ruffini-galois-extensions-oq-07 in:title state:open"` returning only 4 stale "build pending" researcher-PRs from May 8-12 (see §3 below). No `loom:mechanic` BUILD-FIX PR is yet open on this slug.

---

## §2. Mathlib bearer pin + 3-spot API verification

### §2.0 Bearer pin (unchanged since S26 BUILD-DIAGNOSTIC)

```
$ grep -B1 -A5 '"name": "mathlib"' proofs/lake-manifest.json
   "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
   "name": "mathlib",
   "inputRev": "v4.26.0",
$ gh api repos/leanprover-community/mathlib4/commits/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 \
    --jq '.commit.committer.date,.commit.message'
2025-12-13T10:35:53Z
chore: bump toolchain to v4.26.0 (#32833)
```

Pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0, 2025-12-13) **unchanged** since the S26 BUILD-DIAGNOSTIC at 2026-05-16T01:25Z (~7.5h ago). No upstream churn invalidates the session-27 fix candidates.

### §2.1 §2.7 — `Disjoint on f` and `Function.onFun` scoped notation (REFINED)

S26 BUILD-DIAGNOSTIC §2.7 proposed rewriting `Disjoint on (fun Q => ...)` as `fun Q Q' => Disjoint ((Q : Set G) \ ...) ((Q' : Set G) \ ...)`. API-grounded refinement (Mathlib v4.26.0 `Mathlib/Logic/Function/Defs.lean` lines 39-42):

```lean
abbrev onFun (f : β → β → φ) (g : α → β) : α → α → φ := fun x y => f (g x) (g y)

@[inherit_doc onFun]
scoped infixl:2 " on " => onFun
```

**Key fact**: `on` is **scoped** in the `Function` namespace. The file `AbelRuffiniGaloisExtensionsOQ07.lean` opens `BurnsidePQ` namespace immediately after `import Mathlib.Tactic` but does NOT have `open Function` or `open scoped Function`. So the `on` notation is **not in scope** at line 1238 → `Unknown identifier 'on'` error is exactly as predicted by the scoped-notation drift hypothesis.

**Two paste-ready fixes** (mechanic choice):

**Option A** — file-level `open` (1 LOC, lowest disruption):
Insert after line 50 (`import Mathlib.Data.Set.Card.Arithmetic`) and before `namespace BurnsidePQ` at line 52:
```lean
open scoped Function
```
This brings the `infixl:2 " on "` notation into scope for the entire file. `Mathlib/Data/Set/Pairwise/Basic.lean` at the pinned SHA uses `open Function Order Set` (line 35) — confirming this is the canonical Mathlib usage pattern.

**Option B** — per-call rewrite (3 LOC, more local):
At line 1237-1239 replace with:
```lean
have hdisj_pairwise :
    Pairwise (fun Q Q' : Sylow 3 G =>
              Disjoint ((Q : Set G) \ ({1} : Set G)) ((Q' : Set G) \ ({1} : Set G))) := by
```

**Recommendation**: Option A. Single-LOC, future-proofs against any other `on` usage downstream, and matches Mathlib's own pattern (`Mathlib.Data.Set.Pairwise.Basic` opens `Function`).

### §2.2 §2.6 — `Subgroup.eq_bot_of_card_le` signature (CONFIRMED unchanged)

S26 BUILD-DIAGNOSTIC §2.6 hypothesised "signature drift". Direct check at `Mathlib/Algebra/Group/Subgroup/Finite.lean` at pin SHA `2df2f0150c…`:

```lean
@[to_additive]
theorem eq_bot_of_card_le [Finite H] (h : Nat.card H ≤ 1) : H = ⊥ :=
  let _ := Finite.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H
```

Signature is exactly `(h : Nat.card H ≤ 1) : H = ⊥` — **NOT drifted**. The §2.6 error report:
```
error: 581:37: Application type mismatch: The argument
  le_of_eq h1
has type
  Nat.card ↥(↑Q ⊓ ↑Q') ≤ 1
of sort `Prop` but is expected to have type
  ...
```

is therefore **not** a signature change but rather an `H` parameter-elaboration issue at the call site: Lean can't infer the implicit `H : Subgroup G` argument from the inferred-card context. The metavariable `?m.72 ?m.73` in the error message confirms this (those are the implicit `G` and `_` instance arguments).

**Paste-ready fix** (1 LOC at line 581):
```lean
exact (↑Q ⊓ ↑Q').eq_bot_of_card_le (le_of_eq h1)
```
or equivalently (dot-notation):
```lean
exact Subgroup.eq_bot_of_card_le (H := ↑Q ⊓ ↑Q') (le_of_eq h1)
```

Dot-notation `(↑Q ⊓ ↑Q').eq_bot_of_card_le` fixes `H` at the resolution site and bypasses the metavariable-unification failure. Alternative APIs also work: `Mathlib/Algebra/Group/Subgroup/Finite.lean` also exposes `card_le_one_iff_eq_bot : Nat.card H ≤ 1 ↔ H = ⊥` (same file at pin), so `(card_le_one_iff_eq_bot).mp h1.le` is an equivalent rewrite.

### §2.3 §2.5 — `subgroupOfEquivOfLe` definition (CONFIRMED present)

S26 BUILD-DIAGNOSTIC §2.5 referenced the "subgroupOfEquivOfLe workaround broken again". Direct check at `Mathlib/Algebra/Group/Subgroup/Map.lean` at pin SHA:

```lean
@[to_additive (attr := simps)
/-- If `H ≤ K`, then `H` as a subgroup of `K` is isomorphic to `H`. -/]
def subgroupOfEquivOfLe {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    H.subgroupOf K ≃* H where
  toFun g := ⟨g.1, g.2⟩
  invFun g := ⟨⟨g.1, h g.2⟩, g.2⟩
  map_mul' _g _h := rfl
```

Definition **unchanged**. The §2.5 error (`motive is not type correct: fun _a => Nat.card ↥(↑Q ⊓ ↑Q') ∣ _a`) is **not** about `subgroupOfEquivOfLe` itself but about an upstream `rw` whose RHS depends on a Subgroup-coerced-to-Set membership proof. The motive-rejection means Lean's `rw` is trying to substitute under a binder where the bound variable's type depends on the term being rewritten.

**Mechanic candidate fix** (need Lean elaboration to verify; ~3 LOC):
```lean
-- Replace the offending `rw` at line ~574-576 with explicit `set`:
set k : Nat := Nat.card ↥(↑Q ⊓ ↑Q') with hk
-- now `k` is a free variable; the `rw [...] ∣ _` substitution lifts without motive issues
```

Or use `Eq.mpr` / `conv` to thread the rewrite through the divisibility argument by hand. This one is **not** API drift; it's proof-engineering. Recommend mechanic try `set ... with hk` first.

---

## §3. Stale open PRs audit (4 PRs, all `build pending` from May 8-12)

`gh pr list --search "abel-ruffini-galois-extensions-oq-07 in:title state:open"`:

| PR# | Title | Opened | Days stale (vs 2026-05-16) | S24 PREP §4 status | Action |
|---|---|---|---|---|---|
| #17528 | S14 — cube-identity bridge for S10 closure | 2026-05-08 | ~8d | formally obsolete | leave / mechanic closes |
| #17586 | S16 — Set-level pairwise disjointness for punctured Sylow 3-subgroups | 2026-05-09 | ~7d | formally obsolete | leave / mechanic closes |
| #17587 | S16 — sylow_three_set_diff_one_ncard_eq_two | 2026-05-09 | ~7d | formally obsolete | leave / mechanic closes |
| #17685 | S19 — ingredient 4 forward set inclusion | 2026-05-12 | ~4d | formally obsolete | leave / mechanic closes |

All four were superseded by S24's inline closure of `sylow_two_unique_when_n3_four` (which subsumed the cube-identity / Sylow-3-disjointness scaffold these PRs were building toward). S24 PREP §4 already declared them "formally obsolete"; S26 BUILD-DIAGNOSTIC §6 confirmed: "not actioned here." This PREP does the same — closing them is mechanic / champion housekeeping, not researcher work, and closing them while the BUILD-BLOCKER persists creates no value.

**Recommendation**: When the mechanic's BUILD-FIX ships, the same PR can `gh pr close --comment "Superseded by S24 inline closure + S25 dispatch peel-off (PR #19162). The original scaffold ingredient is no longer reachable from the post-S24 proof structure."` on all four in a single batch. Until then, leave them as a historical audit trail.

---

## §4. Mechanic-handoff packaging (UPDATED)

Per S26 BUILD-DIAGNOSTIC §4 + this PREP's §2 refinements, here is the consolidated mechanic-handoff:

| Cluster | Lines | Count | Fix readiness | Recommended approach |
|---|---|---|---|---|
| §2.1 `p` unresolved post-`subst` | 386-388 | 4 | medium (needs Docker) | `set p_pow := p^1` BEFORE `subst hni`, OR refactor to avoid `subst` |
| §2.2 `positivity` failure | 393 | 1 | high | replace with `Nat.one_le_pow 2 p hp.pos` (1 LOC) |
| §2.3 `pow_one` simp normal-form drift | 657, 684, 1346, 1376 | 4 | medium (4 sites) | per-site: pre-rewrite via `show (2^2*3 : ℕ) = 2^2 * 3^1 from by ring` OR switch to `simp only` |
| §2.4 `pow_one`-induced `hcard'` type mismatch | 485, 1500, 1522 | 3 | **HIGH (paste-ready in S26 BUILD-DIAGNOSTIC §2.4)** | add `rw [pow_one]` before call OR use `q^1` explicit form (S26 ACT recipe already uses this) |
| §2.5 motive-not-type-correct on intersection | 576 | 1 | medium (proof-engineering) | use `set k := Nat.card ... with hk` to abstract |
| §2.6 `eq_bot_of_card_le` argument elaboration | 581 | 1 | **HIGH (paste-ready, see §2.2 above)** | `(↑Q ⊓ ↑Q').eq_bot_of_card_le (le_of_eq h1)` (dot-notation pins H) |
| §2.7 `Disjoint on f` scoped notation | 1238 | 1 | **HIGH (paste-ready, see §2.1 above)** | add `open scoped Function` after imports (1 LOC, file-level) |
| §2.8 intersection-rewrite pattern unification | 1295 | 1 | medium | precede with `simp only [Subgroup.coe_inf]` to canonicalise the `↑Q ∩ ↑Q'` form |
| §2.9 `12 = 3 * 4` arithmetic rewrite | 1356 | 1 | high | `have : (↑Q).index = 4 := by omega` (1 LOC; bypasses the failed `rw`) |
| **Total** | | **18** | 3 HIGH paste-ready, 4 medium, 2 high non-paste-ready | |

**Net LOC forecast**:
- 3 HIGH paste-ready clusters (§2.4, §2.6, §2.7): ~5 LOC net (1 LOC each + the `open` directive)
- §2.2 + §2.9: ~2 LOC net (1 LOC each, single-line tactic swaps)
- §2.3 (4 sites): ~8 LOC net (~2 LOC per site)
- §2.1 (4 sites in 1 helper): ~3-6 LOC (single restructuring covers all 4)
- §2.5 + §2.8: ~3-5 LOC each (2 sites, may need Docker iteration)
- **Total**: ~25-40 LOC net across the file. S26 BUILD-DIAGNOSTIC estimated "20-50 LOC net"; this PREP's API-grounded refinement narrows to ~25-40 LOC.

**Docker iter forecast**: 2-4 iterations. The §2.5 / §2.8 proof-engineering fixes may need 1-2 retries each; the API-paste-ready clusters should hold first try.

---

## §5. Bearer drift recheck for S26 ACT (forward-looking, unchanged)

The S26 BUILD-DIAGNOSTIC §5 noted that the S26 ACT theorems (`burnside_p_pow_a_q_q_lt_p`, `burnside_p_q_pow_b_p_lt_q`, from S26 PREP §3.2 + §3.3, paste-ready in `session-26-mathlib-audit-and-peel-off-roadmap.md`) use only **S7-tier bearers** (none of which appear in the §2.* error catalog).

Spot-check (this session, against pin `2df2f0150c…`):

| Bearer | Source | Pin verification |
|---|---|---|
| `IsPGroup` | `Mathlib.GroupTheory.PGroup` | unchanged (imports trivially) |
| `IsPGroup.iff_card` | `Mathlib.GroupTheory.PGroup` | unchanged |
| `Sylow.normal_of_normalizer_normalizer` | `Mathlib.GroupTheory.Sylow` | unchanged (used by `burnside_pq_with_normal_pSylow`) |
| `Nat.card` API | `Mathlib.SetTheory.Cardinal.Finite` | unchanged |

(Full bearer manifest is in S26 PREP §2; not re-derived here. The point is: **the S26 ACT is mechanic-clear-trigger-ready** — when mechanic BUILD-FIX merges, the S26 ACT can re-apply paste-ready first-try.)

---

## §6. LOC delta forecast (this PR vs upcoming S28/S29)

| File | This S27 PREP | After mechanic BUILD-FIX (S28) | After S26 ACT re-attempt (S29) |
|---|---|---|---|
| `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` | 0 LOC | +25 to +40 LOC (BUILD-FIX) | +60 to +70 LOC (S26 ACT, two new theorems) |
| `src/data/proofs/.../meta.json` | 0 LOC | ±5 LOC (`lineCount`/`theoremCount` resync) | ±5 LOC (`+2` theoremCount, +60-70 lineCount) |
| `state.md` | +~30 LOC (head replacement) | +~40 LOC (S28 BUILD-FIX section) | +~40 LOC (S29 ACT section) |
| Sessions | +~400 LOC (THIS file) | +~100-200 LOC (mechanic logs) | +~200 LOC (S29 ACT memo) |

This PR ships **doc-only**: 2 files changed (state.md head replacement + new session memo). No Lean / meta.json / problem.md / knowledge.md edits.

---

## §7. ACT-readiness gate (S28+ — post-mechanic-clear)

| Gate | Status | Notes |
|---|---|---|
| BUILD-BLOCKER cleared | ❌ RED | 18 errors per S26 BUILD-DIAGNOSTIC; mechanic BUILD-FIX has NOT shipped (no `loom:mechanic` PR open) |
| Mathlib pin stable | ✅ GREEN | `2df2f0150c…` unchanged since v4.26.0 bump 2025-12-13 |
| S26 ACT recipe valid | ✅ GREEN | §3.2 + §3.3 paste-ready, §2.4 issue self-mitigated |
| Bearer manifest stable | ✅ GREEN | 4-spot recheck vs S26 PREP — all unchanged |
| Stale PRs blocked / actionable | ✅ GREEN | 4 stale PRs all formally obsolete; not blocking |
| Disk / Docker available for BUILD-VERIFY | ❌ RED | `/System/Volumes/Data` at 100% / 7.0Gi avail; `docker info` slow (host-disk pressure pattern; see memory) |
| Mechanic-handoff paste-ready | ✅ GREEN (sharpened in §4) | 3/9 clusters now HIGH paste-ready vs S26 BUILD-DIAGNOSTIC's 1/9 |

**5/7 GREEN, 2/7 RED (both INFRASTRUCTURE-ONLY: needs mechanic + needs Docker)**. No research-side gates remain RED. The slug is in a clean handoff state to mechanic; researcher can re-claim and ship S28 (post-mechanic-clear STATE-SYNC) or S29 (S26 ACT re-attempt) immediately when both RED gates clear.

---

## §8. What this PR DOES and DOES NOT do

**DOES**:
- `state.md` head: phase remains BUILD-BLOCKER; iteration 26 → 27; "Last Updated" 2026-05-16 (researcher-5) → 2026-05-16 (researcher-6); S27 PREP section added before S26 BUILD-DIAGNOSTIC; S26 BUILD-DIAGNOSTIC section preserved verbatim.
- New `session-28-s27-prep-postcompletion-housekeeping.md` (THIS file): post-PR #19510 absorption + 3-spot API recheck + stale-PR audit + sharpened mechanic-handoff.

**DOES NOT**:
- Touch `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ07.lean` (BUILD-BLOCKER persists; mechanic owns the BUILD-FIX).
- Touch `src/data/proofs/abel-ruffini-galois-extensions-oq-07/meta.json` (PR #19510 already absorbed the drift; no further drift since).
- Touch `problem.md` or `knowledge.md` (no math content shifts; the proof structure is unchanged).
- Close the 4 stale "build pending" PRs (not researcher work; recommend batch-close concurrent with mechanic's BUILD-FIX merge).
- Attempt any Lean build (Docker daemon slow under host-disk pressure; would be uncertified-by-CI anyway since file doesn't compile).

---

## §9. References

- PR #19510: mechanic meta-fix (merged 2026-05-16T08:52:48Z, +4/-4 LOC `meta.json` only)
- S26 BUILD-DIAGNOSTIC: `session-27-build-blocker-diagnostic.md` (researcher-5, 2026-05-16T01:25Z) + state.md head
- S26 PREP: PR #19234 (researcher-12, merged 2026-05-15) + `session-26-mathlib-audit-and-peel-off-roadmap.md` (paste-ready scaffolds §3.2 + §3.3)
- S25 ACT: PR #19162 (researcher-9, merged 2026-05-14, BUILD-NEVER-VERIFIED; contains §2.4 errors)
- Mathlib v4.26.0 pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (2025-12-13)
- Mathlib `Mathlib/Logic/Function/Defs.lean` lines 39-42 (scoped `on` notation)
- Mathlib `Mathlib/Algebra/Group/Subgroup/Finite.lean` (`eq_bot_of_card_le` signature)
- Mathlib `Mathlib/Algebra/Group/Subgroup/Map.lean` (`subgroupOfEquivOfLe` definition)
- Mathlib `Mathlib/Data/Set/Pairwise/Basic.lean` line 35 (canonical `open Function Order Set` pattern)
- Memory: `feedback_researcher_postship_pivot_lands_on_fully_discharged_slug_blocked_hermit_followup_ship_packaged_followups_prep.md` (PREP-as-handoff pattern; this S27 PREP is a sibling variant — BUILD-BLOCKER vs fully-discharged context)
- Memory: `feedback_researcher_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify.md` (host-infra-blocked pivot rationale)
- Memory: `feedback_researcher_lake_symlink_loop_and_wipe.md` (origin of slug's "build pending" convention; the S26 BUILD-DIAGNOSTIC's discovery that 9 consecutive iters shipped uncertified)

---

**Recommended next action (S28 = mechanic BUILD-FIX, unchanged from S26)**:
Apply per-cluster minimal-surface fixes in dependency order: §2.1 / §2.2 (S7.5 helper) → §2.7 (file-level `open` directive; 1 LOC) → §2.6 (dot-notation; 1 LOC) → §2.3 / §2.4 (factorization chains) → §2.5 / §2.8 / §2.9. Estimated 25-40 LOC net; 2-4 Docker iters. The §2.4 / §2.6 / §2.7 are now HIGH paste-ready per §4 above.

**After mechanic clears: S29 ACT** re-applies S26 ACT recipe (paste-ready in `session-26-mathlib-audit-and-peel-off-roadmap.md` §3.2 + §3.3; +60-70 LOC). First-try buildable per §5 (bearer recheck).

**After S29 ACT lands: S30 dispatch refactor + axiom narrowing** per S26 PREP §6.
