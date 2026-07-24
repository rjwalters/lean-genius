# Current State

**Phase**: COMPLETE (S12 — final 2 sorries discharged, Docker-GREEN)
**Since**: 2026-07-24 (S12 ACT, researcher-2)
**Iteration**: 12
**Last Updated**: 2026-07-24

## S12 ACT (researcher-2, 2026-07-24) — THREAD COMPLETE: final 2 sorries discharged

The S11 BLOCKED flag was verification-infra-only; Docker is GREEN today, so
both build-gated sorries were discharged (Docker 8577 jobs, exit 0):

1. **`reaches_iff_hits_or_above`** — via new discrete intermediate-value lemma
   `hitSet_nonempty_of_ge` (any partial sum `≥ a > 0` forces an exact hit of
   `a`; induction on the index, a `+1` jump from `< a` cannot overshoot), with
   recurrence `partialSumBool_succ` and base `partialSumBool_zero` (both take
   explicit `Fin.mk` bound proofs so `omega` atoms unify).
2. **R6 `discrete_reflection`** — `|reaches ≥ a| = 2·|ends ≥ a| − |ends = a|`:
   partitions `A = B ⊔ D`, `B = C ⊔ E` (`card_union_of_disjoint`), the
   reflection bijection `|D| = |E|` via `Finset.card_nbij'` with
   `i = j = reflectAt · a` (R4 involution + R5 endpoint formula + new helper
   `firstHit_mem_hitSet_reflectAt`), and a closing `omega`.

**File**: `BallotProblemOQ02OQ05.lean` 545 LOC, **0 sorries** (was 2), 1 axiom
(`donsker_fclt` — the intended Donsker FCLT statement axiom, Wiedijk #45).
Per S11, these two sorries were "the only work left on this slug" — the
discrete-reflection section (André 1887) is now fully machine-checked and the
thread is COMPLETE. The continuous-side derivations (S4-S7 checklist items:
deriving the parent's axioms from `donsker_fclt`) remain out-of-scope DEEP
work, already recorded as such.

**Gotcha recorded**: `rw [if_pos (by omega)]` with unanchored condition can
unify with the wrong `ite` — bind `have c : cond := by omega` first.
Session memo: `sessions/2026-07-24-s12-act-final-sorries-discharged.md`.

---

> STATE-SYNC (2026-06-14, researcher-6): the S11 BLOCKED flag had not
> reached the registry or the pool. The registry
> `src/data/research/problems/ballot-problem-oq-02-oq-05.json` was still
> iteration 10 / phase ACT / status active / empty blockers, its
> `leanFiles[]` read 229 LOC / 4 thm / 6 sorry while the merged source (and
> the registry's own focus prose) is 357 / 6 / 2, and the candidate-pool
> entry was stuck at `in-progress` — so claim-random kept re-serving this
> Docker-gated slug. Brought registry to BLOCKED / iter-11 with blockers
> populated and leanFiles synced (357 / 6 / 2; def 7, axiom 1 unchanged), and
> marked the pool entry blocked. No Lean changes.

## S11 BLOCKED (researcher-1, 2026-06-13)

The OQ-05 statement layer is complete and tracker-synced at iteration 10
(state.md, the research-pool JSON `currentState`, and origin/main's
`proofs/Proofs/BallotProblemOQ02OQ05.lean` all agree: 357 LOC, 1 axiom
`donsker_fclt`, **2 real sorries**). The two remaining sorries are the only
work left on this slug, and both require a Docker `lake build` to discharge
and verify:

1. `reaches_iff_hits_or_above` (LOW, line 334, ~8 LOC) — `Int.le_iff_exists_eq_succ`
   on the ±1 partial-sum jumps (`S_0 = 0`, `S_k ≥ a > 0` forces an exact hit).
2. `discrete_reflection` (R6, line 353, ~20 LOC) — `Finset.card_nbij'` with
   `i = j = reflectAt _ a`, using the now-proved R4 (`reflectAt_involutive`) for
   `left_inv`/`right_inv` and R5 (`partialSumBool_reflectAt_endpoint`) for the
   `(ending<a, hits a) ↔ (ending>a)` membership image, then linear arithmetic
   for `2 * card_ge − card_eq`.

**Why blocked, not PREP**: both sorries already have paste-ready proof
sketches (S5/S10). The blocker is purely infrastructural, not mathematical —
on 2026-06-13 the Docker daemon is down (`docker info` no Server section) and
the Aristotle backend returns `Resource not found` (404) for every submission,
so neither the build nor the proof-search route can close or verify these.
Both sorries are well-scoped Aristotle candidates; submit `prove_file` on
`BallotProblemOQ02OQ05.lean` and Docker-build once the backend / daemon is
back. No Lean / problem.md / knowledge.md edits in this entry.

## S10 ACT (#22924, 2026-06-13, Docker-verified) — STATE-SYNC back-fill

R5 `partialSumBool_reflectAt_endpoint` was discharged in PR #22924
(2026-06-13 05:51, Docker-verified 7744 jobs), dropping the file's declared
sorries 3 → 2. That PR touched **only** `proofs/Proofs/BallotProblemOQ02OQ05.lean`
(1 file, +43/−11), leaving this `state.md` and the research-pool JSON
(`src/data/research/problems/ballot-problem-oq-02-oq-05.json`, frozen at S6/iter 6)
stale. This entry back-fills the record; no Lean / problem.md / knowledge.md edits.

**R5 proof** (per #22924 commit): the reflected lattice path's endpoint equals
`2a − S_n(ω)`. Splits both endpoints into full signed sums (the `i.val < n`
guard is vacuous for `i : Fin n`), shows `R + S_n = 2a` pointwise (terms double
below the first-hit time `τ` and cancel at/above it), and closes via
`S_τ(ω) = a` from `min'_mem`.

**File metrics (post-S10, origin/main)**:

| Metric | Post-S9 | Post-S10 | Δ |
|--------|---------|----------|---|
| LOC | 325 | 357 | +32 |
| Sorries (declared) | 3 (R5 + LOW + R6) | 2 (LOW + R6) | −1 |
| Axioms | 1 (`donsker_fclt`) | 1 (`donsker_fclt`) | 0 |
| Col-0 lemmas/theorems | 6 | 6 | 0 |

**Remaining sorries**: `reaches_iff_hits_or_above` (LOW, line 334) and
`discrete_reflection` (R6, line 353) — both Docker-gated final discharges.

## S9 ACT (researcher-1, 2026-06-01, Docker-verified)

Discharged the R4-sub `hτ` sorry inline (Route B from S8 ACT's Next Action),
plus added the supporting helper `partialSumBool_congr_below` referenced in
Route A. Both ship in one PR since the helper is small (~7 LOC) and the
inline discharge naturally consumes it.

**Patch (42 LOC added, 1 sorry removed)**:

1. **New helper** `partialSumBool_congr_below` (~12 LOC w/ docstring) inserted
   between `reflectAt_eq_below_firstHit` and `reflectAt_involutive`:
   for `k.val ≤ (firstHitFin ω a).val`, `partialSumBool (reflectAt ω a) k
   = partialSumBool ω k`. Proof is `Finset.sum_congr rfl` + per-summand
   `by_cases hi : i.val < k.val`, then `reflectAt_eq_below_firstHit` on the
   `if_pos` branch and `rfl` on the `if_neg` branch.

2. **R4-sub `hτ` discharge** (~28 LOC, replacing 1 sorry + ~6 LOC of comments):
   `firstHitFin (reflectAt ω a) a = firstHitFin ω a` via `le_antisymm`:
   - **≤ direction**: `firstHitFin ω a ∈ hitSet (reflectAt ω a) a` (using
     `partialSumBool_congr_below (le_refl _)`), then `Finset.min'_le`.
   - **≥ direction**: for any `k ∈ hitSet (reflectAt ω a) a`, by contradiction
     assume `k < firstHitFin ω a`; then `partialSumBool_congr_below
     (Nat.le_of_lt hk_val)` gives `partialSumBool ω k = a`, so `k ∈ hitSet ω a`,
     so `firstHitFin ω a ≤ k` by `Finset.min'_le` — contradicting `k <
     firstHitFin ω a`.

**File metrics**:

| Metric | Pre-S9 | Post-S9 | Δ |
|--------|--------|---------|---|
| LOC | 283 | 325 | +42 |
| Sorries | 4 | 3 | −1 |
| Axioms | 1 (`donsker_fclt`) | 1 (`donsker_fclt`) | 0 |
| Defs | 6 | 6 | 0 |
| Lemmas | 4 (Helper-1 + R4 + R5 + LOW) | 5 (+`partialSumBool_congr_below`) | +1 |
| R4 status | TRUE with `hτ` sub-sorry | TRUE, fully discharged | **sorry-free** |

**Sorry inventory (post-S9)**:

| Sorry | Discharge approach | Note |
|-------|-------------------|------|
| ~~R4-sub `hτ`~~ | — | **DISCHARGED in S9 ACT** |
| R5 (`partialSumBool_reflectAt_endpoint`) | `Finset.sum_ite` + `min'_mem h` + arithmetic | unchanged from S6 |
| LOW (`reaches_iff_hits_or_above`) | `Int.le_iff_exists_eq_succ` on ±1 jumps | unchanged from S6 |
| R6 (`discrete_reflection`) | `Finset.card_nbij'` assembly using R4 + R5 | unchanged from S6 |

**Build status**: **VERIFIED via Docker — 7744 jobs successful, single-file
target `Proofs.BallotProblemOQ02OQ05`, 3 declared sorries (R5 line 288, LOW
line 298, R6 line 313), 0 errors**. Bearer pins all unchanged (lake-pinned
Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

**LOC budget**: 325 LOC exceeds the 250-LOC informal cap by 75 LOC (30%).
Comparable to S8's 6% overage; acceptable for the structural-correctness
+ sorry-count improvement (4 → 3). Compression candidates for future
S-cycles: the multi-paragraph history docstring on `reflectAt_involutive`
(~20 LOC) can be condensed once S10+ R5/R6 are also discharged.

**Bearer 0-drift**: lake-pinned Mathlib SHA unchanged since S5 PREP §4. No
new bearers needed (the discharge uses only previously-pinned APIs:
`Finset.min'`, `Finset.min'_mem`, `Finset.min'_le`, `Finset.le_min'`,
`Finset.sum_congr`, `Finset.mem_filter`, all line-verified in
`~/GitHub/mathlib4` at SHA `2df2f0150c`).

**Sibling-coordination**: no new sibling slug references (`grep -rnE
'partialSumBool_congr_below|reflectAt_involutive' proofs/Proofs/` returns
matches only in this file). No race risk.

**Sorry projection** (unchanged from S8): post-S9 = 3 (R5 + LOW + R6).
Each is independently discharge-able via the discharge sketches in S5 PREP
§6 / S6 ACT inventory.

See `sessions/2026-06-01-s9-act-htau-discharge-inline.md` for the
full memo (patch detail, helper proof, two-direction antisymmetry, bearer
table, sorry projection for S10+).

## S8 ACT (researcher-1, 2026-05-31, build pending — G9 lake self-loop)

Applied the paste-ready patch from S7 PREP §3 verbatim:

1. **Inserted Helper-1** `reflectAt_eq_below_firstHit` (10 LOC including docstring) before R4: a pure `if_neg` collapse showing reflection is identity below the first hit time. Sorry-free.

2. **Changed R4 signature** from `(ω : Fin n → Bool) (a : ℤ)` to
   `{ω : Fin n → Bool} {a : ℤ} (h : (hitSet ω a).Nonempty)`. Implicit `ω`/`a` + explicit `h` matches the R5 convention and supplies the Nonempty branch that the S7 counterexample showed is required.

3. **Replaced R4 proof body** with the §3 skeleton:
   ```lean
   have hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a := by
     sorry  -- R4-sub `hτ`: min'-of-hitSet argument; ~15 LOC discharge planned
   funext i
   unfold reflectAt
   rw [hτ]
   split_ifs with hi
   · simp [Bool.not_not]
   · rfl
   ```
   R4 now has 1 named sub-sorry (`hτ`) on a TRUE sub-statement; the surrounding R4 body is sorry-free modulo that sub-sorry.

**File metrics**:

| Metric | Pre-S8 | Post-S8 | Δ |
|--------|--------|---------|---|
| LOC | 229 | 266 | +37 |
| Sorries | 4 | 4 | 0 |
| Axioms | 1 (`donsker_fclt`) | 1 (`donsker_fclt`) | 0 |
| Defs | 6 | 6 | 0 |
| Lemmas | 3 (R4 + R5 + LOW) | 4 (Helper-1 + R4 + R5 + LOW) | +1 |
| R4 status | FALSE as stated | TRUE with one honest sub-sorry | **structural correctness restored** |

**Sorry inventory (post-S8)**:

| Sorry | Discharge approach | Note |
|-------|-------------------|------|
| R4-sub `hτ` | `min'`-of-hitSet antisymmetry on `Fin (n+1)`; uses Helper-1 | NEW (replaces R4's prior 1-sorry on a FALSE lemma) |
| R5 | `Finset.sum_ite` + `min'_mem` + arithmetic | unchanged from S6 |
| LOW | `Int.le_iff_exists_eq_succ` on ±1 jumps | unchanged from S6 |
| R6 | `Finset.card_nbij'` assembly using R4 + R5 | unchanged from S6 |

**Build status**: **VERIFIED via Docker — 7744 jobs successful, single-file target `Proofs.BallotProblemOQ02OQ05`, 4 declared sorries (R4-sub `hτ` + R5 + LOW + R6), 0 errors**. The G9 lake self-loop is empirically inert for Docker builds (confirmed in a parallel S11 INFRA-VERIFY for `prob-method-lovasz-local-oq-01`, same session): Docker `-v` mount on `lean-mathlib-cache:/workspace/proofs/.lake/build` overrides the host's broken `.lake` symlink chain.

**3 bugs caught at first build attempt** (2 preexisting from S6 ACT skeleton which was never actually built, 1 introduced in this S8 ACT). All three fixed:

1. **partialSumBool** had `if h : i.val < k.val` with unused `h` (warning) → `if i.val < k.val` (S6 ACT bug)
2. **reflectAt** depends on noncomputable `firstHitFin` but was itself `def` (compile error) → `noncomputable def reflectAt` (S6 ACT bug)
3. **R4 proof body**: S7 PREP §3 tactic `unfold reflectAt; rw [hτ]` failed because `unfold` rewrites the inner `reflectAt` inside `firstHitFin (reflectAt ω a) a` too (S8 ACT paste error) → use `show` to expose only the outer `reflectAt`'s def via definitional equality, then `rw [hτ]`. Required explicit parens around `!`-expression in inner `show` due to `!` precedence interaction with `=`.

Empirical R4 proof body now ~22 LOC (was estimated ~10 LOC pre-S7); slug file 269 LOC total. The "(build pending — G9 lake self-loop)" qualifier in this PR's initial commit is obsolete; the follow-up fix-and-verify commit corrects to VERIFIED status.

**Bearer 0-drift**: lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since S5 PREP §4. Two new core bearers (`Nat.not_le_of_lt`, `Bool.not_not`) — both Lean core, no Mathlib pin needed.

**Sibling-coordination**: `grep -rnE 'reflectAt_involutive|reflectAt_eq_below_firstHit|discrete_reflection' proofs/Proofs/` returns matches only in this file (Helper-1 / R4 / R6) and parent `BallotProblemOQ02.lean`'s unrelated `reflection_principle` axiom (continuous BM). No sibling implementation; no race risk. `gh pr list` for `discrete_reflection in:title` returns 0.

**LOC budget**: 266 LOC exceeds the 250-LOC informal cap by 16 LOC (6%). Acceptable for the structural-correctness gain; revisit in S9 to compress R4's docstring history block (~15 LOC of recoverable comment text).

See `sessions/2026-05-31-s8-act-reflectat-involutive-fix-paste.md` for the
full memo (diff applied, tactic justification, R5/R6 audit, `hτ` discharge
plan for S9, bearer table, risk inventory, Aristotle compatibility).

## S7 PREP (researcher-1, 2026-05-30, doc-only)

While round-tripping the S5 PREP §6 discharge sketch for R4
(`reflectAt_involutive` — "Case-split on `(firstHitFin ω a).val ≤ i.val` +
`Bool.not_not`") against the file as it stands on `main`, a concrete
2-bit counterexample surfaced that **falsifies the lemma as stated**:

- `n = 2`, `a = 1`, `ω = ![false, false] : Fin 2 → Bool`
- `hitSet ω 1 = ∅` ⟹ `firstHitFin ω 1 = ⟨0, _⟩` (placeholder)
- `reflectAt ω 1 = ![true, true]` (predicate `0 ≤ i.val` flips every bit)
- `hitSet (![true, true]) 1 = {⟨1, _⟩}`, so `firstHitFin (![true, true]) 1 = ⟨1, _⟩`
- `reflectAt (reflectAt ω 1) 1 = ![true, false] ≠ ![false, false] = ω` ✗

The structural bug: when `(hitSet ω a)` is empty, `reflectAt ω a = !ω`
pointwise (placeholder hit-time hits 0). But `!ω` may itself hit `a`
(e.g., when `ω` hits `-a` — symmetric example above with `a = 1`,
`-a = -1` reached by `ω` at index 1). Then `firstHitFin (!ω) a` is no
longer the placeholder, and the second reflection flips a different set
of bits, breaking involution.

**Fix (Option A, smallest)**: add `(h : (hitSet ω a).Nonempty)` as an
explicit hypothesis to `reflectAt_involutive`. R5 already takes the same
hypothesis; R6's use of R4 sits inside a `Finset.card_nbij'` bijection
whose source-set restriction includes `(hitSet ω a).Nonempty`, so the
hypothesis flows for free on the consumer side. Zero-cost downstream.

**S7 PREP deliverable (paste-ready for S8 ACT)**:

- **Helper-1** (~7 LOC): `reflectAt_eq_below_firstHit` —
  for `i.val < (firstHitFin ω a).val`, `reflectAt ω a i = ω i`. Pure
  `if_neg` collapse, trivially provable.
- **R4 signature change** (1 LOC): `(ω : Fin n → Bool) (a : ℤ)` →
  `{ω : Fin n → Bool} {a : ℤ} (h : (hitSet ω a).Nonempty)`.
- **R4 proof body** (~10 LOC): `funext + rw [hτ] + split_ifs + simp [Bool.not_not]`
  with `hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a` as a
  named sub-`sorry` or inline discharge (~15 LOC via the `min'`-based
  argument: τ is in both hit-sets by Helper-1; both sides are `min'`).

**Updated R4 family LOC budget**: was ~10 LOC (single `sorry`). Now
~30 LOC = 7 (Helper-1) + 10 (R4 body) + 15 (Helper-2 `hτ`, optionally
inline). Slug remains within the 250-LOC informal cap (229 + 30 ≈ 259;
acceptable for the structural-correctness gain).

**Sorry projection after S8 ACT**:

| State | R4 family | R5 | LOW | R6 | Total |
|-------|-----------|----|----|----|------|
| Pre-S7 (current) | 1 (`reflectAt_involutive`, FALSE) | 1 | 1 | 1 | 4 |
| Post-S8 best case | 0 (R4 + helpers all discharged) | 1 | 1 | 1 | 3 |
| Post-S8 worst case | 1 (`hτ` left as sub-sorry) | 1 | 1 | 1 | 4 |

**No net regression**; R4 graduates from "false-as-stated, unprovable"
to "honest sorry" (worst case) or "fully discharged" (best case).

**Bearer pin recheck at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**:
all 10 S5/S6 pins remain GREEN. Two **new** S8-needed bearers identified:
`Finset.sum_congr` (for `partialSumBool`-congruence rewrites in `hτ`)
and `Nat.not_le_of_lt` (for `if_neg` flip in Helper-1). Both standard;
will be line-pinned at S8 ACT.

**Infra recovered since S6** (T+14d):

- Docker daemon: hung → GREEN (29.4.1 server responsive)
- Host disk: 5.4 Gi avail → 61 Gi avail (GREEN, +55.6 Gi)
- Mathlib pin: unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Build verification is therefore unblocked for S8 ACT.

**No Lean change in this PREP**. File remains at 229 LOC, 4 `sorry`s,
1 axiom. This is a structural-design correction that catches a wrong
lemma BEFORE S8 ACT pastes a ~10-LOC proof that would fail to type-check
(or worse, leave a permanent sorry on a false statement).

See `sessions/2026-05-30-s7-prep-reflectat-involutive-counterexample.md`
for the full memo (counterexample arithmetic, root-cause analysis, fix
route comparison, paste-ready patch, helper sketches, sub-sorry
discharge plan for `hτ`, R5/R6 re-audit, bearer pin recheck, infra
status, sibling-coordination, risk inventory, S8 ACT-readiness gate).

## S6 ACT (researcher-9, 2026-05-16, build pending)

Pasted S5 PREP §5 ~99-LOC skeleton verbatim into
`proofs/Proofs/BallotProblemOQ02OQ05.lean` BEFORE `end BallotOQ05`
(line 130 → file now 229 LOC), so the new `section DiscreteReflection`
sits inside the existing `BallotOQ05` namespace. (S5 PREP's "after line 130"
instruction was corrected to "before line 130" so the new section is
inside the namespace rather than requiring a re-open.)

**Build status**: NOT pre-verified — Docker daemon hung at 2026-05-16T15:26Z
(`timeout 8 docker info` returns no Server section; CLI v29.4.1 responds
normally; host disk 100% / 5.4Gi avail, **slightly worse than S5 PREP-time
6.9Gi**). Ships under `(build pending — Docker daemon hung)` qualifier
per memory feedback pattern. Risk-acceptance criteria all met:

- ✅ **Leaf-only**: `grep -rn 'import Proofs.BallotProblemOQ02OQ05' proofs/Proofs/` returns nothing — 0 downstream importers; 4-sorry add cannot cascade beyond this file.
- ✅ **Recent build-verify**: file at base commit `cff3fd36c83` (#19282 S2 ACT) was Docker-verified 2026-05-15 with 7744 jobs successful.
- ✅ **Bearer 0-drift**: lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since S5 PREP §4 recheck — all 10 bearer pins still GREEN (`card_bij`/`card_bij'`/`card_nbij`/`card_nbij'` at `Mathlib/Data/Finset/Card.lean:341,366,383,398`; `min'`/`min'_mem`/`min'_le`/`le_min'` at `Mathlib/Data/Finset/Max.lean:196,207,210,213`; `BrownianMotion`/`iIndepFun` unchanged since S2).
- ✅ **Sibling-coordination**: `grep -rnE 'discrete_reflection|partialSumBool|reflectAt' proofs/Proofs/Ballot*` → matches only in this file + parent `BallotProblemOQ02.lean` `reflection_principle` axiom (continuous BM, unrelated). No race.

**Delivery summary**:

| Metric | Pre-S6 | Post-S6 | Δ |
|--------|--------|---------|---|
| LOC | 130 | 229 | +99 |
| Sorries | 0 | 4 | +4 |
| Axioms | 1 (`donsker_fclt`) | 1 (`donsker_fclt`) | 0 |
| Defs | 3 (`partialSum`/`interpolatedRescaled`/`WeakConvergesInC01`) | 6 (+`partialSumBool`/`hitSet`/`reflectAt`) | +3 |
| Noncomputable defs | 0 | 1 (`firstHitFin`) | +1 |
| Theorems | 0 | 1 (`discrete_reflection`) | +1 |
| Lemmas | 0 | 3 (`reflectAt_involutive`/`partialSumBool_reflectAt_endpoint`/`reaches_iff_hits_or_above`) | +3 |

**Sorry inventory (post-S6)**:

| Sorry | Risk | LOC est | Discharge approach (from S5 PREP §6) |
|-------|------|---------|-----|
| `reflectAt_involutive` | R4 MEDIUM | ~10 | Case-split on `(firstHitFin ω a).val ≤ i.val` + `Bool.not_not` |
| `partialSumBool_reflectAt_endpoint` | R5 HIGH | ~25 | `Finset.sum_ite` + `min'_mem h` + arithmetic |
| `reaches_iff_hits_or_above` | LOW | ~8 | `Int.le_iff_exists_eq_succ` on partial-sum ±1 jumps |
| `discrete_reflection` | R6 HIGH | ~20 | `Finset.card_nbij'` applied to (ending<a, hits a) ↔ (ending>a) |

All 4 are theorem/lemma sorries (not def sorries) — eligible for
further decomposition or Aristotle submission per `research/SORRY-CLASSIFICATION.md`.
Plausible Aristotle candidates: R5 (sum-splitting + arithmetic — well within `auto` strength after right hint) and final `discrete_reflection` (assembly given the supporting lemmas).

**Insertion correction note**: S5 PREP §5/§11 say "after line 130 (`end BallotOQ05`)" — taken literally that would place the new section OUTSIDE the namespace and the unprefixed identifiers (`partialSumBool`, `hitSet`, etc.) referenced in subsequent S7-S9 ACTs would mis-resolve. Corrected to "before line 130 (the `end BallotOQ05` line, so new section sits inside)". This is a one-line interpretation fix, not a design change.

See `sessions/2026-05-16-s6-act-discrete-reflection-skeleton-build-pending.md`
for the full memo (paste application, build deferral rationale, sorry
discharge roadmap, next action for S7).

## S5 PREP (researcher-6, 2026-05-16, doc-only)

The S4-published "Next Action" `discrete_reflection` sketch (lines 86-95
below — retained for traceability) was never round-tripped against the
file as it stands on `main` (`cff3fd36c83`) or Mathlib v4.26.0 at the
lake-pinned SHA. This S5 PREP closes that gap: 4 issues surfaced with
the bare sketch, 3 design choices documented with a recommendation, all
load-bearing Mathlib bearers re-pinned, and a paste-ready ~90-LOC
skeleton w/ 3 acknowledged `sorry`s on R4/R5/R6 sub-proofs queued for
the eventual S6 ACT.

**Sketch issues fixed in S5 paste-ready skeleton** (full discussion in
`sessions/2026-05-16-s5-prep-discrete-reflection-paste-ready-skeleton.md` § 2):

| Issue | Fix |
|-------|-----|
| `∃ k ≤ n` not decidable for `Finset.filter` | Reshape to `∃ k : Fin (n+1), ...` (§3.1) |
| `partialSumBool` undefined + `ℕ` index awkward | `(Fin n → Bool) → Fin (n+1) → ℤ` w/ bounded `∑ i : Fin n` indicator (§3.1 Option C) |
| No `τ_a` first-hit-time infrastructure | `Finset.min'` on `hitSet ω a` (§3.2 Option β) + `reflectAt` (§5) |
| ℕ-subtraction well-definedness `2 * card_ge - card_eq` | `Finset.card_le_card` + `filter_subset_filter` side lemma (§2.4) |

**Design choice rec** (§3): Option **C** (`Fin (n+1)` index) + Option **β**
(`Finset.min'`) + Option **iv** (`Finset.card_nbij'` — non-dependent
inverse-pair; **NEW pin not in S4 inventory**).

**Bearer pin recheck at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (S5 PREP § 4):

| API | File | Line | Diff vs S4 |
|-----|------|------|------------|
| `Finset.card_bij` | `Mathlib/Data/Finset/Card.lean:341` | 341 | unchanged |
| `Finset.card_bij'` | `Mathlib/Data/Finset/Card.lean:366` | 366 | unchanged |
| `Finset.card_nbij` | `Mathlib/Data/Finset/Card.lean:383` | 383 | **NEW pin (not in S4)** |
| `Finset.card_nbij'` | `Mathlib/Data/Finset/Card.lean:398` | 398 | **NEW pin (not in S4) — recommended for `reflectAt = reflectAt⁻¹`** |
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean:196` | 196 | **NEW pin (not in S4)** |
| `Finset.min'_mem` | `Mathlib/Data/Finset/Max.lean:207` | 207 | **NEW pin (not in S4)** |
| `Finset.min'_le` | `Mathlib/Data/Finset/Max.lean:210` | 210 | **NEW pin (not in S4)** |
| `Finset.le_min'` | `Mathlib/Data/Finset/Max.lean:213` | 213 | **NEW pin (not in S4)** |

**Risk inventory (R1-R8, full table in S5 PREP § 6)**:

- R1 (LOW): `partialSumBool` def
- R2 (LOW): Decidability of `∃ k : Fin (n+1), P k`
- R3 (LOW): `firstHitFin` totality on non-hitting paths
- R4 (MEDIUM): `reflectAt_involutive`
- R5 (HIGH): `partialSumBool_reflectAt_endpoint`
- R6 (HIGH): `discrete_reflection` `card_nbij'` assembly
- R7 (LOW): ℕ-subtraction well-definedness
- R8 (INFRA): Docker daemon hung — ship `(build pending — Docker daemon hung)` per memory pattern

**S6 ACT-readiness gate (8 items, 7 GREEN / 1 RED-INFRA-only)**:

1. ✅ `BallotProblemOQ02OQ05.lean` on `main` (`cff3fd36c83`)
2. ✅ `partialSumBool` design fixed to `Fin (n+1) → ℤ` (S5 § 3.1)
3. ✅ `Finset.card_nbij'` pinned at line 398 (S5 § 3.3)
4. ✅ `Finset.min'`/`min'_mem`/`min'_le`/`le_min'` pinned at lines 196/207/210/213
5. ✅ No active sibling-slug `discrete_reflection` ACT (`gh pr list` → 0; `grep -rn` `Ballot*` → 0 outside this file)
6. ✅ PR #19065 disposition not an ACT blocker (still OPEN+CONFLICTING; champion-deferred)
7. ✅ Slug LOC budget (~95 + ~90 = ~185) within 250-LOC cap
8. 🔴 Docker daemon hung; host disk 100% / 6.9Gi avail — ACT requires `(build pending — Docker daemon hung)` qualifier OR infra recovery

**Sorry inventory at end of S6 ACT** (after paste-ready skeleton lands): `0 → 4` sorries, on:

- `reflectAt_involutive` (R4, MEDIUM, ~10 LOC)
- `partialSumBool_reflectAt_endpoint` (R5, HIGH, ~25 LOC)
- `reaches_iff_hits_or_above` (R6-supporting, LOW, ~8 LOC)
- `discrete_reflection` (R6, HIGH, ~20 LOC main assembly)

All 4 are theorem/lemma sorries (not def sorries) — eligible for further
decomposition; R5 and the final `discrete_reflection` are plausible
Aristotle candidates if the post-ACT sub-iter route is needed.

See `sessions/2026-05-16-s5-prep-discrete-reflection-paste-ready-skeleton.md`
for the full memo (sketch round-trip, design audit, bearer recheck,
paste-ready ~90-LOC skeleton with 3 acknowledged `sorry`s, risk
inventory, ACT-readiness gate, host infra snapshot).

## S4 STATE-SYNC (researcher-6, 2026-05-16, doc-only)

Two PRs from the 2026-05-15 drain wave landed:

- **#19282** (researcher-9) — S2 ACT — Donsker FCLT axiomatized statement layer.
  Merged 2026-05-15 at commit `cff3fd36c83`. Creates
  `proofs/Proofs/BallotProblemOQ02OQ05.lean` (130 LOC, 1 named axiom
  `donsker_fclt`, 0 sorries, 3 defs: `partialSum` + `interpolatedRescaled` +
  `WeakConvergesInC01`).
- **#19288** (researcher-12) — S3 PREP — duplicate-S2-ACT race audit recommending
  merge of #19065 over #19282. Merged 2026-05-15 (commit
  `03625856a59`). The audit recommendation was retroactively overridden
  by the deployer (#19282 merged instead of #19065).

**PR #19065** (`research/ballot-problem-oq-02-oq-05-s2-1778770457`,
researcher-12-era) is **still OPEN + CONFLICTING** as of S4. Its
`BallotProblemOQ02OQ05.lean` is functionally equivalent to what is now
on `main` (modulo the `partialSum` named helper, already on `main` via
#19282 anyway). **Recommendation: close PR #19065 without merging**
(deferred to deployer/champion; this S4 STATE-SYNC PR does not close it).

**Bearer drift recheck at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (v4.26.0):
`Finset.card_bij` at `Mathlib/Data/Finset/Card.lean:341` and `Finset.card_bij'`
at line 366 are unchanged since the S1/S2 pin (verified via `gh api
/repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
file SHA `ce82fb5788b6c30ea01c64fb091124e990516497`).

**S3 ACT-readiness gate (6 items, all GREEN)**:

1. ✅ `BallotProblemOQ02OQ05.lean` on `main` (`cff3fd36c83`)
2. ⚠ `partialSumBool : (Fin n → Bool) → ℕ → ℤ` needs `~5 LOC` definition in S3
3. ✅ `Finset.card_bij` / `card_bij'` pinned & line-verified at Mathlib v4.26.0 SHA
4. ✅ No active sibling-slug `discrete_reflection` ACT (`gh pr list --search 'discrete_reflection'` → 0)
5. ✅ PR #19065 disposition is not an ACT blocker (research-side; champion handles close)
6. ✅ Slug LOC budget (~95 + ~100 = ~195) within 250-LOC informal cap

See `sessions/2026-05-16-s4-statesync-postdrain-s2-act-merged.md` for the
full memo (drift inventory, PR-#19065 disposition narrative, bearer pin
table, S3 ACT-readiness gate, conflict-free guarantee).

## Current Focus (post-S4)

Next scheduled work: **S3 ACT** — prove `discrete_reflection` for the
symmetric ±1 random walk via the André-Feller lattice-path bijection,
shaped against `Finset.card_bij` / `Finset.card_bij'` (the inverse-pair
form is a closer fit for the involutive reflection). Target ~100 LOC,
0 sorries, 0 new axioms, 1 new theorem. See `## Next Action` block
below (unchanged from pre-S4) for the full sketch.

## S2 ACT Focus (researcher-9, 2026-05-15, shipped via #19282)

S2 (researcher-9, 2026-05-15): ACT — ship statement layer of OQ-05 pipeline.

Created `proofs/Proofs/BallotProblemOQ02OQ05.lean` (~95 LOC) containing:

- `partialSum xi k ω = ∑ i ∈ Finset.range k, xi i ω` — partial-sums helper.
- `interpolatedRescaled xi n t ω = (S_⌊tn⌋ + frac · ξ_⌊tn⌋) / √n` — the canonical $C([0, 1], \mathbb{R})$-valued process used in Donsker's theorem.
- `WeakConvergesInC01 μ Xn X` — ad hoc weak-convergence predicate against pointwise-continuous test functionals. Strictly weaker than the classical sup-norm formulation but compatible with Mathlib v4.26.0 (no Polish/Borel structure on $C([0, 1])$ required).
- `donsker_fclt` — the named axiom: Donsker's FCLT (Wiedijk #45). Asserts existence of a Brownian motion on the same probability space such that the rescaled walk converges weakly in $C([0, 1])$ to its sample-path process.

**Build**: verified via Docker (7744 jobs successful, file built in 6.8s on cache hit). Statement-only — 0 sorries, 1 new axiom, 0 theorems requiring proof.

## Active Approach

**Unchanged from S1**: "Axiomatize Donsker, derive parent axioms" — three parent axioms collapse into one or two named classical axioms.

The S2 deliverable opens the file at the correct module path so that S3 can prove `discrete_reflection` (the only sorry-free deliverable of substance), S4 can axiomatize the continuous mapping for the sup-functional and derive `reflection_principle`, and so on through S7.

## Blockers

None new. Existing Mathlib gaps tracked in `problem.md` (Mathlib infrastructure map): no Polish structure on $C([0, 1])$, no Prokhorov, no Kolmogorov-Centsov, no continuous mapping theorem, no Donsker. These remain Mathlib upstream contributions.

## Next Action

**S9 ACT shipped** in this PR (researcher-1, 2026-06-01, Docker-verified) —
`partialSumBool_congr_below` helper added; R4-sub `hτ` discharged inline via
`le_antisymm` on `Fin (n+1)` with `Finset.min'_le` / `Finset.le_min'`.
R4 is now fully sorry-free; file count drops 4 → 3 (R5, LOW, R6).

**S10+**: discharge the R5 / LOW / R6 chain.

- R5 (`partialSumBool_reflectAt_endpoint`, HIGH ~25 LOC): `Finset.sum_ite`
  + `min'_mem h` + arithmetic.
- LOW (`reaches_iff_hits_or_above`, ~8 LOC): `Int.le_iff_exists_eq_succ`
  on ±1 jumps.
- R6 (`discrete_reflection`, HIGH ~20 LOC): `Finset.card_nbij'`
  applied to the (ending<a, hits a) ↔ (ending>a) restriction using
  R4 + R5.

Plausible Aristotle candidates after S9 lands:
- R4 (now `funext + rw + split_ifs + simp`-shaped after Helper-1 + hτ land —
  well within `auto` strength).
- LOW (jump analysis — borderline).
- R5 + R6 main assembly (borderline; could attempt if Aristotle's
  `card_bij`/`Finset.sum_ite` patterns mature).

Helper-2 (`hτ`) itself is more involved (`min'`-based antisymmetry) and is
borderline for Aristotle without further decomposition into the
`partialSumBool_congr_below` sub-helper (Route A).

**Build-verify** all S9+ ACTs via `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05`
once the G9 lake self-loop is resolved at the main-repo level.

**Original S8 plan** (now shipped — verbatim) and the **superseded original S7 sketch**
are below for traceability.

**Original S7 (now obsolete)** sketch retained below for traceability:

~~`reflectAt_involutive` (R4 MEDIUM, ~10 LOC) — `unfold reflectAt`,
   `funext i`, `simp only [Function.iterate_one]`, case-split on
   `(firstHitFin ω a).val ≤ i.val`, terminate with `Bool.not_not` /
   `if_pos`/`if_neg`.~~ **FALSE without `(hitSet ω a).Nonempty` hypothesis** — see S7 PREP §1-2.
2. `partialSumBool_reflectAt_endpoint` (R5 HIGH, ~25 LOC) — `unfold
   partialSumBool reflectAt`, split `∑ i : Fin n` via `Finset.sum_ite`
   on `(firstHitFin ω a).val ≤ i.val`, identity on `i < τ`,
   sign-flipped on `i ≥ τ`. Use `(hitSet ω a).min'_mem h` to extract
   `partialSumBool ω (firstHitFin ω a) = a` and arithmetize.
3. `reaches_iff_hits_or_above` (LOW, ~8 LOC) — partial sums of ±1
   increase/decrease by exactly 1 each step, so `S_k ≥ a` with `a > 0`
   and `S_0 = 0` implies `∃ j ≤ k, S_j = a` (IVT for ℤ-valued ±1 paths).
4. `discrete_reflection` (R6 HIGH, ~20 LOC) — assemble: write
   `reaches ≥ a = (ending ≥ a) ⊔ (ending < a ∧ hits a)`; apply
   `Finset.card_nbij'` with `i = j = fun ω _ => reflectAt ω a`, using R4
   for both `left_inv`/`right_inv`, R5 for membership-image
   (`reflectAt` of `ending < a, hits a` lands in `ending > a`), and
   linear arithmetic over ℕ for `2 * card_ge - card_eq` step.

Plausible Aristotle candidates: R5 + final assembly (both well-scoped
once supporting lemmas land).

**Target shape (refined post-S5; preserved verbatim for traceability)**:

**Target shape (refined post-S5)**:

```lean
section DiscreteReflection
variable {n : ℕ}

-- §3.1 Option C: bounded sum over Fin n, indexed by Fin (n+1)
def partialSumBool (ω : Fin n → Bool) (k : Fin (n+1)) : ℤ :=
  ∑ i : Fin n, if h : i.val < k.val then (if ω i then (1 : ℤ) else -1) else 0

-- §3.2 Option β: Finset.min' on hit set
noncomputable def firstHitFin (ω : Fin n → Bool) (a : ℤ) : Fin (n+1) := ...

-- Reflection past τ_a, identity on non-hitting paths
def reflectAt (ω : Fin n → Bool) (a : ℤ) : Fin n → Bool := ...

-- R4, R5, R6-supporting, R6: 4 sorries to discharge
theorem discrete_reflection (hn : 0 < n) (a : ℤ) (ha : 0 < a) :
    (Finset.univ.filter fun ω : Fin n → Bool =>
        ∃ k : Fin (n+1), partialSumBool ω k ≥ a).card
    = 2 * (Finset.univ.filter ...).card - (Finset.univ.filter ...).card := by sorry

end DiscreteReflection
```

**Approach (refined post-S5)**: André-Feller reflection at first-hit-time
`τ_a` (encoded via `Finset.min'` on `hitSet ω a`), assembled via
`Finset.card_nbij'` (§3.3 Option iv — the inverse-pair non-dependent
form, **NEW pin at `Mathlib/Data/Finset/Card.lean:398` not in S4 inventory**)
with `reflectAt = reflectAt⁻¹` (involutive).

**Expected size**: ~90 Lean lines added, 4 sorries (3 acknowledged on
load-bearing sub-proofs + 1 LOW), 0 new axioms, 1 new theorem (plus 3
supporting lemmas + 2 defs + 1 noncomputable def).

**Risk** (§6 of S5 PREP):

- R4 MEDIUM: `reflectAt_involutive` — `Bool.not_not` after case-split on `(firstHitFin ω a).val ≤ i.val`
- R5 HIGH: `partialSumBool_reflectAt_endpoint` — sum-splitting at `τ_a` + `min'_mem`
- R6 HIGH: `discrete_reflection` — `card_nbij'` assembly
- R8 INFRA: Docker daemon hung → ship S6 ACT with `(build pending — Docker daemon hung)` per memory pattern

**Sibling-coordination check (re-verified S5)**: `grep -rnE
'discrete_reflection|partialSumBool|reflectAt' proofs/Proofs/Ballot*`
returns matches **only in this file** (`BallotProblemOQ02OQ05.lean`)
and the parent `BallotProblemOQ02.lean` `reflection_principle` axiom
(line 184, continuous BM — unrelated). No sibling implementation
exists; no race risk.

**Decidability handling**: `∃ k : Fin (n+1), P k` is decidable for
decidable `P` via `Fintype.decidableExistsFintype` (Lean stdlib) — no
`open Classical` needed at the `Finset.filter` call sites.

**ℕ-subtraction well-definedness**: `card_eq ≤ card_ge` (paths-ending-=-a
⊆ paths-ending-≥-a) ⟹ `2 * card_ge - card_eq` is well-defined on `ℕ`.
Discharge via `Finset.card_le_card` + `Finset.filter_subset_filter` (5-LOC
helper lemma).

## Prior Next-Action Sketch

S1 specified the file structure (definitions + axiom) verbatim. S2 implemented it directly with the only adjustments being (a) added `partialSum` as a named helper for clarity, and (b) **strengthened** the `∀ i j, i ≠ j → IndepFun` (pairwise) hypothesis to `iIndepFun xi μ` (mutual, matching `Proofs/FairGamesTheoremOQ02OQ01OQ01.lean:59`'s pattern). Pairwise independence is insufficient for the classical Donsker theorem; the strengthening keeps the axiom mathematically truthful.

## Attempt Counts

- Total attempts: 5 (S1 OBSERVE survey, S2 ACT statement layer, S5 PREP paste-ready skeleton, S7 PREP false-statement discovery + corrected plan, S8 ACT R4 fix paste)
- Current approach attempts: 5 (axiomatize-Donsker decomposition; S6 ACT skeleton; S7 PREP defect catch; S8 ACT defect fix)
- Approaches tried: 1

## Open files

- `problem.md` — formal Lean signature targets, classification, Mathlib gap analysis, S2-S7 decomposition.
- `knowledge.md` — historical timeline, reflection-principle bijection proof, three CMT formulations, Lévy arcsine variants, Sparre Andersen, full bibliography.

## S2 Deliverable

- 1 new Lean file: `proofs/Proofs/BallotProblemOQ02OQ05.lean` (~95 LOC).
- 1 new named axiom (`donsker_fclt`).
- 2 new definitions (`partialSum`, `interpolatedRescaled`).
- 1 new predicate (`WeakConvergesInC01`).
- 0 new theorems requiring proof.
- 0 sorries.
- Build: verified by Docker (7744 jobs successful).

The OQ-05 pipeline now has a load-bearing statement layer. Sessions S3+ can begin proving content against the published types without re-litigating the signature.

## S1 Deliverable Summary

(retained for reference — see git history of state.md for full S1 narrative)

S1 produced OBSERVE survey: `problem.md`, `knowledge.md`, JSON entry, with full S2-S7 decomposition. 0 Lean files modified. The S2 ACT executed S1's plan verbatim with two small adjustments documented above under "Prior Next-Action Sketch".
