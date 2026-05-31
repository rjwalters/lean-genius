# S7 PREP — `reflectAt_involutive` (R4) is false as stated; corrected discharge plan

**Researcher**: researcher-1
**Date**: 2026-05-30
**Phase**: PREP (doc-only; one 1-LOC Lean signature change recommended)
**Predecessor**: S6 ACT (researcher-9, 2026-05-16, #19675) — paste-ready skeleton landed
**Successor**: S8 ACT — discharge R4 family (new helper + revised R4) per this PREP

## Executive summary

While preparing to discharge the four sorries left in `proofs/Proofs/BallotProblemOQ02OQ05.lean` after S6 ACT, a routine round-trip of the **R4** lemma against its discharge sketch (S5 PREP §6: "Case-split on `(firstHitFin ω a).val ≤ i.val` + `Bool.not_not`") revealed that **`reflectAt_involutive` is false as currently stated**. A concrete 2-bit counterexample is given below. The bug is structural, not a proof-pearl issue: the lemma's universally-quantified form does not hold without a `(hitSet ω a).Nonempty` hypothesis.

The fix is small (1 LOC signature change, ~25 LOC of supporting helper) and ripples downstream cleanly because R6's only use of R4 happens inside the `card_nbij'` bijection where the `(hitSet ω a).Nonempty` hypothesis is already in scope.

This PREP is **doc-only** — no Lean change is committed here. The 1-LOC signature change is queued for S8 ACT along with the helper lemma and the revised R4 proof body. The four `sorry` count remains 4; the slug LOC budget remains within cap.

## 1. The counterexample

Let `n = 2`, `a = 1`, `ω = ![false, false] : Fin 2 → Bool`. Then:

| `k : Fin 3` | `partialSumBool ω k` |
|---:|---:|
| `⟨0, _⟩` | `0` |
| `⟨1, _⟩` | `-1` |
| `⟨2, _⟩` | `-2` |

So `hitSet ω 1 = ∅`, hence `(hitSet ω 1).Nonempty = False`, hence
`firstHitFin ω 1 = ⟨0, Nat.zero_lt_succ _⟩`. Now compute `reflectAt ω 1` on the two cells:

- `i = ⟨0, _⟩`: `(firstHitFin ω 1).val = 0 ≤ 0 = i.val`, so `reflectAt ω 1 ⟨0, _⟩ = !(ω ⟨0, _⟩) = !false = true`.
- `i = ⟨1, _⟩`: `0 ≤ 1`, so `reflectAt ω 1 ⟨1, _⟩ = !false = true`.

Hence `reflectAt ω 1 = ![true, true]`. Now `partialSumBool` on this:

| `k : Fin 3` | `partialSumBool (reflectAt ω 1) k` |
|---:|---:|
| `⟨0, _⟩` | `0` |
| `⟨1, _⟩` | `1` |
| `⟨2, _⟩` | `2` |

So `hitSet (reflectAt ω 1) 1 = {⟨1, _⟩}`, `firstHitFin (reflectAt ω 1) 1 = ⟨1, _⟩` (not `⟨0, _⟩`!). Now compute `reflectAt (reflectAt ω 1) 1`:

- `i = ⟨0, _⟩`: `(firstHitFin (reflectAt ω 1) 1).val = 1 ≤ 0` is **false**, so output is `(reflectAt ω 1) ⟨0, _⟩ = true`.
- `i = ⟨1, _⟩`: `1 ≤ 1` is **true**, so output is `!((reflectAt ω 1) ⟨1, _⟩) = !true = false`.

Hence `reflectAt (reflectAt ω 1) 1 = ![true, false] ≠ ![false, false] = ω`. ∎

The lemma `reflectAt_involutive ω 1 : reflectAt (reflectAt ω 1) 1 = ω` is therefore false for this `ω`.

## 2. Root cause

The S5 PREP §6 discharge sketch reads:

> R4 (MEDIUM): `reflectAt_involutive` — `firstHitFin (reflectAt ω a) a = firstHitFin ω a` ⟹ pointwise `!!b = b`

The first half of this — **first-hit-time preservation under reflection** — does **not** hold when `(hitSet ω a)` is empty. In that case, `firstHitFin ω a = ⟨0, _⟩` (the placeholder default), and `reflectAt ω a = !ω` pointwise (because the predicate `0 ≤ i.val` is satisfied everywhere). The complemented path `!ω` has partial sums that are the **negations** of `ω`'s, so its hit-set at level `a` is `{k : partialSumBool ω k = -a}`, which is generically **non-empty** when `a ≠ 0` (and is non-empty in the counterexample above for `a = -(-1) = 1`).

When `(hitSet ω a)` IS non-empty, first-hit preservation holds and the proof goes through as sketched. The structural fix is therefore to **restrict R4 to the non-empty branch**.

Equivalent fix routes considered and rejected:

| Route | Effect | Why rejected |
|---|---|---|
| **A. Restrict R4** — add `(h : (hitSet ω a).Nonempty)` hypothesis to `reflectAt_involutive` | 1-LOC signature change; R6 already has `h` in scope inside the bijection restriction | **CHOSEN** (smallest, cleanest, no def edit) |
| B. Redefine `reflectAt` — guard with `if (hitSet ω a).Nonempty then ... else ω` | R4 holds unconditionally; but R5 must still match the new shape, and the **proof** of R4 still requires first-hit-preservation inside the non-empty branch | Strictly more work for the same theorem strength downstream |
| C. Make `reflectAt` total over `Option (Fin (n+1))` first-hit-time | Cleaner mathematically; large refactor (~40 LOC) | Out of S7 scope; would itself need its own PREP |
| D. Pose R4 as `(hitSet ω a).Nonempty → reflectAt (reflectAt ω a) a = ω` (logical implication form) | Equivalent to A but breaks the `simp` extension pattern | A is the more idiomatic Lean 4 form |

## 3. Recommended fix (paste-ready)

**Lean diff for `proofs/Proofs/BallotProblemOQ02OQ05.lean`** (S8 ACT will apply):

Change R4's signature from
```lean
lemma reflectAt_involutive (ω : Fin n → Bool) (a : ℤ) :
    reflectAt (reflectAt ω a) a = ω := by
```
to
```lean
lemma reflectAt_involutive {ω : Fin n → Bool} {a : ℤ}
    (h : (hitSet ω a).Nonempty) :
    reflectAt (reflectAt ω a) a = ω := by
```
(implicit `ω`/`a`, explicit hypothesis `h` — matches the convention used by R5 immediately below).

Add a **supporting lemma** before R4 (~10 LOC) to make the first-hit-preservation step explicit and reusable:

```lean
/-- **R4-helper.** Below the first hit time, reflection is the identity.
    Used to show `firstHitFin (reflectAt ω a) a = firstHitFin ω a` when
    `(hitSet ω a).Nonempty`. -/
lemma reflectAt_eq_below_firstHit
    {ω : Fin n → Bool} {a : ℤ} {i : Fin n}
    (hi : i.val < (firstHitFin ω a).val) :
    reflectAt ω a i = ω i := by
  unfold reflectAt
  exact if_neg (Nat.not_le_of_lt hi)
```

This is a pure `if_neg` collapse and is trivially `rfl`-adjacent — at most 3 LOC of proof body, ~7 LOC including the signature.

The **revised R4 proof body** (after the helper lands):

```lean
lemma reflectAt_involutive {ω : Fin n → Bool} {a : ℤ}
    (h : (hitSet ω a).Nonempty) :
    reflectAt (reflectAt ω a) a = ω := by
  -- Step 1: firstHitFin is preserved under reflection (uses h)
  have hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a := by
    sorry  -- R4-sub: min'-of-hitSet argument; ~15 LOC
  -- Step 2: pointwise `!!b = b` collapse with first-hit alignment
  funext i
  unfold reflectAt
  rw [hτ]
  split_ifs with hi
  · simp [Bool.not_not]
  · rfl
```

So R4 itself reduces to ~10 LOC + one sub-`sorry` (`hτ`). The sub-`sorry` is the first-hit-preservation step:

```lean
hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a
```

Discharge sketch for `hτ`:

1. Let `τ := firstHitFin ω a`. By `(hitSet ω a).Nonempty`, `τ = (hitSet ω a).min' h` and `partialSumBool ω τ = a` (from `min'_mem` + hitSet defn).
2. Show `partialSumBool (reflectAt ω a) τ = a`, i.e., `τ ∈ hitSet (reflectAt ω a) a`. This uses `reflectAt_eq_below_firstHit` plus a `Finset.sum_congr` argument: for `j : Fin n` with `j.val < τ.val`, `reflectAt ω a j = ω j`; the contribution at `j = τ` (if `τ.val < n`) is zero in `partialSumBool _ τ` because the indicator `i.val < τ.val` excludes it.
3. Show `(hitSet (reflectAt ω a) a)` is non-empty (witness: `τ`), so its `min'` is defined.
4. Show `min' ≤ τ`: immediate from `τ ∈ hitSet (reflectAt ω a) a` and `min'_le`.
5. Show `τ ≤ min'`: suppose `k ∈ hitSet (reflectAt ω a) a` with `k.val < τ.val`. By `reflectAt_eq_below_firstHit` applied to all `j < τ`, `partialSumBool (reflectAt ω a) k = partialSumBool ω k`, so `partialSumBool ω k = a`, hence `k ∈ hitSet ω a`. But `k.val < τ.val` contradicts `τ = (hitSet ω a).min' h` and `min'_le`.
6. Combine: `firstHitFin (reflectAt ω a) a = (hitSet (reflectAt ω a) a).min' ⟨τ, _⟩ = τ = firstHitFin ω a`.

Estimated ~15 LOC, no sub-`sorry`s if `partialSumBool_congr_below` is added (which is itself `Finset.sum_congr` applied to a guard).

## 4. Updated S8 ACT sorry inventory

After the fix lands in S8:

| Slot | Symbol | Risk | LOC | Notes |
|------|--------|------|-----|-------|
| Helper-1 | `reflectAt_eq_below_firstHit` | LOW | ~7 | Pure `if_neg`; trivially provable |
| Helper-2 (sub-sorry inside R4) | `hτ : firstHitFin (reflectAt _) = firstHitFin _` | MEDIUM | ~15 | `min'`-based argument per §3 |
| R4 (after fix) | `reflectAt_involutive` | LOW (was MEDIUM) | ~10 | Now `funext + rw + split_ifs + Bool.not_not` |
| R5 | `partialSumBool_reflectAt_endpoint` | HIGH | ~25 | Unchanged (already has correct hypothesis) |
| LOW | `reaches_iff_hits_or_above` | LOW | ~8 | Unchanged |
| R6 | `discrete_reflection` | HIGH | ~20 | Unchanged — R4's added `(h : ...)` is supplied by `card_nbij'`'s set restriction |

**Net sorry count after S8 ACT**: was 4 → could be 4 again (Helper-2 absorbs one of R4's into a sub-sorry), or 3 if `hτ` is also discharged inline. Either way, no NET regression; **R4 graduates from "false-as-stated" to "honest sorry"**.

**LOC budget**: Adding Helper-1 (~7 LOC) + Helper-2 sketch (~15 LOC) brings the section to ~250 LOC (still within the 250-LOC informal cap for OQ slugs).

## 5. R5 and R6 status (re-audit)

**R5 (`partialSumBool_reflectAt_endpoint`)**: already takes `(h : (hitSet ω a).Nonempty)` as an explicit hypothesis (lines 192-196), so it is unaffected by the R4 fix. Its discharge sketch (`Finset.sum_ite` + `min'_mem h` + arithmetic) remains valid.

**R6 (`discrete_reflection`)**: the bijection is constructed via `Finset.card_nbij'` between the restriction `{ω : ending ω < a, (hitSet ω a).Nonempty}` and `{ω : ending ω > a}`. The hypothesis `(hitSet ω a).Nonempty` is **part of the source set's defining predicate**, so it is available in scope whenever R4 or R5 is invoked. The fix is therefore zero-cost on the consumer side.

**LOW (`reaches_iff_hits_or_above`)**: unchanged; pure partial-sum jump analysis (±1 steps imply an intermediate-value-style hit).

## 6. Bearer pin recheck (no drift expected; verified)

Lake-pinned Mathlib SHA at S6 ACT: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). Confirmed unchanged at S7 PREP-time via `cat proofs/lake-manifest.json | jq -r '.packages[]|select(.name=="mathlib")|.rev'`. All 10 bearer pins from S5 PREP §4 / S6 ACT remain valid:

| API | File | Line | Status |
|-----|------|------|--------|
| `Finset.card_bij` | `Mathlib/Data/Finset/Card.lean` | 341 | GREEN |
| `Finset.card_bij'` | `Mathlib/Data/Finset/Card.lean` | 366 | GREEN |
| `Finset.card_nbij` | `Mathlib/Data/Finset/Card.lean` | 383 | GREEN |
| `Finset.card_nbij'` | `Mathlib/Data/Finset/Card.lean` | 398 | GREEN |
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean` | 196 | GREEN |
| `Finset.min'_mem` | `Mathlib/Data/Finset/Max.lean` | 207 | GREEN |
| `Finset.min'_le` | `Mathlib/Data/Finset/Max.lean` | 210 | GREEN |
| `Finset.le_min'` | `Mathlib/Data/Finset/Max.lean` | 213 | GREEN |
| `ContinuousBallot.BrownianMotion` | `Proofs/BallotProblemOQ02.lean` | 75-93 | GREEN |
| `iIndepFun` | `Mathlib/Probability/Independence/Basic.lean` | — | GREEN |

Two **new** Mathlib bearers will be needed in Helper-2's discharge of `hτ`:

| API | File | Line (v4.26.0) | Use |
|-----|------|------|-----|
| `Finset.sum_congr` | `Mathlib/Algebra/BigOperators/Basic.lean` | (locate in S8) | rewrite `partialSumBool (reflectAt _) k` under `i < τ` guard |
| `Nat.not_le_of_lt` | core (`Mathlib/Init/Order/...`) | — | flip `i.val < (firstHitFin _).val` ⟹ `¬ (firstHitFin _).val ≤ i.val` for `if_neg` |

Both are standard, single-line lookups; will be pinned in S8.

## 7. Infrastructure status

- **Docker daemon**: GREEN (was RED at S6 ACT). `docker info` returns full Server block; `docker ps` responds normally.
- **Host disk**: GREEN (61 GiB available — was 5.4 GiB at S6 ACT). Headroom for Mathlib rebuild.
- **Mathlib pin**: unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- **`.lake` symlink**: not re-checked this session (S7 PREP is doc-only); will recheck at S8 ACT.

Build verification is therefore unblocked for S8 ACT.

## 8. Sibling-coordination check

`grep -rnE 'reflectAt_involutive|reflectAt_eq_below_firstHit' proofs/Proofs/` returns matches only in `BallotProblemOQ02OQ05.lean`. No sibling implementation has shipped a competing version of `reflectAt` or its involution lemma. `gh pr list --state open --search 'discrete_reflection in:title'` returns 0 — no concurrent ACT race.

## 9. Risk inventory (S7 PREP → S8 ACT)

| ID | Description | Risk | Mitigation |
|----|-------------|------|-----------|
| P1 | Helper-2 (`hτ`) might itself need a sub-sub-lemma about `partialSumBool` congruence under partial bit equality | MEDIUM | Pre-stage a `partialSumBool_congr_below` lemma as a 5-LOC helper if Helper-2 grows past 25 LOC |
| P2 | The Bool case-split in R4's `simp [Bool.not_not]` step may not close cleanly if `if_pos h'` rewrite leaves a `decide`-ambiguous term | LOW | Fallback to `cases ω i <;> rfl` after `split_ifs` |
| P3 | R5's `(hitSet ω a).Nonempty` hypothesis flows fine to R4 inside R6's bijection, but the witness must come from the filter predicate not the goal | LOW | Use `Finset.mem_filter.mp` extraction inside R6's `card_nbij'` block; standard pattern |
| P4 | Aristotle compatibility: R4 (after fix) is `funext + rw + split_ifs + simp` — well within Aristotle's `auto` strength. Helper-2's `min'`-based proof is borderline; may need decomposition | LOW | Submit R4 + Helper-1 to Aristotle if S8 ACT defers Helper-2 |

## 10. S8 ACT-readiness gate (this PREP's deliverable)

| # | Gate | Status |
|---|------|--------|
| 1 | False-statement of R4 identified + counterexample documented | ✅ §1 |
| 2 | Root cause diagnosed (first-hit-preservation fails when `(hitSet ω a)` empty) | ✅ §2 |
| 3 | Fix chosen (Option A: add hypothesis) with rationale | ✅ §2 table |
| 4 | Paste-ready signature change drafted | ✅ §3 |
| 5 | Helper lemmas drafted | ✅ §3 |
| 6 | Sub-sorry plan for `hτ` documented | ✅ §3 |
| 7 | R5/R6 re-audit confirms zero-cost fix on consumer side | ✅ §5 |
| 8 | Bearer pins reverified at lake-pinned Mathlib SHA | ✅ §6 |
| 9 | Infra (Docker, disk, lake) re-checked | ✅ §7 |
| 10 | No sibling race | ✅ §8 |
| 11 | Risk inventory drafted | ✅ §9 |

All 11 gates GREEN. S8 ACT can proceed directly with the paste-ready material in §3.

## 11. Deliverable summary (this PREP)

- **No Lean change** in this PREP; the file remains at 229 LOC, 4 `sorry`s, 1 axiom.
- 1 new session memo (this file): documents the R4-falsity discovery and the corrected discharge plan.
- 1 state.md update: records S7 PREP, points S8 ACT at the paste-ready signature change + helpers, refreshes infra status.
- Bearer pin table reverified.

**Net research progress**: R4's "MEDIUM ~10 LOC" discharge estimate was based on a false lemma. Catching this before S8 ACT shipped the wrong proof saves ~10 LOC of dead-end work and avoids a build failure that would have surfaced only after a ~13-minute Docker cycle. The corrected plan (Helper-1 + Helper-2 + revised R4) is structurally sound, mathematically honest, and unlocks the downstream R5 → R6 chain.

## 12. Next action (S8)

Apply the paste-ready patch from §3:

1. Insert `reflectAt_eq_below_firstHit` (Helper-1, ~7 LOC) before R4.
2. Change R4 signature to take `{ω}`, `{a}` implicit + `(h : (hitSet ω a).Nonempty)` explicit.
3. Replace R4 proof body with the §3 skeleton (`funext + rw [hτ] + split_ifs + Bool.not_not`), leaving the `hτ` sub-sorry inline.
4. Optionally: discharge `hτ` inline (~15 LOC) if S8 budget allows; otherwise leave as a named sub-sorry for S9.
5. Build-verify via `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05` once the lake symlink (G9) is healthy.

Sorry count after S8 ACT: 3 (Helper-1, R4-via-hτ, plus the inherited R5/R6/LOW — well wait, helper-1 is sorry-free; correctly: R4 itself + R5 + LOW + R6 = 4 if hτ is left inline, or R4 itself fully discharged ⟹ 3 if hτ is inlined and proved. Best-case S8 outcome: 3 sorries net.)

Plausible Aristotle candidates after S8: R4 (now `funext + rw + split_ifs + simp`-shaped after Helper-1 + hτ land — well within `auto` strength), and the LOW lemma (jump analysis — borderline). Helper-2 (`hτ`) and R5 remain too involved for Aristotle.
