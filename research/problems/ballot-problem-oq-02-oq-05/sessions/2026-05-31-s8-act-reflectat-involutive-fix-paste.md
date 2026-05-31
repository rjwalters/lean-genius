# S8 ACT — Apply R4 false-statement fix (Helper-1 + revised R4 with sub-sorry)

**Researcher**: researcher-1
**Date**: 2026-05-31
**Phase**: ACT (Lean change; build deferred under G9 lake self-loop qualifier)
**Predecessor**: S7 PREP (researcher-1, 2026-05-30) — counterexample documented; paste-ready fix queued
**Successor**: S9 — discharge `hτ` sub-sorry (~15 LOC), then R5 / LOW / R6 chain

## Executive summary

Applied the paste-ready patch from S7 PREP §3 verbatim:

1. **Inserted Helper-1** (`reflectAt_eq_below_firstHit`, ~10 LOC including docstring) before R4: a pure `if_neg` collapse showing that below the first hit time, reflection is the identity.

2. **Changed R4 signature** from `(ω : Fin n → Bool) (a : ℤ)` to `{ω : Fin n → Bool} {a : ℤ} (h : (hitSet ω a).Nonempty)`. Implicit `ω`/`a` + explicit `h` matches the R5 convention immediately below R4 and supplies the Nonempty branch that the counterexample showed is required for the lemma to be true at all.

3. **Replaced R4 proof body** with the §3 skeleton:
   - `have hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a := by sorry` (named sub-sorry; ~15 LOC discharge planned for S9)
   - `funext i; unfold reflectAt; rw [hτ]; split_ifs with hi`
   - then-branch: `simp [Bool.not_not]`
   - else-branch: `rfl`

Sorry count stays at 4 (R4-sub `hτ`, R5, LOW, R6 — same headline count as pre-S8), but R4 graduates from **"false-as-stated, unprovable"** to **"true, with one honest sub-sorry on a discharge-known step"**. Net research progress: structural correctness restored without LOC regression beyond the +37 LOC for Helper-1 + docstring + revised R4 body.

## 1. Diff applied

**File**: `proofs/Proofs/BallotProblemOQ02OQ05.lean` (was 229 LOC, now 266 LOC, Δ +37 LOC).

**Insertion**: between the `reflectAt` definition (lines 172-177) and the original R4 (was lines 179-185).

**Helper-1** (10 LOC including docstring):
```lean
/-- **R4-helper.** Below the first hit time, reflection is the identity.

    Used by R4 (`reflectAt_involutive`) to show
    `firstHitFin (reflectAt ω a) a = firstHitFin ω a` on the
    `(hitSet ω a).Nonempty` branch. Pure `if_neg` collapse. -/
lemma reflectAt_eq_below_firstHit
    {ω : Fin n → Bool} {a : ℤ} {i : Fin n}
    (hi : i.val < (firstHitFin ω a).val) :
    reflectAt ω a i = ω i := by
  unfold reflectAt
  exact if_neg (Nat.not_le_of_lt hi)
```

**Revised R4** (27 LOC including docstring + history block):
```lean
lemma reflectAt_involutive {ω : Fin n → Bool} {a : ℤ}
    (h : (hitSet ω a).Nonempty) :
    reflectAt (reflectAt ω a) a = ω := by
  have hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a := by
    sorry  -- R4-sub `hτ`: min'-of-hitSet argument; see S7 PREP §3 (6 bullets)
  funext i
  unfold reflectAt
  rw [hτ]
  split_ifs with hi
  · simp [Bool.not_not]
  · rfl
```

R4's docstring carries the S7 PREP history block (counterexample, root cause, downstream-zero-cost justification) so a future reader doesn't need to chase the session memo.

## 2. Sorry inventory after S8

| Symbol | Status pre-S8 | Status post-S8 | LOC delta |
|--------|---------------|----------------|-----------|
| `reflectAt_eq_below_firstHit` (Helper-1) | not present | sorry-free | +10 |
| `reflectAt_involutive` (R4) | 1 sorry on FALSE statement | 1 sub-sorry on TRUE statement | +27 |
| `partialSumBool_reflectAt_endpoint` (R5) | 1 sorry | 1 sorry | 0 |
| `reaches_iff_hits_or_above` (LOW) | 1 sorry | 1 sorry | 0 |
| `discrete_reflection` (R6) | 1 sorry | 1 sorry | 0 |
| **Total** | **4 sorries** | **4 sorries** | **+37** |

Net sorry count unchanged. Qualitative gain: R4 is now mathematically truthful.

## 3. Build verification status

**Not verified**: G9 lake self-loop active in worktree.

- `ls -la proofs/.lake` → symlink to `/Users/rwalters/GitHub/lean-genius/proofs/.lake`
- `readlink -f proofs/.lake` exits non-zero (self-loop detected by `readlink`'s loop limit)

This is the known main-repo `.lake` self-symlink condition (see project memory:
[lake-self-loop-main-repo](../../../../.claude/memory/project_lake_self_loop_main_repo.md)).
Ship under `(build pending — G9 lake self-loop)` qualifier per the standard
memory pattern; do not fix from inside a research PR.

**Risk-acceptance criteria**:

- ✅ **Leaf-only**: `grep -rn 'import Proofs.BallotProblemOQ02OQ05' proofs/Proofs/` returns nothing — 0 downstream importers; cannot cascade beyond this file.
- ✅ **Recent build-verify**: S6 ACT (#19675, base commit `cff3fd36c83`) was Docker-verified 2026-05-15 with 7744 jobs successful. The S8 ACT delta is +37 LOC, all syntactically standard Lean 4: one `lemma` declaration, one signature change with implicit binders, one proof body using `have/sorry/funext/unfold/rw/split_ifs/simp/rfl`. No new imports, no new defs, no Mathlib API call outside `Nat.not_le_of_lt` (core) and `Bool.not_not` (core).
- ✅ **Bearer 0-drift**: all 10 bearers pinned in S7 PREP §6 verified at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`cat proofs/lake-manifest.json | jq -r '.packages[]|select(.name=="mathlib")|.rev'`).
  Two new bearers used in this ACT:
  - `Nat.not_le_of_lt` — core Lean, no Mathlib pin needed.
  - `Bool.not_not` — core Lean, no Mathlib pin needed.
- ✅ **Sibling-coordination**: `grep -rnE 'reflectAt_involutive|reflectAt_eq_below_firstHit|discrete_reflection' proofs/Proofs/` matches only in this file + parent `BallotProblemOQ02.lean`'s unrelated `reflection_principle` axiom (line 184, continuous BM). No race.

## 4. R5 / R6 audit confirms zero-cost on consumer side

**R5** (`partialSumBool_reflectAt_endpoint`): already takes `(h : (hitSet ω a).Nonempty)` as explicit (current lines 209-213). Unaffected.

**R6** (`discrete_reflection`): the proof sketch via `Finset.card_nbij'` constructs a bijection between `{ω : ending ω < a, (hitSet ω a).Nonempty}` and `{ω : ending ω > a}`. The `(hitSet ω a).Nonempty` predicate is part of the source set's `Finset.filter`, so when R6's body extracts a witness via `Finset.mem_filter.mp`, the hypothesis `h` flows directly into the call to R4. Zero consumer breakage.

**LOW** (`reaches_iff_hits_or_above`): unchanged.

## 5. Tactic justification (R4 proof body)

After `funext i; unfold reflectAt`, the goal is:
```
(if (firstHitFin (reflectAt ω a) a).val ≤ i.val
  then !((reflectAt ω a) i)
  else (reflectAt ω a) i) = ω i
```
where the inner `reflectAt ω a` is itself an `if`-expression on `(firstHitFin ω a).val ≤ i.val`.

After `rw [hτ]`, both `if`-conditions become identical: `(firstHitFin ω a).val ≤ i.val`.

`split_ifs with hi` then introduces:
- `hi : (firstHitFin ω a).val ≤ i.val` ⟹ goal `!(!(ω i)) = ω i`, closed by `simp [Bool.not_not]`.
- `¬hi` ⟹ goal `ω i = ω i`, closed by `rfl`.

The two cases of `split_ifs` align because both `if`s share the same decidable condition after `rw [hτ]`.

## 6. The `hτ` sub-sorry: full S9 discharge plan

The sub-sorry inside R4 is the **first-hit-preservation** claim:
```
hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a
```

**Discharge plan (6 bullets, ~15 LOC)** — preserved from S7 PREP §3 for S9 paste:

1. **Define** `τ := (hitSet ω a).min' h`. Then `firstHitFin ω a = τ` (defn of `firstHitFin` on Nonempty branch).
2. **Show** `τ ∈ hitSet (reflectAt ω a) a`. Proof: `partialSumBool (reflectAt ω a) τ = a`. The sum `∑ i : Fin n, ...` has `if h : i.val < τ.val then ...` guards. For each `i` with `i.val < τ.val`, `reflectAt ω a i = ω i` by Helper-1. So the partial sum equals `partialSumBool ω τ = a` (by `min'_mem h` + `hitSet` defn).
3. **Show** `(hitSet (reflectAt ω a) a).Nonempty`: witness is τ from step 2.
4. **Show** `(hitSet (reflectAt ω a) a).min' _ ≤ τ`: immediate from `Finset.min'_le` + step 2.
5. **Show** `τ ≤ (hitSet (reflectAt ω a) a).min' _`: by `Finset.le_min'`. Suppose `k ∈ hitSet (reflectAt ω a) a` and `k.val < τ.val`. By Helper-1 applied to every `j : Fin n` with `j.val < τ.val` (which includes every `j` with `j.val < k.val`), `partialSumBool (reflectAt ω a) k = partialSumBool ω k = a`. So `k ∈ hitSet ω a`. But then `min'_le` gives `τ = (hitSet ω a).min' h ≤ k`, contradicting `k.val < τ.val`.
6. **Combine** 4 + 5 + antisymmetry on `Fin (n+1)`: `firstHitFin (reflectAt ω a) a = (hitSet (reflectAt ω a) a).min' _ = τ = firstHitFin ω a`.

**Sub-helper** likely needed at S9: `partialSumBool_congr_below` (~5 LOC) — `Finset.sum_congr rfl` applied to the indicator guard `i.val < k.val`. Captures the structural argument used twice (steps 2 and 5).

## 7. Bearer status table (post-S8)

All bearers from S7 PREP §6 remain valid at lake-pinned `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| API | File | Line | Use in this file |
|-----|------|------|------------------|
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean` | 196 | `firstHitFin` |
| `Finset.min'_mem` | `Mathlib/Data/Finset/Max.lean` | 207 | (S9 — hτ step 2) |
| `Finset.min'_le` | `Mathlib/Data/Finset/Max.lean` | 210 | (S9 — hτ step 4) |
| `Finset.le_min'` | `Mathlib/Data/Finset/Max.lean` | 213 | (S9 — hτ step 5) |
| `Nat.not_le_of_lt` | core | — | Helper-1 |
| `Bool.not_not` | core | — | R4 then-branch |

The `Finset.card_nbij`/`card_nbij'`/`card_bij`/`card_bij'` pins remain queued for R6's assembly in a later session.

## 8. Sibling-coordination check (re-verified S8)

`gh pr list --state open --search 'discrete_reflection in:title'` returns 0.
`grep -rnE 'reflectAt_involutive|reflectAt_eq_below_firstHit' proofs/Proofs/` returns matches only in `BallotProblemOQ02OQ05.lean`.

No concurrent ACT; no race risk.

## 9. Risk inventory (S8 → S9)

| ID | Description | Risk | Mitigation |
|----|-------------|------|-----------|
| P1 | R4 body's `simp [Bool.not_not]` may need `decide`-cleanup if `split_ifs` introduces `Decidable.decide` rather than `if`-form | LOW | Fallback to `cases ω i <;> rfl` after `split_ifs` |
| P2 | `rw [hτ]` may need positional disambiguation if `unfold reflectAt` leaves both `firstHitFin (reflectAt ω a) a` AND `firstHitFin ω a` in scope (the outer `firstHitFin` is the one being rewritten) | LOW | Use `conv` block to target outer `firstHitFin` if `rw` complains. The inner `reflectAt` does NOT contain a `firstHitFin (reflectAt ω a) a` after `unfold` so only one rewrite target exists |
| P3 | G9 lake self-loop persists into S9; Helper-2 (the `hτ` discharge) is similarly leaf-only, so the same `(build pending — G9)` qualifier applies | KNOWN | Coordinate with deployer to land main-repo `.lake` symlink fix in a separate PR |
| P4 | The `hτ` sub-sorry plan (§6) requires `partialSumBool_congr_below` as a 5-LOC helper; if not added, the proof grows to ~25 LOC inline | LOW | Pre-stage the helper in S9 PREP |

## 10. Deliverable summary

| Metric | Pre-S8 | Post-S8 | Δ |
|--------|--------|---------|---|
| File LOC | 229 | 266 | +37 |
| Sorries | 4 | 4 | 0 (one moves into a sub-sorry on a TRUE statement) |
| Axioms | 1 (`donsker_fclt`) | 1 (`donsker_fclt`) | 0 |
| Defs | 6 | 6 | 0 |
| Lemmas | 3 | 4 (+`reflectAt_eq_below_firstHit`) | +1 |
| Theorems | 1 (`discrete_reflection`) | 1 (`discrete_reflection`) | 0 |
| R4 status | FALSE as stated | TRUE with one honest sub-sorry on a discharge-known step | structural correctness restored |

Slug LOC budget: 266 LOC — exceeds the 250-LOC informal cap by 16 LOC (6%). Acceptable for the structural-correctness gain; recommend revisiting in S9 to compress R4's docstring history block (~15 LOC of recoverable comment text) once the fix has settled.

## 11. Next action (S9)

**S9 PREP or S9 ACT** (any researcher): discharge the `hτ` sub-sorry inside R4. Two routes:

- **Route A (PREP)**: stage the `partialSumBool_congr_below` helper lemma (~5 LOC) + paste-ready `hτ` discharge skeleton (~15 LOC) per §6. Same `(build pending — G9)` shipping pattern.
- **Route B (ACT)**: discharge `hτ` inline directly without the helper. ~20 LOC if `Finset.sum_congr` calls are inlined. Acceptable but less reusable.

After S9 lands, R4 is fully sorry-free; net file sorry count drops to 3 (R5, LOW, R6). The R5/LOW/R6 chain remains in place and can be attempted in S10+ or via Aristotle.

## 12. Aristotle compatibility note

R4 (after Helper-1 + hτ both discharged) is a `funext + rw + split_ifs + simp` proof — well within `auto`'s strength on Aristotle. Helper-1 is a 2-line `unfold + exact if_neg`. Both are plausible Aristotle candidates **once `hτ` is fully discharged**; the `hτ` sub-sorry itself is more involved (`min'`-based antisymmetry argument) and is borderline for Aristotle without further decomposition into the helper sub-lemma.

If S9 takes Route A and the helper lemma is small enough, the combined Helper-1 + hτ + R4 cluster becomes Aristotle-eligible as a unit.
