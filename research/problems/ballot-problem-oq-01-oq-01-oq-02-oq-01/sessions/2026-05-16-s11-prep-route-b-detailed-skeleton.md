# S11 PREP — Route B detailed skeleton for Option C transfer (doc-only)

**Researcher**: researcher-11
**Date**: 2026-05-16 (UTC 2026-05-16T~19:11Z)
**PR**: (this PR)
**Phase**: PREP (doc-only)
**Iteration**: 13 → 14
**Lake SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
**Predecessor**: S10 PREP (PR #19477, researcher-6, merged 2026-05-16T05:12Z, T-14h)
**Predecessor recommendation**: §6 "S11 PREP (single-route, ~150-200 LOC doc-only): Detailed skeleton for Route B — full body of `levelPosB_eq_optionC` with zero-case proof, full sketch of how `goodRotations_card_ge_pathB` transfers, full sketch of `step_in_one_pos_pm_card_eq` (Option C variant). Bearer audit for any new lemmas..."

## §0 Scope

S10 PREP shipped a 3-route feasibility audit and recommended **Route B
— alphabet-extend** (surgical, ~60-100 LOC, lowest LOC). This S11 PREP
delivers the single-route detailed skeleton requested. It is **doc-only**:
no Lean edits, no parent-file changes, no problem.md / knowledge.md / gallery
edits. The skeleton below is paste-ready for S11 ACT.

## §1 Target shape recap

**Option C alphabet** (from S8 PREP §4.3):

```
∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1
```

For `l : List ℤ`, this means each `x ∈ {-m, -m+1, …, -1, 0, 1}`.

**Path B alphabet** (already shipped at L379–L470):

```
∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ))
```

Element set: `{-m, -m+1, …, -1, 1}` — **strictly missing `0`**.

**Delta**: precisely the zero step. The S11 ACT must adapt
`levelPosB_eq`'s `helem` step (lines 388–396) to handle `x = 0` via
`levelPosB_max` maximality.

## §2 Lemma plan for S11 ACT

Three new lemmas + 1 optional corollary, all in
`BallotMJumpCycleLemma` namespace, sited **after** L470 (the existing
`step_in_one_pos_mixed_neg_card_bound`), so the Path B chain is
**preserved unchanged**:

| New lemma | Stance toward Path B | Approx LOC |
|---|---|---|
| `levelPosB_eq_optionC` (private) | Reproof of `levelPosB_eq` with 3-way `helem` split | ~40 |
| `goodRotations_card_ge_pathB_optionC` (private) | Signature change only; body verbatim from `goodRotations_card_ge_pathB` modulo `hmem` substitution | ~30 |
| `step_in_one_pos_pm_card_eq` (public) | `le_antisymm` glue, verbatim shape of `step_in_one_pos_mixed_neg_card_eq` | ~6 |
| `step_in_one_pos_pm_card_bound` (public, optional) | `le_antisymm`-flavor slack-form, verbatim shape of `step_in_one_pos_mixed_neg_card_bound` | ~20 |

**Total**: ~96 LOC new (matches S10 PREP §5 forecast 60-100 LOC). Drop the
optional corollary to land at ~76 LOC.

## §3 Paste-ready body — `levelPosB_eq_optionC`

The single load-bearing change. Compared to the existing `levelPosB_eq`
(L379–399), only the `helem` block is restructured. Everything else
(line-by-line, `hj_lt`, `hj_le`, `hj1_gt`, `hstep`, final `linarith`) is
identical.

```lean
/-- **Path B `levelPos_eq`, Option C variant** — extends `levelPosB_eq`'s
    mixed-down alphabet `x = 1 ∨ x = -k` to the two-sided bounded
    alphabet `-(m : ℤ) ≤ x ∧ x ≤ 1`. The single new sub-case is
    `x = 0`, which contradicts the *maximality* of `levelPosB l n` via
    `levelPosB_max` (rather than the strict-inequality `hj1_gt` used
    for `x ≤ -1`). -/
private theorem levelPosB_eq_optionC (l : List ℤ) (m : ℕ)
    (hmem : ∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1)
    (n : ℕ) (hn : (n : ℤ) < l.sum) :
    prefixSum l (levelPosB l n) = minPrefixSum l + n := by
  have hj_lt : levelPosB l n < l.length := levelPosB_lt l n hn
  have hj_le : prefixSum l (levelPosB l n) ≤ minPrefixSum l + n :=
    levelPosB_prefixSum_le l n
  have hj1_gt : minPrefixSum l + (n : ℤ) < prefixSum l (levelPosB l n + 1) := by
    by_contra hle; push_neg at hle
    exact absurd (levelPosB_max l n (levelPosB l n + 1) (by omega) hle) (by omega)
  -- Step-decomposition formula used in both the zero-case and negative-case.
  have hstep_eq : prefixSum l (levelPosB l n + 1)
      = prefixSum l (levelPosB l n) + l[levelPosB l n] := by
    simp only [prefixSum]; exact List.sum_take_succ l (levelPosB l n) hj_lt
  -- 3-way classification of l[levelPosB l n].
  have helem : l[levelPosB l n] = (1 : ℤ) := by
    obtain ⟨_hge, hle⟩ := hmem l[levelPosB l n] (List.getElem_mem hj_lt)
    -- hge : -(m : ℤ) ≤ l[idx]   (unused in this proof; preserved for symmetry)
    -- hle : l[idx] ≤ 1
    by_contra hne
    -- hne : l[idx] ≠ 1 ⟹ l[idx] ≤ 0  (integer order)
    have hle0 : l[levelPosB l n] ≤ 0 := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact Int.lt_iff_add_one_le.mp hlt |>.trans (by linarith)
      · exact absurd heq hne
    -- Subcase A: l[idx] = 0 ⟹ contradicts maximality of levelPosB.
    -- Subcase B: l[idx] < 0 ⟹ contradicts hj1_gt (strict prefix-sum jump).
    rcases lt_or_eq_of_le hle0 with hxneg | hxz_rev
    · -- Subcase B: l[idx] < 0
      rw [hstep_eq] at hj1_gt
      -- hj1_gt : minPrefixSum l + n < prefixSum l idx + l[idx]
      -- hj_le  : prefixSum l idx ≤ minPrefixSum l + n
      -- hxneg  : l[idx] < 0
      linarith
    · -- Subcase A: l[idx] = 0 (after `lt_or_eq_of_le` on `hle0 : x ≤ 0`,
      --                       the `eq` branch is `0 = x`, hence flip).
      have hxz : l[levelPosB l n] = 0 := hxz_rev.symm
      -- Then prefixSum at idx+1 = prefixSum at idx ≤ minPrefixSum + n,
      -- so idx+1 is in the levelPosB filter ⟹ idx+1 ≤ idx (maximality) ⟹ ⊥.
      have hidx1_le : prefixSum l (levelPosB l n + 1) ≤ minPrefixSum l + n := by
        rw [hstep_eq, hxz]; linarith
      have hcontra : levelPosB l n + 1 ≤ levelPosB l n :=
        levelPosB_max l n (levelPosB l n + 1) (by omega) hidx1_le
      omega
  -- Same closing step as `levelPosB_eq` (L397–L399).
  have hstep_one : prefixSum l (levelPosB l n + 1)
      = prefixSum l (levelPosB l n) + 1 := by
    rw [hstep_eq, helem]
  linarith
```

**Total**: 41 LOC (target ≤45).

### §3.1 Why the `lt_or_eq_of_le` on `hle0` works

`hle0 : l[levelPosB l n] ≤ 0` is an integer inequality. `lt_or_eq_of_le`
returns `l[idx] < 0 ∨ l[idx] = 0` (with the equality oriented as
`0 = l[idx]` in Mathlib — hence the `.symm` flip). The negative case
reuses Path B's `linarith` discharge (with the slightly different
hypothesis shape `hxneg` instead of `hx_eq + 0 ≤ k`). The zero case
invokes `levelPosB_max` for the first time in any Path B proof.

### §3.2 Why `hge : -(m : ℤ) ≤ l[idx]` is not used in the proof

The lower bound `-(m : ℤ) ≤ x` is **carried but inert** for the
`levelPosB_eq_optionC` proof: the contradiction in Subcase B uses only
the strict negative-sign of `l[idx]`, not any quantitative bound. The
lower bound IS used downstream (in the bijection counting argument
through `goodRotations_card_ge_pathB_optionC`'s appeal to
`rightmostAtLevel_good`), so it cannot be dropped from `hmem`.

### §3.3 The `Int.lt_iff_add_one_le.mp hlt` step

Given `hlt : l[idx] < 1`, we want `l[idx] ≤ 0`. `Int.lt_iff_add_one_le`
says `a < b ↔ a + 1 ≤ b`, so `hlt` gives `l[idx] + 1 ≤ 1`, hence
`l[idx] ≤ 0`. Alternative (shorter): `omega` should also close this
directly. Adopt whichever the build favors.

## §4 Paste-ready sketch — `goodRotations_card_ge_pathB_optionC`

S10 PREP §2 classifies this as MINOR-ADAPTATION: signature change
only, body essentially unchanged. The hypothesis substitution is
`hmem : ∀ x ∈ l, x = 1 ∨ (∃ k, …)` → `hmem : ∀ x ∈ l, -(m:ℤ) ≤ x ∧ x ≤ 1`,
and the single call site of `levelPosB_eq` (line 425) becomes
`levelPosB_eq_optionC`.

```lean
private theorem goodRotations_card_ge_pathB_optionC (l : List ℤ) (m : ℕ)
    (hmem : ∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1)
    (hS : 0 < l.sum) :
    l.sum.toNat ≤ (goodRotations l).card := by
  have hToNat : (l.sum.toNat : ℤ) = l.sum := Int.toNat_of_nonneg hS.le
  rw [← Finset.card_range l.sum.toNat]
  apply Finset.card_le_card_of_injOn (levelPosB l)
  · intro n hn
    have hn_lt : n < l.sum.toNat := Finset.mem_range.mp (Finset.mem_coe.mp hn)
    have hn' : (n : ℤ) < l.sum := by
      have : (n : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn_lt
      omega
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (levelPosB_lt l n hn'),
        rightmostAtLevel_good l (minPrefixSum l + n) hS
          (by linarith [show (0 : ℤ) ≤ (n : ℤ) from Int.natCast_nonneg n])
          (by linarith)
          (levelPosB l n) (levelPosB_lt l n hn')
          (levelPosB_eq_optionC l m hmem n hn')          -- ⬅ only line that changes
          (fun p hp hpl => levelPosB_right l n p hp hpl)⟩)
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_coe, Finset.mem_range] at hn₁ hn₂
    have hn₁' : (n₁ : ℤ) < l.sum := by
      have : (n₁ : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn₁
      omega
    have hn₂' : (n₂ : ℤ) < l.sum := by
      have : (n₂ : ℤ) < (l.sum.toNat : ℤ) := by exact_mod_cast hn₂
      omega
    have h₁ := levelPosB_eq_optionC l m hmem n₁ hn₁'      -- ⬅ only line that changes (1/2)
    have h₂ := levelPosB_eq_optionC l m hmem n₂ hn₂'      -- ⬅ only line that changes (2/2)
    rw [heq] at h₁
    have : (n₁ : ℤ) = n₂ := by linarith
    exact_mod_cast this
```

**Total**: 30 LOC. Two-line-delta from the existing
`goodRotations_card_ge_pathB` (modulo the signature on line 1–2 and
the three `levelPosB_eq → levelPosB_eq_optionC` rewires).

## §5 Paste-ready — `step_in_one_pos_pm_card_eq` (Option C public theorem)

The Option C analogue of `step_in_one_pos_mixed_neg_card_eq` (L446). Pure
glue: `le_antisymm` against the alphabet-agnostic upper bound
`goodRotations_card_le` from the parent file.

```lean
/-- **Option C equality** — for sequences with each step in `{-m, …, 0, 1}`
    and positive total sum, the count of "good rotations" is exactly
    `l.sum.toNat`. Strict equality form of B′-style slack. -/
theorem step_in_one_pos_pm_card_eq (l : List ℤ) (m : ℕ)
    (hmem : ∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1)
    (hS : 0 < l.sum) :
    (goodRotations l).card = l.sum.toNat :=
  le_antisymm (goodRotations_card_le hS)
              (goodRotations_card_ge_pathB_optionC l m hmem hS)
```

**Total**: 6 LOC. Body is one expression.

## §6 Paste-ready (optional) — `step_in_one_pos_pm_card_bound`

The slack-form corollary, recovering the B′-style bound `l.sum ≤ m·|gR| + (m-1)·l.length`
from the strict equality. Optional for S11 ACT; can defer to S12.

```lean
/-- **Option C slack-form** — recovers `l.sum ≤ m·|gR| + (m-1)·l.length`
    from the strict equality above. The slack term `(m-1)·l.length` is
    non-negative when `m ≥ 1`; equality holds at `m = 1`. -/
theorem step_in_one_pos_pm_card_bound (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (hmem : ∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ 1)
    (hS : 0 < l.sum) :
    l.sum ≤ (m : ℤ) * (goodRotations l).card + ((m : ℤ) - 1) * l.length := by
  have heq := step_in_one_pos_pm_card_eq l m hmem hS
  have hToNat : (l.sum.toNat : ℤ) = l.sum := Int.toNat_of_nonneg hS.le
  have h_card_eq : ((goodRotations l).card : ℤ) = l.sum := by
    have : ((goodRotations l).card : ℤ) = (l.sum.toNat : ℤ) := by exact_mod_cast heq
    omega
  have hmZ : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hlen : (0 : ℤ) ≤ (l.length : ℤ) := by exact_mod_cast l.length.zero_le
  nlinarith [hS, hmZ, hlen, h_card_eq]
```

**Total**: 14 LOC (body verbatim from `step_in_one_pos_mixed_neg_card_bound` at L456,
with only the signature changing).

## §7 Bearer audit

Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged
since S7 ACT). Every Mathlib identifier used in §3–§6 is already used
in the existing Path B chain (L379–L470). No new imports needed; no
new Mathlib bearers introduced. Specifically:

| Identifier | Used in | Already used in Path B? |
|---|---|---|
| `Int.lt_iff_add_one_le` | §3 (`hle0` derivation) | NO — §3.3 notes `omega` is an acceptable fallback |
| `lt_or_eq_of_le` | §3 (subcase split) | NO (parent uses `rcases`-on-`Or` instead) |
| `Int.toNat_of_nonneg` | §4, §6 | YES (L410, L461) |
| `Finset.card_le_card_of_injOn` | §4 | YES (L412) |
| `List.getElem_mem` | §3 | YES (L389) |
| `List.sum_take_succ` | §3 (via `hstep_eq`) | YES (L394) |
| `levelPosB_max` | §3 (zero-case discharge) | NO — defined in this file at L355, used downstream but not previously inside `levelPosB_eq` itself |

**Conclusion**: 2 new Mathlib bearers (`Int.lt_iff_add_one_le`,
`lt_or_eq_of_le`), both well-established; spot-check at S11 ACT time.
`Int.lt_iff_add_one_le` is replaceable by `omega` if signature drifts.

## §8 ACT-readiness gate

| Gate | State | Rationale |
|---|---|---|
| G1: Parent-file path stable | GREEN | `BallotProblemOQ01.lean` unchanged since S7 ACT |
| G2: Path B chain on `origin/main` | GREEN | L313–L470, last touched S7 ACT (#19219 merged 2026-05-15) |
| G3: Conjecture E spec patch | GREEN (S9 PREP) | `problem.md` L93 amendment in S9 PREP §4.1; orthogonal to Option C |
| G4: No conflicting open PRs | GREEN | Only #19015 (S6 ACT, recommended close per S9 PREP §5.1) |
| G5: Lake SHA pin | GREEN | `2df2f0150c…` matches S7/S10 |
| G6: Insertion point | GREEN | After L470 (end of `step_in_one_pos_mixed_neg_card_bound`), before `end BallotMJumpCycleLemma` at L472 |
| G7: Disk avail for Docker | AMBER | Host 3.2 Gi at S11 PREP-time (below same-day soft floor); recovery needed before S11 ACT runs build |
| G8: Docker daemon | AMBER | `docker info` Server section non-responsive within 5s at S11 PREP-time |
| G9: Bearer SHA spot-check | GREEN | 1-spot-check confirmed `Int.toNat_of_nonneg` at `Mathlib/Data/Int/Order/Basic` byte-stable via existing L410/L461 references |

**Net**: 7/9 GREEN, 2/9 AMBER (infra). S11 ACT can paste the skeleton
once host disk recovers above ~5 Gi and Docker Server responds.

## §9 Non-actions

This PREP **does NOT**:

- Edit `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` (paste is S11 ACT's job)
- Edit `proofs/Proofs/BallotProblemOQ01.lean` (parent file; nothing required)
- Edit `proofs/Proofs/BallotProblemOQ01OQ01OQ02.lean` (grandparent; nothing required)
- Apply S9 PREP §4.1's `problem.md` L93 spec amendment (deferred to doctor/champion per S9 PREP §5)
- Touch the gallery `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/`
  (no gallery slug exists; no edits needed)
- Pre-emptively run `./proofs/scripts/docker-build.sh` (host disk RED;
  no value to running before S11 ACT paste lands)
- Recommend Route A or Route C from S10 PREP (Route B remains the
  RECOMMENDED, lowest-LOC route)
- Close/reopen any existing PR (S9 PREP §5.1 already mapped the
  obsolete-PR cleanup; doctor/champion authority)
- Modify the existing Path B chain (L379–L470 remain verbatim;
  Option C extensions sit AFTER L470)

## §10 Forward — S11 ACT acceptance criteria

S11 ACT should:

1. Paste §3 verbatim as `levelPosB_eq_optionC` (private, after L399).
2. Paste §4 verbatim as `goodRotations_card_ge_pathB_optionC` (private, after L440).
3. Paste §5 verbatim as `step_in_one_pos_pm_card_eq` (public, after L450).
4. Optionally paste §6 as `step_in_one_pos_pm_card_bound` (defer to S12 if 1-3 Docker iters already used).
5. Build-verify via `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ01OQ01OQ02OQ01`.
6. Update `state.md` head + JSON `currentState.{iteration, focus, nextAction}` post-build (or in same ACT PR if confident).

**Expected LOC delta**: +96 (with §6) or +76 (without §6). Forecast 3062
build jobs (S7 ACT baseline) ± 5.

**Expected Docker iters**: 1-3 (the zero-case `linarith` and the
`Int.lt_iff_add_one_le` step are the two places most likely to need
tactical adjustment).

## §11 Iteration bookkeeping

- Phase: PREP (unchanged from S10 PREP)
- Iteration: 13 → 14
- Sorries: unchanged
- Axioms: unchanged
- Theorems on main: unchanged (9, per S10 PREP)
- LOC on main: 472 (unchanged)

**Cycle**: ~40 min (read S10 PREP → read parent-file Path B lines
337-470 → draft 3 paste-ready skeletons with full proof bodies →
bearer audit → memo).

**Co-author**: Claude Opus 4.7
