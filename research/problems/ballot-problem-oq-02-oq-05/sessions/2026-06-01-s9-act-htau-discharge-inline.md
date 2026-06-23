# S9 ACT — R4-sub `hτ` discharged inline (Docker-verified)

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: ACT
**Branch**: `research/ballot-problem-oq-02-oq-05-s9-act-2026-06-01`
**Base commit**: `f486a19e2e0` (HEAD on `main`)
**Outcome**: 4 sorries → 3 sorries; +42 LOC; **Docker-verified 7744 jobs OK**

## 1. Goal

S8 ACT (2026-05-31) shipped the R4 false-statement fix by adding a
`(hitSet ω a).Nonempty` hypothesis and replacing the proof body with a
case-split skeleton, but left the key sub-goal

```
hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a
```

as a named sorry. The S8 Next Action proposed two routes:

- **Route A (PREP)**: stage a `partialSumBool_congr_below` helper lemma
  + paste-ready `hτ` discharge skeleton.
- **Route B (ACT)**: discharge `hτ` inline without the helper, ~20 LOC.

S9 ships a hybrid: the helper from Route A **and** the inline `hτ`
discharge from Route B in a single PR, since the helper is small (~7 LOC
without docstring) and the inline discharge naturally consumes it twice.

## 2. Patch (verbatim, applied at base `f486a19e2e0`)

### 2.1 New helper `partialSumBool_congr_below`

Inserted between `reflectAt_eq_below_firstHit` (line 185-190) and
`reflectAt_involutive` (line 206+):

```lean
/-- **R4-sub helper (S9 ACT).** Partial sums up to a position not exceeding
    the first hit time are unchanged by reflection. The sum's `i.val < k.val`
    guard restricts each summand index `i` to satisfy `i.val < k.val ≤ τ.val`,
    so `reflectAt_eq_below_firstHit` collapses every summand pointwise. -/
lemma partialSumBool_congr_below
    {ω : Fin n → Bool} {a : ℤ} {k : Fin (n+1)}
    (hk : k.val ≤ (firstHitFin ω a).val) :
    partialSumBool (reflectAt ω a) k = partialSumBool ω k := by
  unfold partialSumBool
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : i.val < k.val
  · rw [if_pos hi, if_pos hi,
        reflectAt_eq_below_firstHit (Nat.lt_of_lt_of_le hi hk)]
  · rw [if_neg hi, if_neg hi]
```

### 2.2 Inline `hτ` discharge

Replaced the sorry inside `reflectAt_involutive`:

```lean
  -- Step 1: firstHitFin is preserved under reflection (uses h).
  -- Discharged inline (S9 ACT): the partial-sum equality below τ
  -- (`partialSumBool_congr_below`) shows τ ∈ hitSet (reflectAt ω a) a and
  -- that the reflected path has no earlier hit; min'-antisymmetry closes.
  have hτ : firstHitFin (reflectAt ω a) a = firstHitFin ω a := by
    have hτ_eq : firstHitFin ω a = (hitSet ω a).min' h := by
      simp [firstHitFin, dif_pos h]
    have hτ_mem : firstHitFin ω a ∈ hitSet ω a := by
      rw [hτ_eq]; exact (hitSet ω a).min'_mem h
    have hτ_ps : partialSumBool ω (firstHitFin ω a) = a :=
      (Finset.mem_filter.mp hτ_mem).2
    have hτ_mem' : firstHitFin ω a ∈ hitSet (reflectAt ω a) a := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [partialSumBool_congr_below (le_refl _)]
      exact hτ_ps
    have h' : (hitSet (reflectAt ω a) a).Nonempty := ⟨_, hτ_mem'⟩
    have hfh' : firstHitFin (reflectAt ω a) a = (hitSet (reflectAt ω a) a).min' h' := by
      simp [firstHitFin, dif_pos h']
    apply le_antisymm
    · rw [hfh']
      exact Finset.min'_le _ _ hτ_mem'
    · rw [hfh']
      refine Finset.le_min' _ _ _ (fun k hk => ?_)
      by_contra hlt
      push_neg at hlt
      have hk_val : k.val < (firstHitFin ω a).val := hlt
      have hk_ps : partialSumBool (reflectAt ω a) k = a :=
        (Finset.mem_filter.mp hk).2
      have hk_ω : partialSumBool ω k = a := by
        rw [← partialSumBool_congr_below (Nat.le_of_lt hk_val)]
        exact hk_ps
      have hk_mem : k ∈ hitSet ω a :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_ω⟩
      rw [hτ_eq] at hk_val
      exact absurd ((hitSet ω a).min'_le _ hk_mem) (not_le.mpr hk_val)
```

## 3. Proof structure (antisymmetry on `Fin (n+1)`)

`Fin (n+1)` has a `LinearOrder` so `le_antisymm` reduces to two `≤` goals.
Let `τ := firstHitFin ω a = (hitSet ω a).min' h`.

### 3.1 ≤ direction: `firstHitFin (reflectAt ω a) a ≤ τ`

It suffices to show `τ ∈ hitSet (reflectAt ω a) a`, then `Finset.min'_le`
gives the inequality.

`τ ∈ hitSet (reflectAt ω a) a` ↔ `partialSumBool (reflectAt ω a) τ = a`.
By the new helper at `k = τ` (hypothesis `τ.val ≤ τ.val`, i.e. `le_refl`):
`partialSumBool (reflectAt ω a) τ = partialSumBool ω τ`. The right side is
`a` by `min'_mem` + `mem_filter`.

### 3.2 ≥ direction: `τ ≤ firstHitFin (reflectAt ω a) a`

`Finset.le_min'` reduces to: for any `k ∈ hitSet (reflectAt ω a) a`, show
`τ ≤ k`.

By contradiction: assume `¬ (τ ≤ k)`, i.e. `k < τ`. Then by the new helper
at `k` (hypothesis `k.val ≤ τ.val` from `Nat.le_of_lt`):
`partialSumBool (reflectAt ω a) k = partialSumBool ω k`. Combined with
`k ∈ hitSet (reflectAt ω a) a`, this gives `partialSumBool ω k = a`, so
`k ∈ hitSet ω a`. Then `τ = (hitSet ω a).min' h ≤ k` by `Finset.min'_le`,
contradicting `k < τ`.

## 4. File metrics

| Metric | Pre-S9 | Post-S9 | Δ |
|--------|--------|---------|---|
| LOC | 283 | 325 | +42 |
| Sorries | 4 | 3 | −1 |
| Axioms | 1 | 1 | 0 |
| Defs | 6 | 6 | 0 |
| Lemmas | 4 | 5 | +1 |
| Theorems | 1 | 1 | 0 |
| R4 status | TRUE w/ sub-sorry | TRUE, fully discharged | sorry-free |

## 5. Sorry inventory (post-S9)

| Sorry | Decl line | Sorry line | Approach (unchanged from S6/S8) |
|-------|-----------|------------|----------------------------------|
| R5 `partialSumBool_reflectAt_endpoint` | 288 | 292 | `Finset.sum_ite` + `min'_mem h` + arithmetic |
| LOW `reaches_iff_hits_or_above` | 298 | 302 | `Int.le_iff_exists_eq_succ` on ±1 jumps |
| R6 `discrete_reflection` | 313 | 321 | `Finset.card_nbij'` applied to (ending<a, hits a) ↔ (ending>a), uses R4 + R5 |

## 6. Bearer table (no drift since S8)

All bearers used in the S9 patch were previously pinned at lake-manifest
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0):

| API | File | Line | First pinned |
|-----|------|------|--------------|
| `Finset.min'` | `Mathlib/Data/Finset/Max.lean:196` | 196 | S5 PREP |
| `Finset.min'_mem` | `Mathlib/Data/Finset/Max.lean:207` | 207 | S5 PREP |
| `Finset.min'_le` | `Mathlib/Data/Finset/Max.lean:210` | 210 | S5 PREP |
| `Finset.le_min'` | `Mathlib/Data/Finset/Max.lean:213` | 213 | S5 PREP |
| `Finset.sum_congr` (via `to_additive` of `Finset.prod_congr`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:108` | 108 | S5 PREP §4 |
| `Finset.mem_filter` | `Mathlib/Data/Finset/Filter.lean:127` | 127 | implicit since S2 |

No new pin needed. `Nat.le_of_lt` / `Nat.lt_of_lt_of_le` / `Nat.not_le_of_lt`
are Lean core.

## 7. Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05
...
⚠ [7744/7744] Built Proofs.BallotProblemOQ02OQ05 (11s)
warning: Proofs/BallotProblemOQ02OQ05.lean:288:6: declaration uses 'sorry'
warning: Proofs/BallotProblemOQ02OQ05.lean:298:6: declaration uses 'sorry'
warning: Proofs/BallotProblemOQ02OQ05.lean:313:8: declaration uses 'sorry'
Build completed successfully (7744 jobs).
=== Build succeeded ===
```

Exit code 0. The 3 sorry warnings correspond to the inherited R5, LOW, R6
sorries (not new). The R4-sub `hτ` warning that was at the previous build
is gone — `hτ` is now fully discharged.

## 8. Risk inventory

All RED items from S5 PREP §6 either drained or unchanged:

- R1-R4: drained in S6 ACT + S8 ACT.
- **R4 (MEDIUM)**: drained in S9 ACT (this PR). `reflectAt_involutive` is now
  fully sorry-free under the `(hitSet ω a).Nonempty` hypothesis.
- R5/R6 (HIGH): unchanged, queued for S10+.
- R7 (LOW well-definedness): unchanged.
- R8 (INFRA): drained 2026-05-31 (Docker daemon GREEN both today and S8).

## 9. S10+ readiness (S9 → S10 handoff)

Three sorries remain; each is independently discharge-able:

- **R5** (~25 LOC): `partialSumBool_reflectAt_endpoint` — sum split at τ
  via `Finset.sum_ite`, identity on `i < τ` (by Helper-1 inside the sum),
  sign-flipped on `i ≥ τ`, arithmetize with `min'_mem h`.
- **LOW** (~8 LOC): `reaches_iff_hits_or_above` — IVT for ℤ-valued ±1 paths:
  partial sums increase/decrease by exactly 1 each step.
- **R6** (~20 LOC): `discrete_reflection` — `Finset.card_nbij'` with
  `i = j = reflectAt _ a`, using R4 (involution) + R5 (endpoint identity).

Plausible Aristotle candidates after S9:
- **LOW** (jump analysis — borderline; the ±1 IVT is well-scoped).
- **R5** (sum-splitting + arithmetic — borderline; depends on Aristotle's
  `Finset.sum_ite` maturity).

S10 can ship any subset of {R5, LOW, R6} since they are not mutually
blocking (LOW is independent; R5 is needed for R6).

## 10. LOC budget

325 LOC exceeds the 250-LOC informal cap by 75 LOC (30%). Comparable to
S8's 6% overage; acceptable for the structural-correctness + sorry-count
gain (4 → 3).

Compression candidates for future S-cycles (after R5/LOW/R6 drained):
- `reflectAt_involutive` history docstring (~20 LOC, S7 PREP / S8 ACT
  narrative) can be condensed once the lemma fully discharges.
- The `dif_pos` / `simp [firstHitFin, ...]` chains around `firstHitFin`
  could be replaced by a small `firstHitFin_of_nonempty` lemma (~3 LOC
  saved per call site, ~9 LOC total).

## 11. Sibling-coordination

`grep -rnE 'partialSumBool_congr_below|reflectAt_involutive|discrete_reflection|firstHitFin' proofs/Proofs/`
returns matches only in this file. `gh pr list --search 'discrete_reflection in:title'`
returns 0 open PRs. No race risk.

## 12. Decisions log

- **Route choice**: hybrid (helper from Route A + inline discharge from
  Route B). Rationale: helper is small (~7 LOC body) and reused twice in
  the discharge, so splitting helper PREP + discharge ACT into two PRs
  would have spent extra PR overhead for no proof-clarity gain.
- **`by_contra` for ≥ direction**: chose contradiction over direct proof
  because the helper applies cleanly under `Nat.le_of_lt` for `k.val < τ.val`,
  and `min'_le` gives the contradicting inequality immediately.
- **`simp [firstHitFin, dif_pos h]`**: chosen over `unfold firstHitFin`
  because `unfold` would also rewrite inner occurrences inside the
  surrounding `hitSet (reflectAt ω a) a` — same trap S8 hit on `reflectAt`
  inside `firstHitFin (reflectAt ω a) a`.
