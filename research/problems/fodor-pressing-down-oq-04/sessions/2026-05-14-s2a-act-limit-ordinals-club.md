# S2-α ACT — Limit ordinals form a club (build-verified)

**Date**: 2026-05-14
**Researcher**: researcher-8
**Mode**: ACT (first Lean ACT after S1 OBSERVE + 5 PREP sessions over 2026-05-12 → 2026-05-13)
**Build**: `Proofs.FodorPressingDown` Docker-verified at 3062 jobs (Mathlib v4.26.0)

## 0. Pre-claim baseline

Six consecutive doc-only PREP PRs (#18193, #18375, #18471, #18544, #18603, #18665)
shipped 2026-05-12 → 2026-05-13. None Docker-built the parent file. Per the
silent-parent-regression heuristic (4+ consecutive doc-only PREPs on the same slug),
the first action this session was a baseline build:

```
$ ./proofs/scripts/docker-build.sh Proofs.FodorPressingDown
⚠ [3062/3062] Built Proofs.FodorPressingDown (5.1s)
warning: Proofs/FodorPressingDown.lean:261:5: unused variable `hS_pos`
warning: Proofs/FodorPressingDown.lean:344:34: unused variable `hTS`
Build completed successfully (3062 jobs).
```

Parent file builds clean on Mathlib v4.26.0 commit `2df2f0150…` — no silent
regression. Green-light to ship S2-α ACT.

## 1. Deliverable

Two theorems added to `proofs/Proofs/FodorPressingDown.lean` (new §Part VII,
inserted between Part VI and the Summary block):

### 1.1 `isLimitOrdinals_isClubBelow`

```lean
theorem isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    IsClubBelow {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} κ.ord where
  subset_Iio := fun _ ha => ha.1
  closed := by
    rw [isClosedBelow_iff]
    intro p hpκ pAcc
    refine ⟨hpκ, ?_⟩
    have hpos : (0 : Ordinal) < p := pAcc.pos
    have hAcc : ∀ q < p,
        ∃ r ∈ {α : Ordinal | α < κ.ord ∧ IsSuccLimit α}, q < r ∧ r < p := by
      rw [isAcc_iff] at pAcc
      exact pAcc.2
    refine ⟨?_, ?_⟩
    · intro hmin
      exact hpos.ne' (le_antisymm (hmin (le_of_lt hpos)) (le_of_lt hpos))
    · intro b hcov
      obtain ⟨r, _, hbr, hrp⟩ := hAcc b hcov.1
      exact hcov.2 hbr hrp
  unbounded := by
    intro α hα
    have hω_lt : Ordinal.omega0 < κ.ord := by
      rw [show Ordinal.omega0 = (ℵ₀ : Cardinal).ord from Cardinal.ord_aleph0.symm]
      exact Cardinal.ord_lt_ord.mpr hκ_unc
    have hαω_lt : α + Ordinal.omega0 < κ.ord := by
      rw [Cardinal.lt_ord, Ordinal.card_add, Ordinal.card_omega0]
      exact Cardinal.add_lt_of_lt hκ.aleph0_le (Cardinal.lt_ord.mp hα) hκ_unc
    refine ⟨α + Ordinal.omega0, ⟨hαω_lt, ?_⟩, ?_, hαω_lt⟩
    · exact Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0
    · have h : α + 0 < α + Ordinal.omega0 :=
        (Ordinal.isNormal_add_right α).strictMono Ordinal.omega0_pos
      rwa [add_zero] at h
```

### 1.2 `nonLimitOrdinals_not_isStationaryBelow` (corollary)

```lean
theorem nonLimitOrdinals_not_isStationaryBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    ¬ IsStationaryBelow {α : Ordinal | α < κ.ord ∧ ¬ IsSuccLimit α} κ.ord := by
  intro hStat
  obtain ⟨_, hγnonlim, hγlim⟩ :=
    hStat {α | α < κ.ord ∧ IsSuccLimit α} (isLimitOrdinals_isClubBelow hκ hκ_unc)
  exact hγnonlim.2 hγlim.2
```

Net delta: +68 LOC, +2 theorems, 0 sorries, 0 axioms. File now 453 LOC,
14 theorems, 3 defs, 0 sorries, 0 axioms.

## 2. Build iteration log

Four Docker builds total. Iteration count above the predicted single-build path
because of Mathlib v4.26.0 surface deltas not visible at the `gh api`/`grep` level
that S5/S6 PREP audits used.

### Build #1 — baseline

Parent file on origin/main with no S2-α additions. 3062 jobs clean. Confirmed
no silent regression in the 6-PREP chain.

### Build #2 — initial S2-α with S6 PREP names verbatim

Failed with 5 errors:

1. **`refine ⟨?_, ?_⟩` for `IsSuccLimit p` — wrong field order**.
   `IsSuccLimit a` has `¬ IsMin a` as the first field and `IsSuccPrelimit a` as
   the second. My initial `intro b hcov` (for IsSuccPrelimit) hit `b : IsMin p`
   instead. Fix: swap the order of the two `refine` cases.

2. **`Ordinal.zero_le` unknown**. Not present at that name in v4.26.0. Fix:
   replace `Ordinal.zero_le p` with `le_of_lt hpos`.

3. **`Cardinal.isPrincipal_add_ord` unknown**. S6 PREP §6 cited this name at
   `Mathlib/SetTheory/Cardinal/Ordinal.lean:204` (commit `2df2f0150…`) but the
   build container resolves it as unknown — likely because of namespacing
   changes between the `gh api contents`-pinned name and the actual exported
   name at v4.26.0 release. Fix: bridge through cardinality with
   `Cardinal.lt_ord` + `Ordinal.card_add` + `Cardinal.add_lt_of_lt`.

4. **`Ordinal.add_lt_add_left` unknown**. Generic bare-name `add_lt_add_left`
   from the typeclass also failed (Build #3 below). Fix: use
   `(Ordinal.isNormal_add_right α).strictMono`, which is exported and works.

5. **`Ordinal.add_zero` unknown**. The lemma is in the AddMonoid instance, not
   namespaced. Fix: use bare `add_zero`.

### Build #3 — generic `add_lt_add_left`, IsSuccLimit reorder, cardinality bridge

Failed with 1 error:

> Proofs/FodorPressingDown.lean:401:45: failed to synthesize
>   AddRightStrictMono Ordinal.{0}

The generic `add_lt_add_left` (from the `CovariantClass`-based typeclass) tries
to synthesize `AddRightStrictMono Ordinal`, but ordinal addition is only
left-strictly-monotone (`b < c → a + b < a + c`), not right (`a < b → a + c <
b + c` fails for `c = ω₀, a = 0, b = 1`). Fix: use `IsNormal.strictMono` on
`isNormal_add_right`, which is the export that captures left-strict-monotonicity
for ordinal left-addition.

### Build #4 — IsNormal path

3062 jobs clean, one new lint warning (`simpa using h` → `simp at h; exact h`
since `add_zero` doesn't change the goal). Replaced `simpa using h` with
`rwa [add_zero] at h`.

### Build #5 — final

3062 jobs clean, no new warnings beyond the 2 pre-existing ones (`hS_pos` at
line 261 and `hTS` at line 344, both unrelated to S2-α).

## 3. Mathlib v4.26.0 surface deltas surfaced this session

These are NEW MEMORY-worthy findings for the researcher feedback corpus,
analogous to the existing v4.26.0 kits in `MEMORY.md`:

### 3.1 `Cardinal.isPrincipal_add_ord` is not exported

S6 PREP audited this via `gh api repos/.../contents/Mathlib/SetTheory/Cardinal/Ordinal.lean`
and found `theorem isPrincipal_add_ord` at line 204. But the v4.26.0 build cache
resolves the name as unknown — both bare `isPrincipal_add_ord` and qualified
`Cardinal.isPrincipal_add_ord` fail. Either the name was renamed before release
or the namespace is different than `Cardinal`.

**Workaround that works at v4.26.0**: cardinality bridge.

```lean
have hαω_lt : α + Ordinal.omega0 < κ.ord := by
  rw [Cardinal.lt_ord, Ordinal.card_add, Ordinal.card_omega0]
  exact Cardinal.add_lt_of_lt hκ.aleph0_le (Cardinal.lt_ord.mp hα) hκ_unc
```

This adds 3 LOC vs the projected 1-line `isPrincipal_add_ord` citation.

### 3.2 Ordinal addition has no `AddRightStrictMono` instance

`add_lt_add_left h c : c + a < c + b` from the generic `CovariantClass`-derived
lemma requires `AddRightStrictMono`, which does NOT hold for `Ordinal` (since
ordinal addition is left-strict but not right-strict).

**Workaround that works at v4.26.0**: use `IsNormal.strictMono` directly.

```lean
have h : α + 0 < α + Ordinal.omega0 :=
  (Ordinal.isNormal_add_right α).strictMono Ordinal.omega0_pos
rwa [add_zero] at h
```

The IsNormal-of-left-addition fact (`Ordinal.isNormal_add_right α : IsNormal (α + ·)`)
is at `Mathlib/SetTheory/Ordinal/Arithmetic.lean:507` (verified by S6 PREP §6).

### 3.3 `IsSuccLimit a` is `¬IsMin ∧ IsSuccPrelimit`, not the reverse

The order matters for `refine ⟨?_, ?_⟩`. First goal is `¬ IsMin a`, second is
`IsSuccPrelimit a` (i.e., `∀ b, ¬ b ⋖ a`). The build error is informative —
the first `intro` binder fails because `¬ IsMin a` only has one binder (the
`IsMin a` hypothesis), not two.

## 4. Honesty assessment

What this session produced:

* Two build-verified Lean theorems in the parent file (+68 LOC, 0 sorries, 0 axioms).
* Three NEW Mathlib v4.26.0 surface-delta findings (§3 above) for future MEMORY
  entries — these were NOT detected by 5 prior PREP sessions because `gh api`
  contents-reads don't validate name exports at the release pin.
* Step 1 of the three-step Solovay splitting proof, decomposing the OQ into a
  reachable S3 (binary splitting) next-action.

What it did NOT produce:

* Solovay splitting proper (the OQ asks for full κ-splitting; Step 1 alone is
  not the answer).
* Binary splitting (S2-β / S3): the next target, ~120–250 LOC, single Fodor
  application.
* Any axiom-elimination (file was already 0 axioms before; remains 0 after).

What this means in context: the PREP-heavy 16-hour stretch on this slug
(S1 OBSERVE + 5 PREPs, ~12 hours of cumulative session time) converted into
one build-verified ACT delivering a foundational sub-lemma. That's good progress,
but the full Solovay splitting is at least 2 more ACT sessions away (S3 for
binary, S4+ for full κ-splitting), and `Classical.skolem` integration in S4+
is a real risk that should be audited before committing.

## 5. Race awareness

Pre-claim check: `gh pr list --search "fodor-pressing-down-oq-04 in:title" --state open -R rjwalters/lean-genius`
returned `[]`. Six prior PRs all merged. Lean changes are strictly additive
(new §Part VII between Part VI and the Summary block) — no edit overlap with
the in-flight Club refactor on the sibling slug `fodor-pressing-down-oq-01`
(both slugs target the same file but orthogonal sections).

## 6. References

* This repo:
  * `proofs/Proofs/FodorPressingDown.lean` (385 → 453 LOC).
  * `research/problems/fodor-pressing-down-oq-04/state.md` (refreshed to S2 ACT phase).
  * `src/data/research/problems/fodor-pressing-down-oq-04.json` (phase OBSERVE → ACT, iter 1 → 7).
  * Prior sessions:
    - `2026-05-12-s02-prep-stepI-limit-club.md` (S2 PREP — design)
    - `2026-05-13-s3-prep-cofinality-bound-fodor.md` (S3 PREP — Step IIa precursor)
    - `2026-05-13-s04-prep-mathlib-name-verification.md` (S4 PREP — names)
    - `2026-05-13-s5-prep-s2-tentative-name-audit.md` (S5 PREP — TENTATIVE → CONFIRMED/PHANTOM)
    - `2026-05-13-s6-prep-row2-row4-erratum-closure.md` (S6 PREP — ERRATUM closure)
* PRs:
  - #18193 (S1 OBSERVE, MERGED 2026-05-12)
  - #18375 (S2 PREP, MERGED 2026-05-13)
  - #18471 (S3 PREP, MERGED 2026-05-13)
  - #18544 (S4 PREP, MERGED 2026-05-13)
  - #18603 (S5 PREP, MERGED 2026-05-13)
  - #18665 (S6 PREP, MERGED 2026-05-13)
  - This session: S2-α ACT (pending)
* Mathlib commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). Files used:
  - `Mathlib/SetTheory/Ordinal/Arithmetic.lean:507` (`isNormal_add_right`)
  - `Mathlib/SetTheory/Ordinal/Arithmetic.lean:511` (`isSuccLimit_add`)
  - `Mathlib/SetTheory/Ordinal/Arithmetic.lean:1056` (`isSuccLimit_omega0`)
  - `Mathlib/SetTheory/Ordinal/Basic.lean:1127` (`ord_lt_ord`)
  - `Mathlib/SetTheory/Ordinal/Basic.lean:1157` (`ord_aleph0`)
  - `Mathlib/SetTheory/Cardinal/Cofinality.lean` (`add_lt_of_lt` — regularity-based cardinality addition closure)

---

**End of S2-α ACT — 2 new theorems, 68 LOC, 0 sorries, 0 axioms, 4 Docker
iterations to build-clean. Three NEW Mathlib v4.26.0 surface-delta findings
that 5 prior PREP sessions did not detect. Step 1 of Solovay splitting
complete; S3 (binary splitting) is the next target.**
