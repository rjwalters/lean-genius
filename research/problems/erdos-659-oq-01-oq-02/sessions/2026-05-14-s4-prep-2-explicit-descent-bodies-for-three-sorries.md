# S4-PREP-2 — Explicit `Nat.strongRecOn` descent bodies for the three S3 SCAFFOLD sorries

**Date**: 2026-05-14
**Researcher**: researcher-8
**Mode**: PREP (doc-only)
**Builds on**: S3 ACT SCAFFOLD PR #18947 (Lean file, on `origin/main`) +
S4 PREP PR #19028 (open, ZMod 5 helpers + S4 ACT plan sketch)
**Goal**: write copy-paste-ready Lean tactic bodies for the three strategic
sorries (`safe_A_holds`, `safe_B_holds`, `safe_C_holds`) in
`proofs/Proofs/Erdos659OQ01OQ02.lean` lines 88/96/104, using the two
ZMod 5 helpers from PR #19028 plus standard Mathlib integer-divisibility
bearers. Each body is ~25-30 LOC; total estimated ACT diff ~85-95 LOC
across the three discharges. **No Lean edits in this PR** — the bodies
remain to be transcribed by the next S4 ACT worker after PR #19028
merges.

## 1. Scope and dependencies

This PREP refines PR #19028's "Next action (S4 ACT)" Step 1-4 sketch
into a concrete, tactic-by-tactic Lean body. The work decomposes into
three independent discharges:

| Sorry | File line | Equation | Mod-5 helper (from #19028) | Descent variable |
|-------|-----------|----------|---------------------------|------------------|
| `safe_A_holds` | 90 | `5 c² = a² + 2 b²` | `zmod_5_a_sq_plus_2_b_sq_eq_zero_iff` | `c.natAbs` |
| `safe_B_holds` | 98 | `2 b² = a² + 5 c²` | `zmod_5_a_sq_eq_two_b_sq_iff` | `b.natAbs` |
| `safe_C_holds` | 106 | `a² = 2 b² + 5 c²` | `zmod_5_a_sq_eq_two_b_sq_iff` | `a.natAbs` |

**Prerequisite ordering**: PR #19028 must merge first so the two helpers
are in-scope on the file's namespace. After #19028 merges, the bodies
below can be transcribed in a single S4 ACT PR.

## 2. Bearer lemma re-audit at Mathlib v4.26.0

Beyond PR #19028's two `decide`-checked helpers, the integer-side
descent needs three Mathlib bearers, all verified present at
`rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Bearer | Mathlib path | Role |
|--------|--------------|------|
| `Int.coe_zmod_eq_zero_iff_dvd` | `Mathlib/Data/ZMod/Basic.lean` | Translate `(a : ZMod 5) = 0` ↔ `(5 : ℤ) ∣ a` |
| `Int.Prime.dvd_mul` (or `Prime.dvd_mul`) | `Mathlib/RingTheory/Int/Basic.lean` | `5 ∣ a² → 5 ∣ a` (via `Int.Prime.dvd_mul.mp`) |
| `Nat.strongRecOn` | `Mathlib/Data/Nat/Init.lean` | Well-founded descent on `c.natAbs` |

The S2b PREP §5 template cited `Int.Prime.dvd_natAbs_of_coe_dvd_sq` at
`Mathlib/Data/Int/NatPrime.lean:38`. At v4.26.0 the equivalent route
goes through `Int.coe_zmod_eq_zero_iff_dvd` (translating
`a = 0 in ZMod 5` to `(5 : ℤ) ∣ a`) — slightly cleaner because the new
mod-5 helper already produces a `ZMod 5 = 0` conclusion.

## 3. Tactic body for `safe_A_holds` (~30 LOC)

The S2b PREP §4.1 derivation in Lean form, using PR #19028's
`zmod_5_a_sq_plus_2_b_sq_eq_zero_iff` for the mod-5 step:

```lean
theorem safe_A_holds : safe_A := by
  -- Strong recursion on the absolute value of c.
  suffices h : ∀ n : ℕ, ∀ a b c : ℤ,
      c.natAbs = n → (5 : ℤ) * c ^ 2 = a ^ 2 + 2 * b ^ 2 →
      a = 0 ∧ b = 0 ∧ c = 0 by
    intro a b c heq
    exact h c.natAbs a b c rfl heq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn heq
    -- Step 1: mod 5, deduce a = 0 ∧ b = 0 in ZMod 5.
    have h5_dvd : (5 : ℤ) ∣ a ^ 2 + 2 * b ^ 2 := ⟨c ^ 2, heq.symm⟩
    have hzmod : ((a : ZMod 5)) ^ 2 + 2 * ((b : ZMod 5)) ^ 2 = 0 := by
      have := (Int.coe_zmod_eq_zero_iff_dvd _ _).mpr h5_dvd
      push_cast at this; linarith [this]  -- or `convert this; ring`
    obtain ⟨ha0, hb0⟩ := (zmod_5_a_sq_plus_2_b_sq_eq_zero_iff _ _).mp hzmod
    -- Step 2: lift to ℤ-divisibility for a and b.
    have h5a : (5 : ℤ) ∣ a := (Int.coe_zmod_eq_zero_iff_dvd a 5).mp (by exact_mod_cast ha0)
    have h5b : (5 : ℤ) ∣ b := (Int.coe_zmod_eq_zero_iff_dvd b 5).mp (by exact_mod_cast hb0)
    obtain ⟨a', ha'⟩ := h5a
    obtain ⟨b', hb'⟩ := h5b
    -- Step 3: substitute, derive 5 ∣ c².
    rw [ha', hb'] at heq
    have hc2 : (5 : ℤ) ∣ c ^ 2 := by
      have : c ^ 2 = 5 * (a' ^ 2 + 2 * b' ^ 2) := by linarith
      exact ⟨a' ^ 2 + 2 * b' ^ 2, this⟩
    -- Step 4: deduce 5 ∣ c via prime divisibility.
    have hprime5 : Prime (5 : ℤ) := by exact_mod_cast (Nat.prime_iff_prime_int.mp (by decide))
    have h5c : (5 : ℤ) ∣ c := hprime5.dvd_of_dvd_pow hc2
    obtain ⟨c', hc'⟩ := h5c
    rw [hc'] at heq
    -- After substitution: 5 (5c')² = (5a')² + 2 (5b')² → 5 c'² = a'² + 2 b'².
    have heq' : (5 : ℤ) * c' ^ 2 = a' ^ 2 + 2 * b' ^ 2 := by linarith
    -- Step 5: descent — c'.natAbs < c.natAbs (since c = 5c' and c.natAbs > 0 or c = 0).
    rcases eq_or_ne c 0 with hc0 | hc0
    · -- c = 0 forces a² + 2b² = 0, so a = 0 and b = 0.
      refine ⟨?_, ?_, hc0⟩
      · rw [hc0] at heq; nlinarith [sq_nonneg a, sq_nonneg b]
      · rw [hc0] at heq; nlinarith [sq_nonneg a, sq_nonneg b]
    · have hc'_lt : c'.natAbs < c.natAbs := by
        rw [hc']; simp [Int.natAbs_mul]
        exact Nat.lt_mul_iff_one_lt_left (Int.natAbs_pos.mpr (mul_ne_zero (by decide : (5 : ℤ) ≠ 0) (by
          rintro rfl; simp at hc'; exact hc0 hc')).symm) (by decide : 1 < 5)
      obtain ⟨ha'_z, hb'_z, hc'_z⟩ := ih c'.natAbs (hn ▸ hc'_lt) a' b' c' rfl heq'
      exact ⟨ha' ▸ by simp [ha'_z], hb' ▸ by simp [hb'_z], hc' ▸ by simp [hc'_z]⟩
```

**Notes**:
- The `c = 0` case-split avoids the trivial-trivial loop where
  `Nat.strongRecOn` would otherwise need `c.natAbs > 0`.
- The cast-and-decide path
  `Prime (5 : ℤ) := by exact_mod_cast (Nat.prime_iff_prime_int.mp (by decide))`
  is the v4.26.0-canonical way to lift `Nat.Prime 5` (decide-able) to
  `Prime (5 : ℤ)` (the integer-side prime predicate needed by
  `dvd_of_dvd_pow`).
- The `nlinarith [sq_nonneg a, sq_nonneg b]` discharge of "a² + 2b² = 0
  ⇒ a = 0" is the standard non-negativity trick; alternatively
  `Int.sq_eq_zero_iff.mp` after factoring.
- The final `simp [ha'_z]` etc. line uses the IH outputs
  `a' = 0`, `b' = 0`, `c' = 0` to derive `a = 5a' = 0`, etc.

## 4. Tactic body for `safe_B_holds` (~28 LOC)

Equation B: `2 b² = a² + 5 c²`. The mod-5 step uses the second helper
(`zmod_5_a_sq_eq_two_b_sq_iff`); the descent variable is `b.natAbs`
(since the mod-5 step deduces `5 ∣ a` and `5 ∣ b` but only after
recognising that `a² ≡ 2 b² (mod 5)` after subtracting `5 c²`):

```lean
theorem safe_B_holds : safe_B := by
  suffices h : ∀ n : ℕ, ∀ a b c : ℤ,
      b.natAbs = n → (2 : ℤ) * b ^ 2 = a ^ 2 + 5 * c ^ 2 →
      a = 0 ∧ b = 0 ∧ c = 0 by
    intro a b c heq; exact h b.natAbs a b c rfl heq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn heq
    -- Step 1: mod 5, deduce a² ≡ 2 b² (mod 5), then a = 0 ∧ b = 0 in ZMod 5.
    have h5_dvd : (5 : ℤ) ∣ a ^ 2 - 2 * b ^ 2 := by
      refine ⟨-c ^ 2, ?_⟩; linarith
    have hzmod : ((a : ZMod 5)) ^ 2 = 2 * ((b : ZMod 5)) ^ 2 := by
      have h := (Int.coe_zmod_eq_zero_iff_dvd _ _).mpr h5_dvd
      push_cast at h; linarith
    obtain ⟨ha0, hb0⟩ := (zmod_5_a_sq_eq_two_b_sq_iff _ _).mp hzmod
    have h5a : (5 : ℤ) ∣ a := (Int.coe_zmod_eq_zero_iff_dvd a 5).mp (by exact_mod_cast ha0)
    have h5b : (5 : ℤ) ∣ b := (Int.coe_zmod_eq_zero_iff_dvd b 5).mp (by exact_mod_cast hb0)
    obtain ⟨a', ha'⟩ := h5a; obtain ⟨b', hb'⟩ := h5b
    rw [ha', hb'] at heq
    -- 2(5b')² = (5a')² + 5c² ⇒ 50 b'² = 25 a'² + 5 c² ⇒ 10 b'² = 5 a'² + c².
    -- So 5 ∣ c² ⇒ 5 ∣ c.
    have hc2 : (5 : ℤ) ∣ c ^ 2 := by
      refine ⟨2 * b' ^ 2 - a' ^ 2, ?_⟩; linarith
    have hprime5 : Prime (5 : ℤ) := by exact_mod_cast (Nat.prime_iff_prime_int.mp (by decide))
    have h5c : (5 : ℤ) ∣ c := hprime5.dvd_of_dvd_pow hc2
    obtain ⟨c', hc'⟩ := h5c; rw [hc'] at heq
    have heq' : (2 : ℤ) * b' ^ 2 = a' ^ 2 + 5 * c' ^ 2 := by linarith
    -- Descent on b.natAbs.
    rcases eq_or_ne b 0 with hb0_int | hb0_int
    · refine ⟨?_, hb0_int, ?_⟩
      · rw [hb0_int] at heq; nlinarith [sq_nonneg a, sq_nonneg c]
      · rw [hb0_int] at heq; nlinarith [sq_nonneg a, sq_nonneg c]
    · have hb'_lt : b'.natAbs < b.natAbs := by
        rw [hb']; simp [Int.natAbs_mul]
        exact Nat.lt_mul_iff_one_lt_left
          (Int.natAbs_pos.mpr (fun heq0 => hb0_int (by rw [hb', heq0]; ring))) (by decide)
      obtain ⟨ha'_z, hb'_z, hc'_z⟩ := ih b'.natAbs (hn ▸ hb'_lt) a' b' c' rfl heq'
      exact ⟨ha' ▸ by simp [ha'_z], hb' ▸ by simp [hb'_z], hc' ▸ by simp [hc'_z]⟩
```

**Key delta from `safe_A_holds`**:
- `h5_dvd` form is `a² - 2 b²` not `a² + 2 b²`, with witness `-c²`.
- The mod-5 conclusion uses `_a_sq_eq_two_b_sq_iff` (eq form) not
  `_a_sq_plus_2_b_sq_eq_zero_iff` (sum-eq-zero form).
- The intermediate `5 ∣ c²` deduction routes through
  `2 b' ^ 2 - a' ^ 2` not the symmetric form.

## 5. Tactic body for `safe_C_holds` (~26 LOC)

Equation C: `a² = 2 b² + 5 c²`. Mirror of `safe_B_holds` with `a` and
`b` swapped in the descent variable role:

```lean
theorem safe_C_holds : safe_C := by
  suffices h : ∀ n : ℕ, ∀ a b c : ℤ,
      a.natAbs = n → a ^ 2 = (2 : ℤ) * b ^ 2 + 5 * c ^ 2 →
      a = 0 ∧ b = 0 ∧ c = 0 by
    intro a b c heq; exact h a.natAbs a b c rfl heq
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn heq
    have h5_dvd : (5 : ℤ) ∣ a ^ 2 - 2 * b ^ 2 := ⟨c ^ 2, by linarith⟩
    have hzmod : ((a : ZMod 5)) ^ 2 = 2 * ((b : ZMod 5)) ^ 2 := by
      have h := (Int.coe_zmod_eq_zero_iff_dvd _ _).mpr h5_dvd
      push_cast at h; linarith
    obtain ⟨ha0, hb0⟩ := (zmod_5_a_sq_eq_two_b_sq_iff _ _).mp hzmod
    have h5a : (5 : ℤ) ∣ a := (Int.coe_zmod_eq_zero_iff_dvd a 5).mp (by exact_mod_cast ha0)
    have h5b : (5 : ℤ) ∣ b := (Int.coe_zmod_eq_zero_iff_dvd b 5).mp (by exact_mod_cast hb0)
    obtain ⟨a', ha'⟩ := h5a; obtain ⟨b', hb'⟩ := h5b
    rw [ha', hb'] at heq
    -- (5a')² = 2(5b')² + 5c² ⇒ 25 a'² = 50 b'² + 5 c² ⇒ 5 a'² = 10 b'² + c².
    have hc2 : (5 : ℤ) ∣ c ^ 2 := ⟨a' ^ 2 - 2 * b' ^ 2, by linarith⟩
    have hprime5 : Prime (5 : ℤ) := by exact_mod_cast (Nat.prime_iff_prime_int.mp (by decide))
    have h5c : (5 : ℤ) ∣ c := hprime5.dvd_of_dvd_pow hc2
    obtain ⟨c', hc'⟩ := h5c; rw [hc'] at heq
    have heq' : a' ^ 2 = (2 : ℤ) * b' ^ 2 + 5 * c' ^ 2 := by linarith
    -- Descent on a.natAbs.
    rcases eq_or_ne a 0 with ha0_int | ha0_int
    · refine ⟨ha0_int, ?_, ?_⟩
      · rw [ha0_int] at heq; nlinarith [sq_nonneg b, sq_nonneg c]
      · rw [ha0_int] at heq; nlinarith [sq_nonneg b, sq_nonneg c]
    · have ha'_lt : a'.natAbs < a.natAbs := by
        rw [ha']; simp [Int.natAbs_mul]
        exact Nat.lt_mul_iff_one_lt_left
          (Int.natAbs_pos.mpr (fun heq0 => ha0_int (by rw [ha', heq0]; ring))) (by decide)
      obtain ⟨ha'_z, hb'_z, hc'_z⟩ := ih a'.natAbs (hn ▸ ha'_lt) a' b' c' rfl heq'
      exact ⟨ha' ▸ by simp [ha'_z], hb' ▸ by simp [hb'_z], hc' ▸ by simp [hc'_z]⟩
```

## 6. Combined diff estimate and risk audit

**Diff estimate**: replace `sorry` at three sites with the bodies in §3,
§4, §5. The introductory `intro a b c _heq` lines on each theorem are
absorbed into the `suffices`/`induction` chain, so the existing
`intro` line is replaced.

| Sorry | Replacing LOC | New body LOC | Δ |
|-------|---------------|--------------|---|
| `safe_A_holds` (line 88-90) | 3 | 32 | +29 |
| `safe_B_holds` (line 96-98) | 3 | 30 | +27 |
| `safe_C_holds` (line 104-106) | 3 | 28 | +25 |
| **Total** | 9 | 90 | +81 |

After S4 ACT the file lands at ~214 LOC (133 + 81), still well under
the 300 LOC threshold for single-file research deliveries. **Sorries
3 → 0; axioms 0 → 0.**

### Risk audit

1. **`Int.coe_zmod_eq_zero_iff_dvd` casting direction** — the helper at
   `Mathlib/Data/ZMod/Basic.lean` is stated as
   `(↑a : ZMod n) = 0 ↔ (n : ℤ) ∣ a` (with `Int` argument). For ZMod 5
   over ℤ-arguments this is the right direction; the `push_cast`
   handles the lift from `((a : ZMod 5))^2 + 2 ((b : ZMod 5))^2 = 0`
   to `(a^2 + 2*b^2 : ZMod 5) = 0`, then the iff produces
   `(5 : ℤ) ∣ a^2 + 2*b^2`. Verified at v4.26.0
   (`rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

2. **`Nat.lt_mul_iff_one_lt_left` direction** — produces `a < a * b`
   from `0 < a` and `1 < b`. In §3 the witness is `1 < 5` (decide-able)
   and `0 < c.natAbs` (from `c ≠ 0`). At v4.26.0 the lemma is at
   `Mathlib/Algebra/Order/Ring/Lemmas.lean`; one alternative is the
   `Nat.lt_mul_left` form, both v4.26.0-stable.

3. **`Nat.prime_iff_prime_int`** — at v4.26.0 this is at
   `Mathlib/Data/Nat/Prime/Basic.lean`. Alternatives:
   `(Nat.Prime 5).prime` then cast, or
   `Int.prime_iff_natAbs_prime.mpr (by decide : (5 : ℤ).natAbs.Prime)`.

4. **`nlinarith` discharge of `a² + 2b² = 0 ⇒ a = 0 ∧ b = 0`** —
   discharges via two non-negative squares summing to zero. Two
   alternatives if `nlinarith` ever drifts:
   `have ha2 : a^2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]; exact sq_eq_zero_iff.mp ha2`,
   or `omega` after `push_cast` (less reliable on integer squares).

5. **`Nat.strong_induction_on` syntax** — at v4.26.0 the canonical
   syntax is `induction n using Nat.strong_induction_on`. Alternative:
   `Nat.strongRecOn n (fun n ih => ...)` direct term mode. Both
   v4.26.0-stable; the `induction` syntax has cleaner goal state for
   debugging.

### Compatibility with PR #19028

The bodies above reference the two new ZMod 5 helpers by their full
names (`zmod_5_a_sq_plus_2_b_sq_eq_zero_iff`,
`zmod_5_a_sq_eq_two_b_sq_iff`) without namespace qualification. After
PR #19028 lands, both helpers live in the `Erdos659OQ01OQ02` namespace
(the same namespace as `safe_A_holds`), so unqualified resolution
works. No additional imports needed beyond what PR #19028 adds
(`import Mathlib.Data.ZMod.Basic` — already present after #19028).

## 7. S4 ACT integration plan (post-#19028 merge)

After PR #19028 merges to `origin/main`, a single S4 ACT PR can:

1. Replace `sorry` at lines 90, 98, 106 with the bodies in §3, §4, §5.
2. Update the in-file docstring at lines 39-43 to remove the "3
   strategic sorries" warning (now zero).
3. Add a brief `Honesty` block to the file header confirming
   `axiomCount = 0`, `sorryCount = 0`, build verified.
4. Run `./proofs/scripts/docker-build.sh Proofs.Erdos659OQ01OQ02`
   from the worktree directory (PR #19028 §Build Status notes the
   worktree-vs-main-repo path subtlety).
5. Update `state.md` Phase: `ACT` → `ACT` (unchanged), Iteration
   `9 → 10`, Last Update `2026-05-14 (researcher-X)`.
6. Update JSON `currentState.{focus,nextAction}` and
   `knowledge.progressSummary`.

**S4 ACT LOC budget (from PR #19028 §Next action)**: ~40-50 LOC.
**This PREP's refined estimate**: ~85-90 LOC (the PR #19028 §Next
action sketch did not show the descent variable threading or the
`c = 0` boundary case; both add ~10 LOC per equation).

The discrepancy is honest: this PREP transcribes the descent in full,
including the `Nat.strong_induction_on` setup, the boundary-case
split, and the IH application. The PR #19028 estimate counts the
core mod-5-and-divisibility lines only.

## 8. Honesty / scope guarantees

* **No Lean edits.** `proofs/Proofs/Erdos659OQ01OQ02.lean` unchanged.
* **No `problem.md` / `knowledge.md` / `state.md` edits.** This PREP
  only adds the present sessions/ file.
* **No `currentState.*` / `knowledge.progressSummary` JSON edits.**
* **No race with PR #19028.** PR #19028 modifies state.md, JSON, and
  the Lean file (helpers); this PR modifies only a new sessions/ file.
  Zero overlap.
* **No race with the next S4 ACT.** This PREP's content is design
  guidance for the eventual S4 ACT worker; the bodies herein are
  drafts that the ACT worker will adapt as Mathlib API responds in
  practice. The ACT worker owns the Lean diff exclusively.

## 9. Anti-targets (do NOT attempt now)

* ❌ **Do not write the Lean code now.** This is a PREP; the bodies in
  §3, §4, §5 are templates for an S4 ACT worker with full Docker
  access.
* ❌ **Do not edit `problem.md` / `knowledge.md` / `state.md`.**
  Landscape edits are for a future STATE-SYNC after #19028 and S4 ACT
  both merge.
* ❌ **Do not modify any prior session file.** Each prior PREP has its
  own context; this PREP-2 appends a new file dated 2026-05-14.
* ❌ **Do not attempt S4 ACT before #19028 merges.** The bodies above
  reference helpers that are not on `origin/main` yet.
