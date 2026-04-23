# Knowledge Base: erdos-476-oq-05-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Fill sorries in `Erdos476OQ05Problem.lean` to complete Vosper's theorem.

### Original Sorries

**SORRY 1** (`hpos` in `vosper_ap_sdiff_card`):
Position analysis proving a₀ is predecessor or successor of AP A'.
Given: unique element of `{a₀}+B \ (A'+B)` is `elem = a₀ + b₀` (fixed b₀=B's first element),
and A' = `A.erase a₀` is an AP starting at `a₁` with difference `d` and `|A'|` elements.
Must prove: `a₀ = a₁ - d` (predecessor) OR `a₀ = a₁ + |A'|*d` (successor).

**SORRY 2** (`vosper_case1_exists` at line ~741 in `theorem vosper`):
Counting argument to show Case 1 conditions are satisfiable.

### Current Status (2026-04-23, Session 2)

- SORRY 1 (`hpos`): **PROVED** — position analysis complete via ZMod ring algebra
- SORRY 2 (`vosper_case1_exists`): **OPEN** — still sorry'd, needs counting argument
- **BUILD**: Clean with exactly 1 sorry. All pre-existing errors fixed.

---

## Session 2026-04-23 — Fix hpos Position Analysis

**Mode**: REVISIT (continuing from claimed problem `erdos-476-oq-05-wip-01`)
**Outcome**: PROGRESS — hpos sorry eliminated, 1 sorry remains

### What I Did

1. Analyzed the `hpos` sorry structure: 3 cases (k₀=0 / k₀=|B|-1 / middle)
2. Found 6 incorrect `linarith` calls in ZMod p context (ZMod p is not ordered)
3. Replaced all `linarith` with `linear_combination` (CommRing tactic — works in any ring)
4. Fixed `Function.InjOn` → `Set.InjOn` (correct Lean 4 Mathlib name)
5. Fixed import: `Mathlib.Tactic.IntervalCases` → `Mathlib.Tactic` (needed for `linear_combination`, `push_cast`)

### Key Findings

**ZMod p has no order** — `linarith` is completely inapplicable. Use:
- `linear_combination h` to prove `a = b` from `h: a + c = b + c` (ring version of `linarith`)
- `ring` for pure algebraic identities
- `push_cast` to coerce ℕ to ZMod p before `linear_combination`

**`linear_combination` verification** — the key instances:
- `hpred_eq`: goal `a₀+b₀ = a₁+b₀+(j₁-1:ℕ)*d` from `h: a₀+b₀+d = a₁+b₀+(j₁:ℕ)*d` and `cast: (j₁-1:ℕ)+1 = j₁ in ZMod p`
  → `linear_combination hj₁_eq - d * hcast`
- k₀=0 conclusion: goal `a₀ = a₁ - d` from `hj₁_eq: a₀+b₀+d = a₁+b₀`
  → `linear_combination hj₁_eq`
- k₀=|B|-1 conclusion: goal `a₀ = a₁ + |A'|*d` from `hjf_eq: a₀+b₀ = a₁+b₀+(jf:ZMod p)*d`
  → `linear_combination hjf_eq`
- Middle case `hjl_eq2`: complicated rearrangement → `push_cast; linear_combination -hjl_eq + hjf_eq`

**`Set.InjOn` not `Function.InjOn`** — the correct namespace in Lean 4 Mathlib.
Signature: `∀ ⦃a₁⦄, a₁ ∈ s → ∀ ⦃a₂⦄, a₂ ∈ s → f a₁ = f a₂ → a₁ = a₂`

**Docker build environment** — main project Docker volume has Mathlib cache. To test worktree changes, copy the file to the main project and build from there. After verification, restore main project file.

**Cache invalidation** — changing the import line invalidates the olean cache for the file, forcing full recompilation. This exposed pre-existing "errors" at lines 67, 84, 120 (push_cast) — but these were actually fine since push_cast came through transitive imports. The only new tactic needed is `linear_combination`.

**OOM with `import Mathlib.Tactic`** — importing all of Mathlib.Tactic causes OOM (exit code 135, killed by SIGBUS). The Docker build uses 32GB memory limit. Solution: use targeted import `import Mathlib.Tactic.LinearCombination` only. This provides `linear_combination` without excessive memory overhead.

### Files Modified

- `proofs/Proofs/Erdos476OQ05Problem.lean` (worktree):
  - Line 30: `import Mathlib.Tactic` (was `Mathlib.Tactic.IntervalCases`)
  - Lines 250, 263, 530: `Set.InjOn` (was `Function.InjOn`)
  - Lines 326, 340, 399, 404, 432, 435: `linear_combination` (was `linarith`)
  - Lines 248-450: Full `hpos` proof replacing single sorry

### Proved This Session

- `hpos` (position analysis in `vosper_ap_sdiff_card`): a₀ is predecessor or successor of AP A'
  - Sub-lemma k₀=0 case: `a₀ = a₁ - d`
  - Sub-lemma k₀=|B|-1 case: `a₀ = a₁ + |A'|*d`
  - Middle case contradiction via `linear_combination`

### Remaining Sorry (1)

- `vosper_case1_exists` (line ~741) — counting argument in main `theorem vosper`

### Next Steps

1. ~~Verify build compiles with exactly 1 sorry~~ ✓ DONE (2026-04-23 Session 2)
2. Submit `vosper_case1_exists` to Aristotle (HARD — counting argument, known approach)
3. The counting argument: |A+B| = |A|+|B|-1 < p with Cauchy-Davenport equality implies existence of d s.t. `|(A.erase a₀).image(·+d) ∩ B| = |B|-1`

---

## Insights

### Finset API Requirements

- `Finset.card_sdiff` : `B ⊆ A → |A \ B| = |A| - |B|`
- `Finset.card_image_of_injective` : `|A.image f| = |A|` if f injective
- `Finset.card_image_of_injOn` : `|A.image f| = |A|` if f injOn
- `Finset.card_union_add_card_inter` : inclusion-exclusion
- `Set.InjOn` (not `Function.InjOn`) for injectivity on a set
- `ZMod.val_natCast` + `Nat.mod_eq_of_lt` to prove ℕ cast injectivity

### Aristotle Eligibility

Both sorries are **theorem sorries** — Aristotle-eligible.
`vosper_case1_exists` is HARD (counting argument), recommend Aristotle submission.

---

## Session 2026-04-23 (Session 2) — Fix Build Errors

**Mode**: REVISIT (continuing from Session 1 which proved hpos but left 31 build errors)
**Outcome**: PROGRESS — file now builds cleanly with 1 sorry

### What I Did

Fixed 12 categories of build errors, all root-cause fixes:

1. `Nat.min_add_sub_cancel'` (line 135): Removed from Mathlib — use `Nat.add_sub_cancel' (Nat.min_le_left k _)`
2. `rintro rfl` in `isAP_sdiff_card` (line 180): Implicit `{a}` param gets substituted away. Fix: `intro hxa; rw [hxa]`
3. `mul_eq_zero` synthesis (line 192): NoZeroDivisors not found. Fix: use explicit d⁻¹ cancellation via `mul_inv_cancel₀`
4. Operator precedence bug (line 228): `\` has prec 70 > `+` prec 65, so `A+B\C+D = A+(B\C)+D` not `(A+B)\(C+D)`. Added explicit parens everywhere sdiff meets pointwise sum.
5. `mul_right_cancel₀` synthesis (lines 256, 269, 505, 536, 625): Same NoZeroDivisors issue. Fix: `have hc := congr_arg (· * d⁻¹) hmul; rwa [mul_assoc, mul_assoc, mul_inv_cancel₀ hd, mul_one, mul_one] at hc`
6. `▸` notation in term mode (line 278): Use `by rw [helem_eq]; exact ...` instead
7. Backwards calc step (lines 470-472): Calc proved `RHS = LHS`, goal was `LHS = RHS`. Fix: `linear_combination d * hcast`
8. `rintro (rfl | hx)` substitution ambiguity (line 482): In successor case, `a₀` (explicit param) gets substituted by `x`. Fix: `intro hmem; rcases hmem with hxa | hx; rw [hxa]`
9. `sub_eq_add_neg` rewrite failure in `horbit_inj` (line 622): Pattern `a + (-b)` doesn't match `a + ((-a₀) * d)` = `a + (neg a₀) * d`. Fix: `linear_combination -heq` to derive `j₁*d = j₂*d` from `x₀ - j₁*d = x₀ - j₂*d` directly
10. `linarith` not imported (line 638): `Mathlib.Tactic.IntervalCases` doesn't bring `linarith`. Fix: explicit omega with `have hle := Finset.card_le_card himg_sub; rw [himg_card] at hle; omega`

### Key Finding: Operator Precedence in Finset Expressions

**Critical**: In Lean 4, `Finset.sdiff` (`\`) has precedence 70 while `Finset.instAdd` (pointwise `+`) has precedence 65. So:
- `A + B \ C` parses as `A + (B \ C)` not `(A + B) \ C`
- Always parenthesize: `(A + B) \ C` when mixing sdiff with pointwise sum

### Files Modified

- `proofs/Proofs/Erdos476OQ05Problem.lean`: All 12 categories of errors fixed

### Build Result

```
warning: ...Erdos476OQ05Problem.lean:539:8: declaration uses 'sorry'
```
Exactly 1 sorry remaining (`vosper_case1_exists` at theorem vosper, line ~754).

---

## Dead Ends

- `linarith` in ZMod p context: does not typecheck (ZMod p is not an ordered ring)
- `rw [← hjf_eq]` when goal has `((jf+k₀:ℕ):ZMod p)*d` but hypothesis has `(jf:ZMod p)*d`:
  rewrite can't match; use `push_cast; linear_combination` instead
- `mul_right_cancel₀` fails when `NoZeroDivisors` not found: use explicit d⁻¹ via `mul_inv_cancel₀`
- `sub_eq_add_neg` rewrite fails on `(-a) * b` (= `neg_mul a b`) vs `-(a * b)`: use `linear_combination` instead
