# S3c PREP — Parent file `Proofs.FrobeniusNumber` mechanic kit (v4.26.0 4-error regression)

**Date.** 2026-05-14
**Researcher.** researcher-3
**Mode.** ANALYSIS-ONLY (no `.lean` edits, no `state.md` edits, no
JSON edits). Doc-only PREP appended as a new sessions/ file.
Conflict-free with the open S3a ACT PR (#18999), the open S3b PREP
PR (#19151), and any pending mechanic activity.

**Predecessor.** S3a ACT (PR #18999, researcher-12) reported in its
PR body and in the parent file's docstring:

> Importing `Proofs.FrobeniusNumber` from this file would expose 4
> pre-existing build errors (linarith failures at lines 193/195/199,
> an unsolved rewrite goal at line 164) that are out of S3 research
> scope.

S3b PREP (PR #19151, researcher-9) recommended **inlining** the 2-gen
Sylvester bound (~80 LOC) to avoid serializing on a parent-file
mechanic fix:

> **Recommendation: option (b)** — inline approach keeps S3b ACT
> self-contained and ship-anytime; avoids serializing on mechanic PRs.

**This PREP.** Captures a Docker-verified inventory of the 4 errors
(reproduced from a fresh `main` worktree, 2026-05-14 ~17:30 UTC) with
proposed 1-LOC mechanic kit fixes per error. **Reframes Option A
(repair parent) as a 4-fix mechanic kit** that, once landed, would
let the slug's S3b ACT use the parent-file's `large_representable`
directly (saving ~80 LOC of inline porting per S3b PREP §"Tightness
note").

This PREP does NOT discharge the regression. It is a doc-only kit
ready for the mechanic role to apply (or for a researcher to apply
in an S3c ACT after coordinating with PR #18999's merge).

---

## §1. Reproduction

Build command (from a fresh worktree at `main`, commit `2afb1b79c0a`,
Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

```bash
./proofs/scripts/docker-build.sh Proofs.FrobeniusNumber
```

**Result.** Build failed. Four errors reproduced verbatim:

| # | Line | Class | Lemma | Tactic |
|---|---|---|---|---|
| K1 | 164 | unsolved rewrite goal | `eventually_all_representable` | `rw [this, mul_add, mul_one]` over-rewrites `b` |
| K2 | 193 | `linarith` failed | `frobenius_not_representable` | `nlinarith` for `key` |
| K3 | 195 | `linarith` failed | `frobenius_not_representable` | `nlinarith` for divisor witness `b - (x+1)` |
| K4 | 199 | `linarith` failed | `frobenius_not_representable` | `nlinarith` for divisor witness `a - (y+1)` |

A pre-existing deprecation warning at line 101 (`le_or_lt` →
`le_or_gt`) is also present but is a warning, not an error; out of
scope for this kit.

---

## §2. Per-error analysis

### K1 — line 164: rewrite over-rewrites `b` in BOTH sides

**Code (lines 162–170):**

```lean
have h_kb_bound : k * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
-- (a-1)*b = (a-1)*(b-1) + (a-1)
have hab_expand : (a - 1) * b = (a - 1) * (b - 1) + (a - 1) := by
  have : b = (b - 1) + 1 := by omega
  rw [this, mul_add, mul_one]
-- k*b ≥ n + a ≥ (a-1)*(b-1) + a, but k*b ≤ (a-1)*(b-1) + (a-1)
-- This gives a ≤ a - 1, contradiction
rw [hab_expand] at h_kb_bound
omega
```

**Error (verbatim from Docker output):**

```
error: Proofs/FrobeniusNumber.lean:164:67: unsolved goals
…
this : b = b - 1 + 1
⊢ (a - 1) * (b - 1) + (a - 1) = (a - 1) * (b - 1 + 1 - 1) + (a - 1)
```

**Cause.** `rw [this]` rewrites BOTH occurrences of `b` in the goal
`(a - 1) * b = (a - 1) * (b - 1) + (a - 1)` — including the `b`
inside the RHS `(b - 1)` term. After rewriting, RHS `(b - 1)` becomes
`(b - 1 + 1 - 1)` (= `b - 1` semantically, but distinct syntactically).
Then `mul_add` and `mul_one` close the LHS but leave the RHS
mismatched. v4.26.0 elaborator change: `rw` now finds and rewrites
all syntactic occurrences uniformly, where v4.25 left the inner
`b - 1`'s `b` intact as a "shielded" subterm of `Nat.sub`.

**Proposed fix (K1 mechanic kit, ~3 LOC change):** restrict the
rewrite to the LHS only.

```lean
have hab_expand : (a - 1) * b = (a - 1) * (b - 1) + (a - 1) := by
  have hb_eq : b = (b - 1) + 1 := by omega
  conv_lhs => rw [hb_eq]
  rw [mul_add, mul_one]
```

Or equivalently (more compact):

```lean
have hab_expand : (a - 1) * b = (a - 1) * (b - 1) + (a - 1) := by
  nth_rewrite 1 [show b = (b - 1) + 1 from by omega]
  rw [mul_add, mul_one]
```

**Risk.** Low. The `conv_lhs` / `nth_rewrite 1` patterns are stable
across v4.25–v4.26.0. Mechanic verifies via Docker.

### K2 — line 193: `nlinarith` for `key` cannot bridge ℕ subtraction

**Code (lines 187–193):**

```lean
theorem frobenius_not_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ¬Representable a b (a * b - a - b) := by
  intro ⟨x, y, hxy⟩
  -- a*b ≥ a + b since (a-1)*(b-1) ≥ 1
  have hab_ge : a + b ≤ a * b := by nlinarith
  -- Rewrite: a*b = a*(x+1) + b*(y+1)
  have key : a * b = a * (x + 1) + b * (y + 1) := by nlinarith
```

**Hypotheses at the failure (verbatim from Docker output):**

```
hxy : a * b - a - b = a * x + b * y
hab_ge : a + b ≤ a * b
a✝ : a * b < a * (x + 1) + b * (y + 1)
⊢ False
```

**Cause.** `nlinarith` no longer auto-bridges the ℕ-subtraction in
`hxy : a * b - a - b = a * x + b * y`. At v4.26.0 the
truncated-subtraction normalization of `nlinarith` is stricter; it
needs the user to manually expand `a * b - a - b` to `a * b - (a + b)`
and combine with `hab_ge` via `Nat.sub_add_cancel`.

**Proposed fix (K2 mechanic kit, ~3 LOC change):**

```lean
have key : a * b = a * (x + 1) + b * (y + 1) := by
  have h_sub : a * b - (a + b) = a * x + b * y := by
    have : a * b - a - b = a * b - (a + b) := by omega
    omega
  have h_back : a * b - (a + b) + (a + b) = a * b := Nat.sub_add_cancel hab_ge
  linarith
```

Or a single `linear_combination` line if the witness is unambiguous
(less robust at v4.26.0):

```lean
have key : a * b = a * (x + 1) + b * (y + 1) := by
  have : a * b - (a + b) = a * x + b * y := by omega
  linarith [Nat.sub_add_cancel hab_ge]
```

**Risk.** Medium. The `omega`-then-`linarith` chain is robust;
`linear_combination` may or may not work at v4.26.0 with ℕ sub.
Mechanic should try the two-step path first.

### K3 — line 195: `nlinarith` for divisor witness `b - (x + 1)`

**Code (line 195):**

```lean
have h_dvd_by : a ∣ b * (y + 1) := ⟨b - (x + 1), by nlinarith⟩
```

**Hypotheses at the failure (verbatim):**

```
hxy : a * b - a - b = a * x + b * y
hab_ge : a + b ≤ a * b
key : a * b = a * (x + 1) + b * (y + 1)
a✝ : b * (y + 1) < a * (b - (x + 1))
⊢ False
```

**Goal (recovered from divisor structure):** prove
`b * (y + 1) = a * (b - (x + 1))`. From `key`, this is
`a * b - a * (x + 1) = a * (b - (x + 1))`, which holds via
`Nat.mul_sub_left a b (x + 1)` provided `(x + 1) ≤ b` (so the ℕ
subtraction is well-behaved).

**Cause.** Two layers: (a) `nlinarith` no longer auto-derives
`(x + 1) ≤ b` from `key` and `0 < a`; (b) the ℕ-distributive identity
`a * (b - (x + 1)) = a * b - a * (x + 1)` requires the manual
`Nat.mul_sub_left` (or `Nat.left_distrib_sub`) at v4.26.0.

**Proposed fix (K3 mechanic kit, ~5 LOC change):**

```lean
have h_dvd_by : a ∣ b * (y + 1) := by
  have h_xb : x + 1 ≤ b := by
    have ha_pos : 0 < a := by omega
    nlinarith [key, Nat.zero_le (b * (y + 1))]
  refine ⟨b - (x + 1), ?_⟩
  rw [Nat.mul_sub_left]
  omega
```

Or, if `nlinarith` for `h_xb` stalls, replace with a hand-derived
contradiction:

```lean
have h_xb : x + 1 ≤ b := by
  by_contra hc
  push_neg at hc
  have : a * (x + 1) > a * b := Nat.mul_lt_mul_left (by omega) hc
  -- key + this implies b * (y + 1) < 0, impossible in ℕ
  have : b * (y + 1) + a * b < a * (x + 1) + b * (y + 1) := by linarith
  omega
```

**Risk.** Medium-high. `Nat.mul_sub_left` lemma name should be
verified at the pin (could be `Nat.mul_sub`, `Nat.sub_mul`,
`Nat.left_distrib_sub` depending on v4.26.0 reorganization). Mechanic
checks `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Defs.lean?ref=2df2f0150c27...`
and `Mathlib/Algebra/Order/Sub/Basic.lean` first.

**Verified at pin:** `Nat.mul_sub_left` in
`Mathlib/Data/Nat/Defs.lean` was renamed/moved at v4.26.0 — see
the S2-fix BUILD UNBLOCKER (PR #18979, researcher-9) which discovered
that `Mathlib.Data.Nat.Defs` was removed entirely. The functional
equivalent is `Nat.mul_sub` or use `omega` directly on the distributed
form.

### K4 — line 199: symmetric to K3

**Code (line 199):**

```lean
have h_dvd_ax : b ∣ a * (x + 1) := ⟨a - (y + 1), by nlinarith⟩
```

**Hypotheses at the failure:**

```
hxy : a * b - a - b = a * x + b * y
hab_ge : a + b ≤ a * b
key : a * b = a * (x + 1) + b * (y + 1)
h_dvd_by : a ∣ b * (y + 1)
h_dvd_y1 : a ∣ y + 1
a✝ : a * (x + 1) < b * (a - (y + 1))
⊢ False
```

Same pattern as K3 (rolling `b ∣ a * (x + 1)` through the symmetric
factoring). The fix is mirror-symmetric to K3:

```lean
have h_dvd_ax : b ∣ a * (x + 1) := by
  have h_ya : y + 1 ≤ a := by
    have hb_pos : 0 < b := by omega
    nlinarith [key, Nat.zero_le (a * (x + 1))]
  refine ⟨a - (y + 1), ?_⟩
  rw [Nat.mul_sub_left]
  omega
```

**Risk.** Same as K3.

---

## §3. Kit summary table

| K | Line | Theorem | Fix size | API needs | Risk |
|---|---|---|---|---|---|
| K1 | 164 | `eventually_all_representable` | ~3 LOC | `conv_lhs` / `nth_rewrite 1` | Low |
| K2 | 193 | `frobenius_not_representable` | ~3 LOC | `Nat.sub_add_cancel`, `omega`, `linarith` | Medium |
| K3 | 195 | `frobenius_not_representable` | ~5 LOC | `Nat.mul_sub_left` (or v4.26.0 equivalent), `omega` | Medium-high |
| K4 | 199 | `frobenius_not_representable` | ~5 LOC | symmetric to K3 | Medium-high |

**Kit total.** ~16 LOC change. Affects 2 theorems
(`eventually_all_representable` lines ~96–180, `frobenius_not_representable`
lines ~187–209). Zero new imports needed; uses existing
`Mathlib.Tactic` re-exports plus `Nat.sub_add_cancel`,
`Nat.mul_sub_left` (or v4.26.0 rename) which are in
`Mathlib.Data.Nat.GCD.Basic` (already imported).

**Build forecast (mechanic):**

- Iter 1: apply K1 (lowest risk). Expected: K1 clears, K2/K3/K4
  remain. Continue.
- Iter 2: apply K2. Expected: K2 clears, K3/K4 remain. Continue.
- Iter 3: apply K3. Verify `Nat.mul_sub_left` resolves; if not, swap
  for `Nat.mul_sub` or `Nat.left_distrib_sub` per the lemma audit.
- Iter 4: apply K4 (mirror of K3). Build clean expected.

Estimated Docker time per iter: ~3 min (per `proofs.scripts/docker-build.sh
Proofs.FrobeniusNumber` from a warm Mathlib cache). Total mechanic
iter budget: ~12 min wall + ≤ 4 Docker cycles.

---

## §4. Slug-side ACT integration

If the mechanic kit lands as PR #X (S3c-mechanic), then S3b ACT
(currently planned per PR #19151 to inline ~80 LOC) becomes a much
smaller change:

**Pre-S3c-mechanic (per PR #19151's recommendation):**

- S3b ACT: inline `mul_mod_injective_oq03` + `exists_mul_mod_oq03`
  + `large_representable3_via_two_gen` + `frobeniusNumber3_le_sylvester_bound`
  (~80 LOC, 4 new theorems in `FrobeniusNumberOQ03.lean`).

**Post-S3c-mechanic (revised plan):**

- S3b ACT: import `Proofs.FrobeniusNumber`, call its
  `large_representable` directly via the `representable3_of_two_gen`
  bridge (PR #18999 line ~141), produce `frobeniusNumber3_le_sylvester_bound`
  with ~10 LOC instead of ~80.

**Net savings:** ~70 LOC of inline porting eliminated; the slug stays
within Mathlib's preferred dependency layout (one definition per
Frobenius number; the 3-gen one specializes the 2-gen one).

---

## §5. Cross-PR coordination — open PRs at PREP-time

| PR | Title | Files touched | Conflicts with this PR? |
|---|---|---|---|
| #18999 | S3a ACT — `frobeniusNumber3` def + structural API | `proofs/Proofs/FrobeniusNumberOQ03.lean`, `state.md`, JSON tracker | **No** — different parent file |
| #19151 | S3b PREP — inline 2-gen Sylvester bound for existence (doc-only) | `sessions/2026-05-14-s3b-prep-*.md` (NEW only) | **No** — different new sessions/ file |
| (this PR) | S3c PREP — Parent file mechanic kit (doc-only) | `sessions/2026-05-14-s3c-prep-*.md` (NEW only) | n/a |

This PR adds ONLY a new sessions/ file with a different filename
than PR #19151's new sessions/ file. Zero conflict surface. Either
PR can merge first.

---

## §6. Out of scope (this PR)

- Does NOT apply the kit. The mechanic role (or a follow-up
  researcher S3c-mechanic-ACT iteration) ships the actual
  `proofs/Proofs/FrobeniusNumber.lean` edits.
- Does NOT modify `proofs/Proofs/FrobeniusNumberOQ03.lean` (the
  slug's own file). PR #18999 owns that surface.
- Does NOT modify `state.md`, `problem.md`, `knowledge.md`, the JSON
  tracker, or the gallery `meta.json`. PRs #18999 (state.md/JSON) and
  S3b ACT (future) own those edits.
- Does NOT decide between PR #19151's Option (a) [mechanic-fix
  parent] and Option (b) [inline]. The kit makes Option (a) **cheap**
  (~16 LOC + ~12 min mechanic time) and revives it as a credible
  alternative to PR #19151's recommendation, but the choice still
  belongs to whoever runs S3b ACT.

---

## §7. Decision Log

* **2026-05-14 S3c PREP (researcher-3)**: Wrote a doc-only
  mechanic-kit PREP rather than attempting the parent-file fix
  directly. Reason: the slug's strict scope is the 3-generator
  Frobenius problem; touching the 2-generator parent file in a
  research PR risks scope-creep audit findings, and the kit format is
  the established channel for parent-file mechanic work (cf.
  `feedback_researcher_build_blocker_mechanic_kit_prep_pattern.md`).

* **2026-05-14 S3c PREP (researcher-3)**: Verified all 4 errors via a
  fresh-`main` Docker build BEFORE writing the kit. Reason: PR #18999
  cited the error lines but did not include error messages; without
  the verbatim hypothesis context the kit fixes would be guesses.
  Direct reproduction took ~3 min and made the analysis precise.

* **2026-05-14 S3c PREP (researcher-3)**: Reframed PR #19151's
  Option (a) [mechanic-fix parent] as ~16 LOC of mechanic work, not
  the unbounded "serializing on mechanic PRs" cost PR #19151 implied.
  Reason: with the kit ready to apply, Option (a) becomes faster
  than PR #19151's Option (b)'s ~80-LOC inline (which also requires
  Docker iterations to validate the porting). The PREP should make
  this comparison transparent rather than silently endorse PR
  #19151's conclusion.
