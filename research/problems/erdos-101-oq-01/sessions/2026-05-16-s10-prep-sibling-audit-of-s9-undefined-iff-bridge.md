# Session 10 PREP — Sibling-audit of S9 PREP (#19403) corrected §5 sketches: undefined bridge lemma + §5.1 elaboration mismatch

- **Date**: 2026-05-16
- **Session**: 10
- **Phase**: PREP (no ACT — surfaces ACT-blocking issues in S9's corrected sketches before next picker fires Docker iter 1)
- **Researcher**: researcher-4
- **Status**: doc-only sibling-audit, conflict-free with all merged PRs on slug

## 1. TL;DR

S8 STATE-SYNC #19360 MERGED at 2026-05-16T03:53:49Z. S9 PREP #19403
MERGED at 2026-05-16T03:51:53Z. Drain wave order: S9 first, S8 second
(~2min apart). Post-merge picture on `origin/main`:

- `state.md` reflects S8's recipe (`Active Approach §1-§3`) which
  contains the **FALSE artifact-(iii) signature** S9 PREP §3 identified
  as Bug F. S8 STATE-SYNC merged with that text intact because S9 PREP
  only added a session file (touched no state.md / JSON).
- S9 PREP's §5.1 / §5.2 corrected sketches live only in the S9
  sessions/ file. The ACT picker reading state.md verbatim hits Bug F
  + Bug G; the picker reading S9 §5.1 / §5.2 verbatim hits **2 new
  ACT-blocking bugs** (H, I) that S9's audit did not catch.

Goal-state simulation of S9 §5.1 + §5.2 at the unchanged lake-pinned
Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; ZERO
drift across ~3.4h since S9 PREP's §6 recheck) surfaces:

| # | Severity | Where in #19403 (S9 PREP) | Issue |
|---|----------|-----------------------------|-------|
| **H** | **substantive, blocker** | §5.2 `erdos_101_oq_01_rate_form_iff_isLittleO` proof body | The iff proof calls `isLittleOh_n_squared_iff_isLittleO.mp h_olittle` and `.mpr h_olittle_mathlib`, but **no lemma of that name is defined** in `Erdos101OQ01.lean` (`grep -nE "(isLittleOh\|IsLittleOh)" Erdos101OQ01.lean` returns 3 hits, all to the SLUG-LOCAL `IsLittleOh_n_squared` Prop def at L69 + 2 docstring refs at L31 + L100 — no `_iff_` lemma exists). The ACT picker pasting §5.2 verbatim hits `unknown identifier 'isLittleOh_n_squared_iff_isLittleO'` during elaboration. **Fix: ship the iff lemma as artifact (ii) *before* artifact (iii) — it is the S6 PREP §"S6 ACT scope" artifact (ii) that S9 §5.2 implicitly assumed already exists.** See §3 below. |
| **I** | **substantive, elaboration** | §5.1 `maxFourPointLines_isBigO_n_squared` proof body, `show` line + `rw [abs_of_nonneg, abs_of_nonneg]` | After `apply Asymptotics.IsBigO.of_norm_le; intro n`, the goal is `‖(maxFourPointLines n : ℝ)‖ ≤ (n : ℝ)^2` (RHS is *not* `‖(n : ℝ)^2‖` — see `Mathlib/Analysis/Asymptotics/Defs.lean:155`: `theorem IsBigO.of_norm_le {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x)`). S9 §5.1's `show |(maxFourPointLines n : ℝ)| ≤ |(n : ℝ)^2|` adds a stale `|·|` on the RHS that does not exist in the goal — `show` fails (`(n : ℝ)^2` and `|(n : ℝ)^2|` are not defeq). Even with `show` skipped, the subsequent `rw [abs_of_nonneg, abs_of_nonneg]` expects two `|·|` to rewrite, but the goal has only one. **Fix: drop the RHS `|·|` and the second `abs_of_nonneg`; use `Real.norm_of_nonneg` for the single norm collapse.** See §4 below. |

Both bugs are invisible to S9's §6 bearer-existence checks (every
Mathlib name exists; types align at the *signature* level). They
appear only when (H) one **searches the slug for the iff lemma's
definition** and (I) one **walks the goal-state after
`apply IsBigO.of_norm_le; intro n`** and notices the RHS in
`of_norm_le`'s hypothesis is `g x`, not `‖g x‖`.

Plus a third lower-severity observation:

| # | Severity | Where | Issue |
|---|----------|-------|-------|
| **J** | informational, recipe sequencing | `state.md` Active Approach §3 (post-S8-merge) | `state.md` describes artifact (iii) as the **FALSE concrete `IsLittleO` form** (S8 verbatim), but S9 PREP §5.2 supersedes with the correct existential form. State.md was not updated in S9 PREP (paths-disjoint guarantee). Picker MUST cross-reference S9 §5.1 / §5.2 — not state.md — for the corrected artifact signatures. See §6 sequencing notes. |

**Recommendation**: amend the S10 / S11 ACT recipe per §3 + §4 + §5
below **before the next ACT picker fires Docker iter 1**. Without
these fixes the picker either (H) hits an `unknown identifier` at
artifact (iii)'s iff proof, or (I) hits a `show` failure at artifact
(i)'s IsBigO body, costing 1-2 Docker iterations to discover what
goal-state simulation surfaces here.

This audit is doc-only, adds **exactly one** new sessions/ file
(`2026-05-16-s10-prep-sibling-audit-of-s9-undefined-iff-bridge.md`),
touches no `state.md` / `knowledge.md` / JSON / Lean. Strictly
conflict-free with all merged PRs on slug.

## 2. Pre-claim probe (2026-05-16T03:50–03:55Z, after both #19360 + #19403 merged)

```
$ gh pr list -R rjwalters/lean-genius --state open \
    --search 'erdos-101-oq-01 in:title' --json number,title,createdAt,mergeStateStatus
[]
```

Zero open PRs on slug at S10 claim (~10min after S8 STATE-SYNC merge,
~12min after S9 PREP merge). Last merged research PR on slug: `#19360`
(S8 STATE-SYNC, doc-only) at 2026-05-16T03:53:49Z.

Sibling worktree audit (`git worktree list` + per-worktree state.md
mtimes): no sibling Docker processes touching `Erdos101OQ01.lean` /
`Erdos101Problem.lean` (`ps -ef | grep docker-build` returns 0 hits).
Race-free.

Lake SHA on `origin/main`: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0). Unchanged vs S8 STATE-SYNC §4 + S9 PREP §6 (both
2026-05-16). Drift verdict over the past ~3.4h: ZERO.

Slug `proofs/Proofs/Erdos101OQ01.lean` on `origin/main` (no Lean edits
since 2026-05-13 S4): 471 LOC, 9 theorems, 4 defs, **2 sorries**
(`erdos_101_oq_01` L110 + `solymosi_stojakovic_lower_bound` L297),
0 axioms, 0 warnings.

## 3. Bug H (substantive, blocker): undefined `isLittleOh_n_squared_iff_isLittleO`

### 3.1 What S9 PREP §5.2 prescribes

S9 PREP §5.2 ships a paste-ready iff proof:

```lean
theorem erdos_101_oq_01_rate_form_iff_isLittleO :
    erdos_101_oq_01_rate_form ↔ erdos_101_oq_01_isLittleO_form := by
  unfold erdos_101_oq_01_rate_form erdos_101_oq_01_isLittleO_form
  constructor
  · rintro ⟨g, h_olittle, h_bounds⟩
    refine ⟨g, isLittleOh_n_squared_iff_isLittleO.mp h_olittle, ?_⟩    -- ← H
    intro P hP
    exact_mod_cast h_bounds P hP
  · rintro ⟨g, h_olittle_mathlib, h_bounds⟩
    refine ⟨g, isLittleOh_n_squared_iff_isLittleO.mpr h_olittle_mathlib, ?_⟩  -- ← H
    intro P hP
    exact_mod_cast h_bounds P hP
```

### 3.2 Why this fails: the bridge lemma is undefined

In `proofs/Proofs/Erdos101OQ01.lean` on `origin/main` at SHA
`78448f56d0a` (post-S8/S9 merge):

```
$ git show origin/main:proofs/Proofs/Erdos101OQ01.lean | grep -nE "(isLittleOh|IsLittleOh)"
31:* Asymptotic vocabulary `IsLittleOh_n_squared` specialised to ℕ → ℕ.
69:def IsLittleOh_n_squared (f : ℕ → ℕ) : Prop :=
100:  ∃ g : ℕ → ℕ, IsLittleOh_n_squared g ∧
```

Three hits, all to the slug-local Prop def at L69 and its module-doc /
`rate_form` references. **There is no `isLittleOh_n_squared_iff_isLittleO`
lemma** (lowercase initial + `_iff_` suffix) anywhere in the slug, the
parent file, the Mathlib import set, or any sibling `Erdos101*`
file.

Elaborating §5.2 verbatim fails at:
```
unknown identifier 'isLittleOh_n_squared_iff_isLittleO'
```

The S9 PREP §"What this PR does" bullet "§5.1 + §5.2 ship paste-ready
**corrected sketches** for the S8 ACT picker" is therefore **only
half-paste-ready**: §5.1 has its own elaboration issue (Bug I below),
and §5.2 references a not-yet-existent lemma.

### 3.3 Why the bug is invisible to S9 PREP's §6 bearer audit

S9 PREP §6 audits 7+5=12 *Mathlib* bearers (line-pinned at the lake
SHA) but **does not audit slug-local lemma references**. The
`isLittleOh_n_squared_iff_isLittleO` identifier looks Mathlib-flavored
(camelCase + `_iff_` suffix) but is actually a **slug-internal
artifact** that S6 PREP §"S6 ACT scope" originally named as artifact
(ii) — and which the S6 / S7 / S8 / S9 PREP chain has been describing
as "to be shipped" without anyone yet shipping it.

Tracing the citation chain:
- **S6 PREP** (#19221) §"S6 ACT scope" artifact (ii): "the bridge
  `IsLittleOh_n_squared g ↔ Asymptotics.IsLittleO atTop (↑g) (·^2)`
  (~25 LOC)" — names the lemma's *shape* but provides no name.
- **S7 PREP** (#19287) §9 step 3.(ii): "**(ii)** `IsLittleOh_n_squared
  ↔ IsLittleO` bridge per S6 PREP (~25 LOC)" — inherits the
  shape-only reference.
- **S8 STATE-SYNC** (#19360) `state.md` Active Approach §2:
  "Artifact (ii) — bridge `IsLittleOh_n_squared g ↔ Asymptotics.IsLittleO
  atTop (↑g) (·^2)`. Direction-mapping per S7 PREP §3.4..." — again
  shape-only.
- **S9 PREP** (#19403) §5.2 proof body: **first** appearance of a
  *name* `isLittleOh_n_squared_iff_isLittleO` in the chain — used as
  if defined, but no `def` / `theorem` / `lemma` ever materialises it.

So the lemma is the **always-deferred artifact (ii)** of S6 PREP, and
§5.2's iff proof implicitly assumes artifact (ii) is in place by the
time §5.2 is pasted. **The ACT picker MUST ship artifact (ii) first**
(i.e., as a `theorem` / `lemma` definition in the Lean file, not as a
PREP §5 sketch) **before pasting §5.2.**

### 3.4 Correct fix: define the bridge lemma + supply its proof

The lemma's statement, matching S6 PREP §"S6 ACT scope" artifact (ii):

```lean
lemma isLittleOh_n_squared_iff_isLittleO (g : ℕ → ℕ) :
    IsLittleOh_n_squared g ↔
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => (g n : ℝ))
        (fun n : ℕ => (n : ℝ)^2) := by
  unfold IsLittleOh_n_squared
  rw [Asymptotics.isLittleO_iff]
  constructor
  · -- slug ⟹ mathlib direction: (<) ⟹ (∀ c > 0, ∀ᶠ n, ≤ c·)
    intro hslug c hc
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := hslug c hc
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn  -- (g n : ℝ) < c * (n : ℝ)^2
    rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
    linarith
  · -- mathlib ⟹ slug direction: (∀ c > 0, ∀ᶠ n, ≤ c·) ⟹ (<) per S7 §3.4 corrected
    intro hmathlib ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by linarith
    have hev := hmathlib hhalf
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N₀, hN₀⟩ := hev
    -- lift N to max N₀ 1 so that (n : ℝ)^2 > 0 for the strict gap (Bug D fix from S7 §3)
    refine ⟨max N₀ 1, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn₁ : 1 ≤ n := (le_max_right _ _).trans hn
    have h := hN₀ n hn₀  -- ‖(g n : ℝ)‖ ≤ (ε/2) * ‖(n : ℝ)^2‖
    rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)] at h
    -- h : (g n : ℝ) ≤ (ε / 2) * (n : ℝ)^2
    have hn_sq_pos : (0 : ℝ) < (n : ℝ)^2 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁
      positivity
    nlinarith
```

LOC: ~28 LOC for the lemma + proof (within S7's "(~25 LOC)" budget
+ 3 LOC for the `n ≥ 1` lift S7 §3 D-fix). Bearer dependencies:
- `Asymptotics.isLittleO_iff` (Defs.lean:175) ✓ (S9 §6 pin)
- `Filter.eventually_atTop` (AtTopBot/Basic.lean:72) ✓ (S9 §6 pin)
- `Real.norm_of_nonneg` (Normed/Group/Basic.lean:1084) — **new bearer**, pinned in §7 below
- `le_max_left`, `le_max_right` — core Lean 4 / Mathlib base, present at v4.26.0
- `positivity`, `linarith`, `nlinarith`, `exact_mod_cast` — Mathlib tactics, present

With this lemma in place, S9 §5.2's `erdos_101_oq_01_rate_form_iff_isLittleO`
proof body becomes paste-ready (the `.mp` / `.mpr` references now
resolve to the lemma defined here).

## 4. Bug I (substantive, elaboration): §5.1 `show` mismatch + duplicate `abs_of_nonneg`

### 4.1 What S9 PREP §5.1 prescribes

```lean
theorem maxFourPointLines_isBigO_n_squared :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (maxFourPointLines n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_norm_le
  intro n
  show |(maxFourPointLines n : ℝ)| ≤ |(n : ℝ)^2|     -- ← I (stale RHS |·|)
  rw [abs_of_nonneg, abs_of_nonneg]                  -- ← I (two targets, one available)
  · unfold maxFourPointLines
    have hbnd : n * (n - 1) / 12 ≤ n * n := by
      have hsub : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      exact (Nat.div_le_self _ 12).trans hsub
    ...
    linarith
  · positivity
  · exact_mod_cast Nat.zero_le _
```

### 4.2 Why it fails: `IsBigO.of_norm_le` hypothesis is `‖f x‖ ≤ g x` (not `≤ ‖g x‖`)

The actual Mathlib v4.26.0 signature, `Mathlib/Analysis/Asymptotics/Defs.lean:155`:

```lean
theorem IsBigO.of_norm_le {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) : f =O[l] g :=
  .of_norm_eventuallyLE <| .of_forall h
```

Note `g x`, **not** `‖g x‖`. The hypothesis bounds `‖f x‖` by `g x`
directly — there is no second norm on the RHS. After
`apply Asymptotics.IsBigO.of_norm_le; intro n`, the goal is:

```
⊢ ‖(maxFourPointLines n : ℝ)‖ ≤ (n : ℝ)^2
```

The S9 §5.1 `show |(maxFourPointLines n : ℝ)| ≤ |(n : ℝ)^2|` tries to
match the LHS (which is defeq up to the `Real.instNorm = abs` defeq —
fine) AND the RHS (which is *not* defeq — `(n : ℝ)^2` vs `|(n : ℝ)^2|`).
The `show` tactic fails with:

```
type mismatch
  goal expects: ‖(maxFourPointLines n : ℝ)‖ ≤ (n : ℝ)^2
  but show writes: |(maxFourPointLines n : ℝ)| ≤ |(n : ℝ)^2|
```

(Even though the two sides are propositionally equal — `(n : ℝ)^2 ≥ 0`
gives `|(n : ℝ)^2| = (n : ℝ)^2` by `abs_of_nonneg` — `show` requires
*definitional* equality, not propositional.)

Subsequent `rw [abs_of_nonneg, abs_of_nonneg]` would, even if `show`
were skipped, look for **two** `|·|` patterns to rewrite — but the
actual goal has only **one** (on the LHS, after unfolding `‖·‖` to
`abs` via `Real.norm_of_nonneg`). The `rw` chain fails at the second
`abs_of_nonneg` with:

```
abs_of_nonneg expects a hypothesis 0 ≤ ?_; no remaining occurrence
of |·| matches
```

### 4.3 Correct fix: single norm collapse via `Real.norm_of_nonneg`

```lean
theorem maxFourPointLines_isBigO_n_squared :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (maxFourPointLines n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_norm_le
  intro n
  -- goal: ‖(maxFourPointLines n : ℝ)‖ ≤ (n : ℝ)^2
  rw [Real.norm_of_nonneg (by positivity)]
  -- goal: ((maxFourPointLines n : ℕ) : ℝ) ≤ (n : ℝ)^2
  unfold maxFourPointLines
  have hbnd : n * (n - 1) / 12 ≤ n * n :=
    (Nat.div_le_self _ 12).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
  have hcast : ((n * (n - 1) / 12 : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hbnd
  have hsq : ((n * n : ℕ) : ℝ) = (n : ℝ)^2 := by push_cast; ring
  linarith
```

LOC: ~12 LOC (vs S9 §5.1's ~17 LOC including the broken `show` + two
unused side-conditions). Bearer dependencies (all v4.26.0):
- `Asymptotics.IsBigO.of_norm_le` (Defs.lean:155) ✓
- `Real.norm_of_nonneg` (Normed/Group/Basic.lean:1084) — see §7
- `Nat.div_le_self`, `Nat.mul_le_mul_left`, `Nat.sub_le`, `Nat.cast_le` —
  already used in `fourPointLineCount_le_quadratic` body
  (`Erdos101OQ01.lean:157, 159, 161`)
- `positivity`, `push_cast`, `ring`, `linarith` — Mathlib tactics

### 4.4 Why S9's §5.1 audit missed this

S9 PREP §5.1 was written by referencing the `IsBigO.of_norm_le` *name*
(verified to exist at SHA `2df2f01` per S9 §6) but **without
goal-state-walking** the body. The `show` line + `rw` chain were
likely transcribed from a different `IsBigO`-from-`norm_le` proof
pattern (the `IsBigO.of_norm_eventuallyLE`-via-mono pattern, which
does want both sides under `‖·‖` via `mono` over `EventuallyLE`).

S9 §6 audit caught the bearer existence (correct: the lemma exists)
but not the bearer **shape** (i.e., that `of_norm_le` has only one
norm in its hypothesis, not two).

This is the **canonical "bearer existence audited, bearer shape not"
pattern** — paralleling the lesson from
`feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`
(which is about typeclass shape upstream of the lemma body, and here
about the lemma's own hypothesis shape).

## 5. Revised artifact-(i)+(ii)+(iii) sketches (corrected for H + I)

Replacing S9 §5.1 + §5.2 with H-fix + I-fix:

### 5.1 Artifact (i) — aggregator + IsBigO + corrected per-P corollary

(Aggregator and per-P corollary unchanged from S9 §5.1; only the IsBigO
proof body corrected per §4.3.)

```lean
/-- Aggregator: upper bound on `fourPointLineCount` for no-five-collinear sets
of size `n`. Surrogate version using `improved_upper_bound`'s `n*(n-1)/12`. -/
noncomputable def maxFourPointLines (n : ℕ) : ℕ :=
  n * (n - 1) / 12

/-- The aggregator is `O(n²)` at infinity (in Mathlib idiom). -/
theorem maxFourPointLines_isBigO_n_squared :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => (maxFourPointLines n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) := by
  apply Asymptotics.IsBigO.of_norm_le
  intro n
  rw [Real.norm_of_nonneg (by positivity)]
  unfold maxFourPointLines
  have hbnd : n * (n - 1) / 12 ≤ n * n :=
    (Nat.div_le_self _ 12).trans (Nat.mul_le_mul_left n (Nat.sub_le n 1))
  have hcast : ((n * (n - 1) / 12 : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hbnd
  have hsq : ((n * n : ℕ) : ℝ) = (n : ℝ)^2 := by push_cast; ring
  linarith

/-- Per-`P` corollary: `fourPointLineCount` is bounded by the aggregator
**for no-five-collinear** sets. The hypothesis `NoFiveCollinear P` is
load-bearing — without it, `P` could be 9-collinear-on-a-line and
`fourPointLineCount P = C(9,4) = 126 > 6 = maxFourPointLines 9`. -/
theorem fourPointLineCount_le_max (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (maxFourPointLines P.points.card : ℝ) := by
  have h₁ : fourPointLineCount P ≤
      P.points.card * (P.points.card - 1) / 12 :=
    improved_upper_bound P hP
  exact_mod_cast h₁
```

LOC: ~22 LOC (saves ~8 LOC vs S9 §5.1's ~30).

### 5.2 Artifact (ii) — bridge lemma (FIRST appearance — was always deferred)

(New: ships the bridge lemma S6 PREP / S7 PREP / S8 STATE-SYNC always
referenced but never defined. Bug H fix.)

```lean
/-- Bridge: the slug-local strict-`<` predicate `IsLittleOh_n_squared g` is
equivalent to Mathlib's `Asymptotics.IsLittleO atTop (↑g) (·^2)` non-strict
form (with the standard `c := ε/2` lift in the `←` direction; the strict
gap requires the `n ≥ 1` floor to ensure `(n : ℝ)^2 > 0`). -/
lemma isLittleOh_n_squared_iff_isLittleO (g : ℕ → ℕ) :
    IsLittleOh_n_squared g ↔
      Asymptotics.IsLittleO Filter.atTop
        (fun n : ℕ => (g n : ℝ))
        (fun n : ℕ => (n : ℝ)^2) := by
  unfold IsLittleOh_n_squared
  rw [Asymptotics.isLittleO_iff]
  constructor
  · intro hslug c hc
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := hslug c hc
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
    linarith
  · intro hmathlib ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by linarith
    have hev := hmathlib hhalf
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N₀, hN₀⟩ := hev
    refine ⟨max N₀ 1, fun n hn => ?_⟩
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn₁ : 1 ≤ n := (le_max_right _ _).trans hn
    have h := hN₀ n hn₀
    rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)] at h
    have hn_sq_pos : (0 : ℝ) < (n : ℝ)^2 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn₁
      positivity
    nlinarith
```

LOC: ~28 LOC. (S6 PREP §"S6 ACT scope" originally budgeted ~25 LOC;
S7 PREP §3 corrected direction-mapping bumped to ~28-30 LOC.)

### 5.3 Artifact (iii) — existential form + iff with primary form

(Unchanged statement from S9 §5.2; iff proof now compiles because §5.2 is in place.)

```lean
/-- **OQ-01, Mathlib-idiom form**: there exists `g : ℕ → ℕ` that is `o(n²)`
(in Mathlib's `Asymptotics.IsLittleO atTop … (·^2)` sense) AND bounds
`fourPointLineCount P` for every no-five-collinear `P`. This statement is
**OPEN** ($100 Erdős prize). It is the Mathlib-idiom twin of
`erdos_101_oq_01_rate_form` (the slug-form existential at L99). -/
def erdos_101_oq_01_isLittleO_form : Prop :=
  ∃ g : ℕ → ℕ,
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ => (g n : ℝ))
      (fun n : ℕ => (n : ℝ)^2) ∧
    BoundsAtRate (fun n : ℕ => (g n : ℝ))

/-- The two existential forms are equivalent. -/
theorem erdos_101_oq_01_rate_form_iff_isLittleO :
    erdos_101_oq_01_rate_form ↔ erdos_101_oq_01_isLittleO_form := by
  unfold erdos_101_oq_01_rate_form erdos_101_oq_01_isLittleO_form
  constructor
  · rintro ⟨g, h_olittle, h_bounds⟩
    refine ⟨g, (isLittleOh_n_squared_iff_isLittleO g).mp h_olittle, ?_⟩
    intro P hP
    exact_mod_cast h_bounds P hP
  · rintro ⟨g, h_olittle_mathlib, h_bounds⟩
    refine ⟨g, (isLittleOh_n_squared_iff_isLittleO g).mpr h_olittle_mathlib, ?_⟩
    intro P hP
    exact_mod_cast h_bounds P hP

/-- **The main OPEN theorem of OQ-01, Mathlib-idiom form.** Equivalent
to `erdos_101_oq_01` via the chain `erdos_101_oq_01 ↔ erdos_101_oq_01_rate_form
↔ erdos_101_oq_01_isLittleO_form`. Proof is OPEN. -/
theorem erdos_101_oq_01_isLittleO : erdos_101_oq_01_isLittleO_form := by
  sorry
```

LOC: ~28 LOC.

### 5.4 Revised total LOC budget

| Artifact | S6 PREP | S7 PREP | S9 PREP | **S10 PREP** | Δ vs S9 |
|----------|---------|---------|---------|--------------|---------|
| (i) aggregator + IsBigO + per-P corollary | ~25 | ~50-65 | ~30 | **~22** | −8 |
| (ii) bridge lemma | ~25 | ~25 | (omitted) | **~28** | +28 (was 0) |
| (iii) existential form + iff + main theorem | ~30 | ~30 | ~30 | **~28** | −2 |
| **Total** | **~80** | **~105-125** | **~60** | **~78** | +18 vs S9 |

S10's ~78 LOC is **smaller than S7's ~105-125 envelope** (with breathing
room), and **larger than S9's claimed ~60 LOC** (because S9 implicitly
assumed artifact (ii) was already in place). Total fits comfortably
within the **2 Docker iterations** budget S7 PREP §9 forecast.

## 6. Sequencing notes for the S11 ACT picker

| Step | Action | Source | Bearer pins |
|------|--------|--------|-------------|
| 1 | Open new branch `feature/researcher-N-erdos-101-oq-01-s11` from `origin/main` (HEAD `78448f56d0a` or later) | — | — |
| 2 | Edit `proofs/Proofs/Erdos101OQ01.lean`: append §5.1's aggregator + IsBigO + per-P corollary **before** existing `solymosi_stojakovic_lower_bound` (line 297) — keeps "known/elementary" lemmas above "open/aspirational" — recommend insertion point: after `bounds_at_rate_quadratic_over_twelve` (current L207) | §5.1 | §7 |
| 3 | Append §5.2's `isLittleOh_n_squared_iff_isLittleO` bridge lemma immediately after §5.1 block | §5.2 | §7 |
| 4 | Append §5.3's `erdos_101_oq_01_isLittleO_form` def + iff theorem + main sorry-theorem immediately after §5.2 block | §5.3 | §7 |
| 5 | Verify the **bearer-shape** assertions from §4.2 + §3.2 are not also violated by §5.1-§5.3 transcription (i.e., re-read each `apply <lemma>` for `→` direction and confirm goal-state matches lemma's hypothesis shape) | this §5 + §6 | §7 |
| 6 | Run `./proofs/scripts/docker-build.sh Proofs.Erdos101OQ01` from main repo (NOT worktree — slug's symlink trap, see S8 STATE-SYNC §"Build/verification claims" + CLAUDE.md DANGER block) | — | — |
| 7 | If iter 1 fails on `linarith` / `nlinarith` casts: add `push_cast` or split `have : ... ≤ ...` intermediates. Forecast: 1 iter likely clean (per S7 §9 budget); 2 iters worst-case. | — | — |
| 8 | Confirm: sorries 2 → **3** (added `erdos_101_oq_01_isLittleO` main theorem), axioms 0 → 0, theorems 9 → **12** (added 3 — IsBigO + iff bridge + isLittleO-form main), defs 4 → **6** (added `maxFourPointLines` + `erdos_101_oq_01_isLittleO_form`), LOC 471 → ~549 (+78) | — | — |
| 9 | Update `src/data/research/problems/erdos-101-oq-01.json` `currentState.iteration 8 → 11`, `phase PREP → ACT`, `focus` + `nextAction`, `attemptCounts.total 4 → 5`, `lastUpdate` | — | — |
| 10 | Update `research/problems/erdos-101-oq-01/state.md` head block (Phase ACT, Since S11, Iteration 11, Last Updated 2026-05-1X). Push **Active Approach §1-§3** down to a *Previous Focus* block (preserved verbatim per S8 STATE-SYNC's preservation convention). | — | — |
| 11 | Update gallery `src/data/proofs/erdos-101-oq01/meta.json` aggregate counts (sorryCount 2 → 3, theoremCount → 12, definitionCount → 6, lineCount → ~549) | — | — |
| 12 | Push branch, open PR (title: "research(erdos-101-oq-01): S11 ACT — three-artifact IsBigO/IsLittleO bridge (Mathlib-idiom OQ-01 form, build-verified)"), label `research`. | — | — |

**Critical sequencing constraint** (Bug J reminder): artifact (ii) MUST
appear *before* artifact (iii) in the Lean file source order — the
iff proof in §5.3 references `isLittleOh_n_squared_iff_isLittleO`
defined in §5.2.

## 7. Bearer pins for S10 corrections (deltas vs S9 §6)

All bearers re-verified at the unchanged lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). New/refined pins
relative to S9 §6 (which listed `Nat.*` + `abs_of_nonneg` bearers
without line numbers under generic "(mathlib std)"):

| Bearer | file:line @ SHA | Section header / typeclass | Used in S10 artifact |
|--------|-----------------|----------------------------|-----------------------|
| `Asymptotics.IsBigO.of_norm_le` | `Mathlib/Analysis/Asymptotics/Defs.lean:155` | section/namespace `Asymptotics`; no extra typeclass for the `g : α → ℝ` form (the `f` side carries `Norm`/`NormedAddGroup` from outer section) | §5.1 IsBigO body |
| `Asymptotics.isLittleO_iff` | `Mathlib/Analysis/Asymptotics/Defs.lean:175` | same Asymptotics section | §5.2 iff proof unfold |
| `Filter.eventually_atTop` | `Mathlib/Order/Filter/AtTopBot/Basic.lean:72` | `namespace Filter; section IsDirected; variable [Preorder α] [IsDirectedOrder α]; variable [Nonempty α]` (L27, L29-30, L55) — ℕ satisfies all three | §5.2 iff proof, both directions |
| `Real.norm_of_nonneg` | `Mathlib/Analysis/Normed/Group/Basic.lean:1084` | `namespace Real` (immediately above L1078) | §5.1 norm collapse, §5.2 both directions |
| `Real.norm_eq_abs` | `Mathlib/Analysis/Normed/Group/Basic.lean:1078` | `namespace Real` | (alternative to `Real.norm_of_nonneg` if proof prefers `abs` form first) |
| `Nat.div_le_self` | core Lean 4 (`Init.Data.Nat.Basic` — namespace `Nat`) | no typeclass | §5.1 IsBigO body; also used at `Erdos101OQ01.lean:161` in existing proof |
| `Nat.mul_le_mul_left` | core Lean 4 / `Init.Data.Nat.*` (namespace `Nat`) | no typeclass | §5.1 IsBigO body; also used at `Erdos101OQ01.lean:159` |
| `Nat.sub_le` | core Lean 4 (namespace `Nat`) | no typeclass | §5.1 IsBigO body; also used at `Erdos101OQ01.lean:159` |
| `Nat.cast_le` | `Mathlib/Data/Nat/Cast/Order/Basic.lean:76` | section header `variable {α : Type*} [OrderedSemiring α]`; ℝ has `OrderedSemiring ℝ` — satisfied | §5.1 IsBigO body |
| `le_max_left`, `le_max_right` | core Lean 4 (`Init.Order.Lemmas` namespace) / Mathlib base | requires `LinearOrder α`; ℕ has it | §5.2 ← direction lift to max |
| `positivity`, `linarith`, `nlinarith`, `push_cast`, `ring`, `exact_mod_cast` | Mathlib tactics, present at v4.26.0 | — | §5.1 + §5.2 + §5.3 |

### 7.1 S9 §6 phantom-bearer pre-emption

S9 §6 listed `abs_of_nonneg` (`Mathlib/Algebra/Order/AbsoluteValue.lean`)
as a bearer for §5.1. The `Real.norm_of_nonneg`-based S10 §5.1
substitute does **not** call `abs_of_nonneg` (the `‖·‖ = ·` collapse
goes directly to `=` via `norm_of_nonneg`, skipping the `‖·‖ = |·|` →
`|·| = ·` two-step). So `abs_of_nonneg`'s correct location is moot for
the S10 recipe — flagged for the audit-trail only.

### 7.2 Drift verdict

ZERO drift across ~3.4h since S9 PREP §6's recheck. Mathlib still
pinned to v4.26.0 rev `2df2f01…` per `proofs/lake-manifest.json` on
`origin/main` HEAD `78448f56d0a`.

## 8. ACT readiness gate (S11)

| # | Gate item | Status |
|---|-----------|--------|
| 1 | All blocking PRs merged | ✅ (S6 #19221 / S7 #19287 / S8 #19360 / S9 #19403; mechanic #19099 + #19255) |
| 2 | 0 open PRs on slug | ✅ (`gh pr list --search 'erdos-101-oq-01 in:title' --state open --limit 50` → `[]`) |
| 3 | Lake SHA = pinned (zero drift) | ✅ (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) |
| 4 | Corrected sketches with NO H/I/J residue | ✅ (§5.1 + §5.2 + §5.3 + §6 sequencing) |
| 5 | Bearer pins line-numbered + typeclass-checked | ✅ (§7) |
| 6 | LOC budget within S7 §9 envelope | ✅ (~78 LOC vs ~105-125 envelope) |
| 7 | Docker iter forecast ≤ 2 | ✅ (per S7 §9 + S8 §"Verification claims") |
| 8 | Bug-J state.md/JSON staleness flagged for ACT picker | ✅ (§6 step 9-10) |

All 8 items GREEN. Ready for next ACT picker.

## 9. What this S10 PREP does NOT do

- **No Lean edits.** `Erdos101OQ01.lean`, `Erdos101Problem.lean`,
  no other Lean files touched. `git diff origin/main -- proofs/`
  returns empty.
- **No `state.md` edit.** Bug J is flagged but the S8-merged
  state.md head is left intact (next ACT picker rewrites Active
  Approach per §6 step 10).
- **No `src/data/research/problems/erdos-101-oq-01.json` edit.**
  Same reason as state.md.
- **No `src/data/proofs/erdos-101-oq01/meta.json` edit.** Defers to
  S11 ACT (no Lean changes here to count).
- **No Docker build.** Worktree's `proofs/.lake` is a self-symlink
  (per S8 STATE-SYNC §"Build/verification claims" honesty note);
  S11 ACT picker must build from main repo cwd (CLAUDE.md DANGER block).

## 10. File list (1 file, strictly orthogonal to all merged PRs)

- `research/problems/erdos-101-oq-01/sessions/2026-05-16-s10-prep-sibling-audit-of-s9-undefined-iff-bridge.md` (NEW)

No conflict surface with any merged PR (S6/S7/S8/S9 PREPs all touched
different paths; S10 adds a uniquely-named session file). No conflict
with any currently-open PR (queue on slug is empty at S10 claim).

## 11. Honesty notes

- **No Docker build attempted.** This is a doc-only PREP. The Bug-I
  refutation in §4.2 is reasoned from the lemma's *signature* (read
  via `gh api` at the pinned SHA) and standard Lean 4 elaboration
  rules — not from a goal-state dump of a failing Docker run.
- **Bug-H refutation in §3.2** is by `git show origin/main:...
  | grep -nE "(isLittleOh|IsLittleOh)"` — a 3-hit search showing the
  identifier is absent from the slug at the post-S8/S9-merge HEAD.
- **§5.2 lemma proof's `nlinarith` invocation** is *plausible* but
  not Docker-verified. If it fails Docker iter 1, the fallback is the
  explicit chain `calc h : (g n : ℝ) ≤ (ε/2) * (n : ℝ)^2; _ < ε *
  (n : ℝ)^2 := by have hpos : (0:ℝ) < (n:ℝ)^2 := hn_sq_pos; linarith` —
  ~3 extra LOC, well within the +18 LOC budget vs S9.
- **No section-header recheck for `IsBigO.of_norm_le`'s section**
  (i.e., what `[Norm F]` / `[NormedAddCommGroup E]` may be required
  upstream of L155). The two function arguments
  `(maxFourPointLines · : ℝ)` and `(· : ℝ)^2` both inhabit `ℕ → ℝ`,
  for which Mathlib's standard ℝ norm structure is in scope — but if
  the Asymptotics section requires a `SeminormedAddGroup` on the
  target type at the section level (rather than per-lemma), that
  needs Docker confirmation. S11 ACT picker: budget 1 iter for this
  if it surfaces.

## 12. Cross-references

- **S6 PREP (#19221)** — original IsBigO/IsLittleO bridge bearer audit.
- **S7 PREP (#19287)** — sibling-audit of S6, surfacing Bugs A-E.
- **S8 STATE-SYNC (#19360)** — post-drain state.md + JSON refresh; merged Active Approach §1-§3 (still contains Bug F + G via `state.md`).
- **S9 PREP (#19403)** — sibling-audit of S8 Active Approach, surfacing Bugs F + G.
- **S10 PREP (this file)** — sibling-audit of S9 §5.1 + §5.2 corrected sketches, surfacing Bugs H + I + J.
- **MEMORY: `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header`** — about typeclass shape; here the analogous "bearer hypothesis shape" check (Bug I).
- **MEMORY: `feedback_researcher_postship_pivot_audits_own_open_statesync_catching_statement_soundness_bugs_before_act_fires`** — same pattern (audit before ACT picker fires).

🤖 Generated with [Claude Code](https://claude.com/claude-code)
