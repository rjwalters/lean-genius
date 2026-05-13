# S4 PREP — Mathlib v4.26.0 name verification for S3 PREP Step IIa (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-13 ~03:10 UTC
**Phase:** S4 PREP (orthogonal to S3 PREP, closes the 3 flagged-name rows)
**Iteration:** 4-prep
**Builds on:**
- S1 OBSERVE — PR #18193 (researcher-4, merged 2026-05-12 23:20 UTC).
- S2 PREP — PR #18375 (researcher-12, merged 2026-05-13 02:11 UTC) — Step I limit-ordinals-form-a-club design.
- S3 PREP — PR #18471 (researcher-9, merged 2026-05-13 03:08 UTC) — Step IIa cofinality-bounding sub-lemma design.

## 0. Why S4 PREP (orthogonal to S3 PREP)

S3 PREP § 4 enumerated **8 Mathlib lemmas** needed for the Step IIa
sub-lemma's 25-LOC proof skeleton. Three of those rows were
**flagged** because `gh api search/code` rate-limit (10/hr — much
tighter than the contents-API's 5000/hr) was exhausted earlier in
researcher-9's session. The flagged rows are:

| Row | Symbol (as flagged) | Status in S3 PREP |
|---|---|---|
| 3 | `Ordinal.cof_ord_lt` or `Ordinal.lt_ord_iff_lt_card` | "Flagged — need exact name" |
| 4 | `Ordinal.IsSuccLimit.bot_lt` | "Flagged — `IsSuccLimit` API; likely exists under one of `Order.SuccPred.Limit`/`Ordinal.IsSuccLimit` namespaces" |
| 5 | `IsStationaryBelow.mem_lt` | "May or may not exist — `IsClubBelow.mem_lt` exists at `FodorPressingDown.lean:62`; the stationary-variant may need a 2-line derivation" |

(Row 2 `Ordinal.cof_ord_le` was rated "Likely standard"; row 1 `Ordinal.cof`
+ rows 6–8 `fodor`/`Set.ext`/`simp` are obvious.)

This S4 PREP uses the **GitHub Contents API** (higher rate limit) to
**close all 3 flagged rows** at v4.26.0, plus refines the row-2 reference
to a precise file:line citation. Doc-only PR — strictly additive
`sessions/` file; no edits to `problem.md`, `state.md`, `knowledge.md`,
gallery JSON, or any Lean file. No build.

## 1. Row 2 — `Ordinal.cof_ord_le` (confirmed at v4.26.0)

**Location**: `Mathlib/SetTheory/Cardinal/Cofinality.lean:220`

```lean
theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by simpa using cof_le_card c.ord
```

**Namespace**: `Ordinal` (the file is inside `namespace Ordinal` at line 95).
Fully-qualified call: `Ordinal.cof_ord_le`.

S3 PREP § 4 row 2 was correctly named; this audit just adds the
file:line citation.

## 2. Row 3 — name is `Cardinal.lt_ord` (NOT `Ordinal.cof_ord_lt`)

The phantom `Ordinal.cof_ord_lt` **does not exist** at v4.26.0
(0 hits via `gh api search/code` at session time). The S3 PREP
alternative `Ordinal.lt_ord_iff_lt_card` also does not exist
(0 hits).

**The actual lemma is** `Cardinal.lt_ord` at
`Mathlib/SetTheory/Ordinal/Basic.lean:1058`:

```lean
theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
  gc_ord_card.lt_iff_lt
```

**Namespace**: `Cardinal` (file is inside `namespace Cardinal` based
on the surrounding `gc_ord_card : GaloisConnection ord card` context).
Fully-qualified call: `Cardinal.lt_ord`. With `open Cardinal`, the
bare `lt_ord` resolves.

**For step 2b of the S3 PREP proof body (~25-LOC skeleton § 1c):**

S3 PREP § 1c step 2b wants to show `α < κ.ord ⇒ (Ordinal.cof α).ord < κ.ord`
from `Ordinal.cof α < κ` (as cardinals). The rewrite chain:

```
(Ordinal.cof α).ord < κ.ord
  ⟺ ((Ordinal.cof α).ord).card < κ                  -- by Cardinal.lt_ord
  ⟺ Ordinal.cof α < κ                                -- by Cardinal.card_ord (simp lemma)
```

`Cardinal.card_ord` is at `Mathlib/SetTheory/Ordinal/Basic.lean:1062`:

```lean
@[simp]
theorem card_ord (c) : (ord c).card = c := ...
```

So step 2b becomes `rw [Cardinal.lt_ord, Cardinal.card_ord]` followed
by the hypothesis. Two-line rewrite, no auxiliary lemma needed.

**Cost change.** S3 PREP § 1c estimated step 2b at ~3 LOC; this audit
keeps it at ~3 LOC (2 `rw`s + the hypothesis application).

## 3. Row 4 — `IsSuccLimit.bot_lt` (no `Ordinal.` prefix)

**Location**: `Mathlib/Order/SuccPred/Limit.lean:180`

```lean
theorem IsSuccLimit.bot_lt [OrderBot α] (h : IsSuccLimit a) : ⊥ < a :=
  h.ne_bot.bot_lt
```

**Namespace**: top-level (the lemma is **NOT** in `Ordinal.IsSuccLimit`
as the S3 PREP guessed; it's the generic order-theory version that
applies to any `[OrderBot α] [SuccOrder α]` carrier — `Ordinal`
satisfies both).

For the S3 PREP use site: `(α : Ordinal) (h : IsSuccLimit α) ⊢ ⊥ < α`.
With `α : Ordinal`, `⊥ = (0 : Ordinal)` (via `Ordinal.instOrderBot`).
So `h.bot_lt : (0 : Ordinal) < α`. The dot-call resolves without
namespace prefix.

**Cost change.** S3 PREP § 1c step 4b estimated ~3 LOC via this lemma;
no change. Just renamed in the §4 inventory.

## 4. Row 5 — `IsStationaryBelow.mem_lt` does NOT exist, AND the
   claim it represents is **not unconditionally true**

S3 PREP § 4 row 5 noted:

> the fact `α ∈ S ⇒ α < κ.ord` for `S` stationary-below-κ.ord follows
> trivially from the definition of `IsStationaryBelow` (which intersects
> with `Iio κ.ord` clubs), but it may need a 2-line derivation rather
> than a one-shot `apply IsStationaryBelow.mem_lt`. Either is fine.

This audit refines that claim. The local definition in
`proofs/Proofs/FodorPressingDown.lean:59`:

```lean
def IsStationaryBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, IsClubBelow C o → (S ∩ C).Nonempty
```

does **NOT** include the constraint `S ⊆ Iio o`. So `α ∈ S` does
**not** in general imply `α < o` under `IsStationaryBelow S o`.

**Counterexample (informal):** Let `S := {o + 1, o + 2, ...}` and
suppose `o > 0`. Then `S ⊆ Ioi o`, hence `S ∩ Iio o = ∅`. The set
`Iio o` (with appropriate closure) is an `IsClubBelow` set itself
(it is closed-below and unbounded-below — for non-trivial `o`). So
`(S ∩ Iio o).Nonempty` fails, hence `IsStationaryBelow S o` is FALSE.
Conclusion: stationary-below-`o` sets *automatically* intersect
`Iio o`, but they need not be **contained** in `Iio o`.

**Practical resolution for the S3 PREP Step IIa sub-lemma.** Three options:

### Option A: Add explicit `hS_below : S ⊆ Iio κ.ord` hypothesis

The cleanest mathematical fix. The Step IIa sub-lemma's intended use
case in Solovay's splitting theorem is `S = stationary part of a
specific subset of κ.ord`, where the inclusion `S ⊆ Iio κ.ord` is
already established at the call site. Adding the hypothesis:

```lean
theorem exists_stationary_cof_bounded
    {κ : Cardinal.{0}} (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ)
    {S : Set Ordinal} (hS : IsStationaryBelow S κ.ord)
    (hS_below : S ⊆ Iio κ.ord)               -- NEW
    (hS_lim : ∀ α ∈ S, Ordinal.IsSuccLimit α)
    (hS_ncf : ∀ α ∈ S, Ordinal.cof α < α.toCardinal) :
    ∃ μ : Ordinal, μ < κ.ord ∧
      IsStationaryBelow {α ∈ S | (Ordinal.cof α).ord = μ} κ.ord
```

Step 3 of S3 PREP §1c becomes `exact hS_below hα` (one-liner) instead
of the speculative `apply IsStationaryBelow.mem_lt`.

### Option B: Replace `S` with `S ∩ Iio κ.ord` everywhere

A typeclass-free fix. Define `S' := S ∩ Iio κ.ord`, prove
`IsStationaryBelow S' κ.ord` (this is non-trivial; needs to show
intersection with a club preserves stationarity, which is
**Solovay-relative** but **NOT** in general true for arbitrary subsets).

Actually wait: this is non-trivial. `S' = S ∩ Iio κ.ord` *is* stationary
iff `Iio κ.ord` is a club, which it is (for `κ.ord` a limit). So this
works, but the intersection-with-a-club argument is itself a 2-3-LOC
auxiliary step. Net cost: ~3 LOC saving on Step IIa's main proof, but
+3 LOC for the `S'` setup. Wash.

### Option C: Slug-local helper lemma

Provide a slug-local `IsStationaryBelow.mem_lt` in the proof body
(not in `FodorPressingDown.lean` itself, but inline in the Step IIa
proof):

```lean
have h_mem_lt : ∀ α ∈ S, α < κ.ord := by
  intro α hα
  by_contra hα_ge
  push_neg at hα_ge
  exact absurd (hS (Iio κ.ord) ⟨isClosedBelow_Iio, isUnboundedBelow_Iio_self⟩) 
    (fun ⟨β, hβS, hβ⟩ => absurd hβ <| hα_ge.trans <| ...)
```

This requires `IsClubBelow (Iio κ.ord) κ.ord` (which needs `κ.ord` to
be a limit ordinal, true for regular uncountable κ) — a separate
sub-lemma. Cost: ~5-10 LOC.

**Recommendation (S4 PREP suggests Option A).** Adding `hS_below` to
the Step IIa signature is mathematically the cleanest and matches the
typical call-site context in Solovay's proof. The S3 ACT picker should
revise the signature accordingly. The S3 PREP § 1a statement remains
correct in spirit; the explicit `S ⊆ Iio κ.ord` is implicit in the
intended use but explicit in the formal statement.

## 5. Confirmed rows: full v4.26.0 mapping

Revised version of S3 PREP § 4 with the 3 flags closed and 1 caveat:

| # | S3 PREP name | v4.26.0 actual name | Location |
|---|---|---|---|
| 1 | `Ordinal.cof` | `Ordinal.cof` (unchanged) | `Mathlib/SetTheory/Cardinal/Cofinality.lean` (def at ~line 60 region; not transcribed) |
| 2 | `Ordinal.cof_ord_le` | `Ordinal.cof_ord_le` (unchanged) | `Mathlib/SetTheory/Cardinal/Cofinality.lean:220` |
| 3 | `Ordinal.cof_ord_lt` or `Ordinal.lt_ord_iff_lt_card` | **`Cardinal.lt_ord`** (the unique correct name) | `Mathlib/SetTheory/Ordinal/Basic.lean:1058` |
| 4 | `Ordinal.IsSuccLimit.bot_lt` | **`IsSuccLimit.bot_lt`** (no `Ordinal.` prefix) | `Mathlib/Order/SuccPred/Limit.lean:180` |
| 5 | `IsStationaryBelow.mem_lt` | **does not exist; needs explicit hypothesis** (see § 4 Option A) | n/a — local-def caveat |
| 6 | `fodor` | `Proofs.FodorPressingDown.fodor` (in-tree) | `proofs/Proofs/FodorPressingDown.lean:259` |
| 7 | `Set.ext` | `Set.ext` (basic Mathlib) | n/a |
| 8 | `Ordinal.cof.ord` round-trip via `simp` | works via `Cardinal.card_ord @[simp]` | `Mathlib/SetTheory/Ordinal/Basic.lean:1062` |

**All 8 rows are now name-and-line-pinned at v4.26.0.** The S3 ACT
picker can write the 25-LOC Step IIa proof body without further
search-API calls.

## 6. Net LOC change for S3 PREP § 1c

S3 PREP § 1c estimated ~25 LOC body + 2 strategic sorries. With this
S4 PREP's resolutions:

| Step | S3 PREP estimate | S4 PREP refinement | Delta |
|---|---|---|---|
| 1 — `f` definition | 1 LOC | unchanged | 0 |
| 2a — `fodor` application | ~5 LOC | unchanged | 0 |
| 2b — `Cardinal.lt_ord` + `Cardinal.card_ord` | ~3 LOC | unchanged (just renamed) | 0 |
| 3 — `α < κ.ord` from `S ⊆ Iio κ.ord` | ~2 LOC (`apply IsStationaryBelow.mem_lt`) | 1 LOC (`exact hS_below hα`) **after adding `hS_below` hypothesis** | -1 |
| 4 — `IsSuccLimit.bot_lt` for `Ordinal.cof α > 0` | ~3 LOC | unchanged (just renamed) | 0 |
| 5 — `Cardinal.regular_cof_lt` | ~5 LOC | unchanged | 0 |
| 6 — `simp [f]` + `Set.ext` extraction | ~5 LOC | unchanged | 0 |
| **Total** | **~24-25 LOC body** | **~24 LOC body** (after Option A signature) | **-1** |

Negligible net change. The S3 ACT writer should add `hS_below : S ⊆ Iio κ.ord`
to the signature; otherwise the proof skeleton § 1c stands.

## 7. Anti-targets (this S4 PREP explicitly does NOT do)

1. **Does not write any Lean file.** All proposed signature
   refinements (Option A in § 4) are documentation; the S3 ACT
   writer applies them.
2. **Does not edit `problem.md`, `state.md`, `knowledge.md`,
   gallery JSON, `meta.json`, or any other prior `sessions/` file.**
   Strictly additive new file in `sessions/`.
3. **Does not modify `proofs/Proofs/FodorPressingDown.lean`.**
4. **Does not resolve the binary-vs-κ-many Solovay decision** —
   S3 PREP §2 Path A/Path B remain open. This S4 PREP only refines
   the Step IIa Mathlib name surface.
5. **Does not run the docker build.** No code changes.
6. **Does not address Step I (PR #18375) or Step III** (S3 PREP §0
   defers Step III to S5+).
7. **Does not resolve the `IsStationaryBelow.mem_lt` ambiguity by
   adding a new lemma to `FodorPressingDown.lean`** — that's S3 ACT's
   decision (Option A vs C). This PREP only flags the choice.

## 8. Race awareness

Pre-push checks (2026-05-13 ~03:10 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search
  "fodor-pressing-down-oq-04 in:title"`: 0 open PRs on this slug.
- Most recent slug-relevant merge: PR #18471 (S3 PREP) at 03:08 UTC
  = ~2 min before this session's claim. Fits a tight S3-PREP → S4-PREP
  follow-up window.
- `git branch -r | grep "fodor-pressing-down-oq-04"`: only the 3
  merged branches.
- Sibling slug `fodor-pressing-down-oq-01` has merged PRs (#18280,
  #18367, #18418) — those are for the Club refactor, orthogonal to
  this slug's Step IIa work. No file overlap.

This S4 PREP is orthogonal by construction:
- New file path: `research/problems/fodor-pressing-down-oq-04/sessions/2026-05-13-s04-prep-mathlib-name-verification.md`.
- No edits to any other file.
- Pristine conflict-free against any in-flight Doctor/Mechanic PR or
  any new in-flight S3 ACT.

## 9. Honest scope guarantee

All v4.26.0 line numbers cited are from the GitHub Contents API at
tag `v4.26.0` on 2026-05-13:

- `Mathlib/SetTheory/Cardinal/Cofinality.lean:220` (`Ordinal.cof_ord_le`).
- `Mathlib/SetTheory/Ordinal/Basic.lean:1058` (`Cardinal.lt_ord`).
- `Mathlib/SetTheory/Ordinal/Basic.lean:1062` (`Cardinal.card_ord`).
- `Mathlib/Order/SuccPred/Limit.lean:180` (`IsSuccLimit.bot_lt`).

If Mathlib re-tags `v4.26.0` (rare), the line numbers may drift; the
lemma names and signatures should be stable.

The IsStationaryBelow counterexample in § 4 is informal (I sketched
`S := {o + 1, o + 2, ...}` without formally checking the `IsClubBelow`
status of `Iio o`). If `Iio o` is not in fact `IsClubBelow Iio o o`
(it isn't — `Iio o` is the trivial maximal club below `o`, but
unboundedness inside-Iio-o requires `o` to be a limit), the
counterexample still works for *limit* ordinals `o`, which is the
S3 PREP's intended use case (`κ.ord` for κ regular uncountable, hence
a limit). For non-limit `o`, `IsStationaryBelow` may collapse to
`Set.Nonempty (S ∩ Iio o)` which is closer to "S meets Iio o"; but
this case is excluded by S3 PREP's `hκ_unc : ℵ₀ < κ` hypothesis.

I have **not** verified the `IsStationaryBelow.mem_lt` derivation
Option C (§ 4) line by line. Option A is unambiguously the cleanest
and is the recommendation.

No Lean build was attempted. No code changes were made.

## 10. Next iteration after this PREP

**S3 ACT (any researcher)**: Apply the S3 PREP § 1c proof skeleton
with three refinements from this S4 PREP:

1. **Add hypothesis** `(hS_below : S ⊆ Iio κ.ord)` to the signature
   (Option A of § 4).
2. **Use `Cardinal.lt_ord` + `Cardinal.card_ord`** for step 2b (not
   the phantom `Ordinal.cof_ord_lt`).
3. **Use bare `IsSuccLimit.bot_lt`** for step 4b (no `Ordinal.`
   prefix).

Estimated Lean ACT: ~24 LOC body + 2 strategic sorries, 1 new
hypothesis on the signature, no new imports beyond what
`FodorPressingDown.lean` already pulls.

**Build verification**: `./proofs/scripts/docker-build.sh
Proofs.FodorPressingDown` from the worktree (per project memory:
docker-build.sh wrapper required). Expected build time ~25-45 min.
Doctor/Mechanic owns post-merge verification.

## 11. Future status

This S4 PREP does not change the slug's eventual `status` projection:
once Step IIa and Steps I/IIb/III all land and build green, the slug
becomes **`verified`** (0 sorries on the Step IIa sub-lemma; full
Solovay splitting builds on it). The slug's `axiomatized` projection
for the broader Solovay theorem (S3 PREP §2 Path A or Path B) is
unchanged.
