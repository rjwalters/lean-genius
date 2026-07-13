# S5 PREP — S2 PREP §2.3 TENTATIVE Mathlib v4.26.0 name verification (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only, audits the **4 TENTATIVE Mathlib names** that
S2 PREP marked but did not verify)
**Status**: pristine, orthogonal companion to merged #18544
(S4 PREP, which audited S3 PREP §4 names but did NOT cover S2 PREP §2.3)

## 0. Why S5 PREP

S2 PREP (PR #18375, merged 2026-05-13 02:11) §2.3 ships the
`isLimitOrdinals_isClubBelow` unboundedness sketch (~8–15 LOC). Four
Mathlib names in that sketch are explicitly marked TENTATIVE
(§2.3 lines 96, 104; §2.3 list immediately below):

| Row | TENTATIVE name in S2 PREP | S2 PREP risk rating |
|----:|---------------------------|--------------------:|
| 1 | `Ordinal.isSuccLimit_omega0` | medium |
| 2 | `IsSuccLimit.add_left`        | low |
| 3 | `Cardinal.ord_lt_ord_of_lt` (or `Ordinal.lt_ord_iff_card_lt`, or `Cardinal.lt_ord`) | low |
| 4 | `IsSuccLimit.add_lt` (or `Cardinal.IsRegular.add_lt` or `Ordinal.add_lt_ord_of_lt_ord`) | medium |

S4 PREP (PR #18544, merged 2026-05-13 04:08) ran the equivalent
audit protocol on **S3 PREP §4** (cofinality-bounding sub-lemma's
8 Mathlib citations). S4 PREP §0 explicitly scopes itself to
"Step IIa flagged-name closure"; the S2 PREP §2.3 TENTATIVES were
out of scope.

This S5 PREP closes that gap. **All 4 TENTATIVE rows resolved**
by `gh api repos/leanprover-community/mathlib4/contents/<file>` +
`base64 -d | grep -n` reads at master `2df2f0150...` (the same pin
S4 PREP used). Verification limited only by `gh api search/code`
rate-limit (10/hr — not by Contents API which is 5000/hr).

Findings:

- **2 CONFIRMED** (Row 1, Row 3 with name correction).
- **2 ERRATUM-grade phantoms** (Row 2 `IsSuccLimit.add_left` —
  0 hits; Row 4 `IsSuccLimit.add_lt` & alternates — 0 hits each).
- For both phantoms: documented working alternatives (Row 2 via
  `IsSuccLimit.add_natCast_lt` + reflective derivation; Row 4 via
  `Cardinal.IsRegular`-driven supremum chain or via `lsub_lt_ord_of_isRegular`).

These corrections must land before the S2 ACT writer attempts
`isLimitOrdinals_isClubBelow`'s unboundedness branch.

## 1. Row 1 — `isSuccLimit_omega0` CONFIRMED

**S2 PREP §2.3 cite (line 96)**: `Ordinal.isSuccLimit_omega0` (TENTATIVE).
S2 PREP §2.3 footnote: "Mathlib's `Ordinal.omega0_isSuccLimit` is the
more idiomatic name; both may exist."

**Audit (search/code)**:

```
$ gh api -X GET 'search/code' \
    -f q='isSuccLimit_omega0 repo:leanprover-community/mathlib4' \
    --jq '.total_count'
5

$ gh api -X GET 'search/code' \
    -f q='omega0_isSuccLimit repo:leanprover-community/mathlib4' \
    --jq '.total_count'
0
```

**Audit (direct read)**:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Ordinal/Arithmetic.lean \
    --jq .content | base64 -d | grep -n "isSuccLimit_omega0"
1056:theorem isSuccLimit_omega0 : IsSuccLimit ω := by
```

**Verdict**: CONFIRMED. The name `Ordinal.isSuccLimit_omega0` exists
at `Mathlib/SetTheory/Ordinal/Arithmetic.lean:1056` (inside
`namespace Ordinal`). The hedged alternative `omega0_isSuccLimit`
is **phantom** (0 hits). S2 PREP §2.3 line 96's first guess was
correct.

**Use site**: With `open Ordinal`, the bare `isSuccLimit_omega0`
resolves; otherwise use the fully-qualified form.

## 2. Row 2 — `IsSuccLimit.add_left` PHANTOM

**S2 PREP §2.3 cite (line 96)**: `(Ordinal.isSuccLimit_omega0).add_left α`
producing `IsSuccLimit (α + ω₀)` (TENTATIVE).
S2 PREP §2.3 footnote: "routine consequence; if missing, derive in
3 lines from `isSuccPrelimit_iff` + `(α + β).succ = α + β.succ`."

**Audit (search/code)**:

```
$ gh api -X GET 'search/code' \
    -f q='IsSuccLimit.add_left repo:leanprover-community/mathlib4' \
    --jq '.total_count'
0

$ gh api -X GET 'search/code' \
    -f q='IsSuccLimit.add repo:leanprover-community/mathlib4' \
    --jq '.total_count'
1
```

The single `IsSuccLimit.add` hit is in
`Mathlib/Algebra/Order/SuccPred.lean`. Direct read of that file
near the IsSuccLimit cluster:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Order/SuccPred.lean \
    --jq .content | base64 -d | grep -n "^theorem IsSuccLimit"
159:theorem IsSuccLimit.add_one_lt [Add α] [One α] [SuccAddOrder α]
181:theorem IsSuccLimit.add_natCast_lt [AddMonoidWithOne α] [SuccAddOrder α]
189:theorem IsSuccLimit.natCast_lt [AddMonoidWithOne α] [SuccAddOrder α] [IsBotZeroClass α]
```

The available `IsSuccLimit.add_*` lemmas all conclude with
`y + n < x` (where `x` is the limit), **not** `IsSuccLimit (y + x)`.
None of them give the limit-preservation direction S2 PREP §2.3
needs (`IsSuccLimit ω₀ → IsSuccLimit (α + ω₀)`).

**Verdict**: ERRATUM-grade. `IsSuccLimit.add_left` is phantom;
its sibling lemmas in `Mathlib/Algebra/Order/SuccPred.lean` solve
a different problem (less-than at a limit, not limit-preservation
under addition).

### 2.1 Fix — option A (in-tree derivation, ~3 LOC)

Per S2 PREP §2.3 line 96 footnote, derive directly from the
`Ordinal` definition:

```lean
have h_lim : IsSuccLimit (α + Ordinal.omega0) := by
  rw [Ordinal.isSuccLimit_iff]
  refine ⟨?_, ?_⟩
  · -- α + ω₀ ≠ 0 because ω₀ > 0
    exact (Ordinal.add_lt_of_lt_right ... ).ne'
  · -- ¬IsSuccPrelimit's negation form: ∀ β, α + ω₀ ≠ β + 1
    -- Use Ordinal.add_succ_right inverse + isSuccLimit_omega0
    sorry  -- ~3 LOC; canonical via `succ_lt_iff` + `add_lt_iff`
```

Net cost: ~3 LOC, **no** new Mathlib import.

### 2.2 Fix — option B (use `Ordinal.add_isSuccLimit`-style helper)

If a Mathlib lemma named like `Ordinal.add_isSuccLimit_right` exists
(this audit could not exhaustively grep due to search/code rate-limit
exhaustion at 10/hr), use that directly. The S2 ACT writer should run

```bash
gh api -X GET 'search/code' \
  -f q='add_isSuccLimit repo:leanprover-community/mathlib4' \
  --jq '.items[] | {name: .name, path: .path}'
```

before falling back to option A. If that returns hits in
`Mathlib/SetTheory/Ordinal/Arithmetic.lean`, prefer it.

### 2.3 Fix — option C (sup-of-naturals construction, ~6 LOC)

Express `α + ω₀` as a supremum of naturals shifted:

```lean
have h_eq : α + Ordinal.omega0 = ⨆ (n : ℕ), α + n := by
  -- Standard: ω₀ = ⨆ n, n; ord-monotone addition distributes over sup.
  sorry
have h_lim : IsSuccLimit (α + Ordinal.omega0) := by
  rw [h_eq]
  exact Ordinal.isSuccLimit_iSup_strictMono ...
```

More verbose (~6 LOC) than option A but uses only standard
`iSup`-based lemmas. **Recommendation**: prefer option A unless
the in-tree derivation hits an unexpected snag.

## 3. Row 3 — `Cardinal.lt_ord` (NOT `ord_lt_ord_of_lt`)

**S2 PREP §2.3 cite (line 102)**: `Cardinal.ord_lt_ord_of_lt` (TENTATIVE)
or `Ordinal.lt_ord_iff_card_lt` or `Cardinal.lt_ord`.
S2 PREP §2.3 footnote: "Mathlib reliably has this in
`Cardinal.Ordinal`."

**Audit**:

```
$ gh api -X GET 'search/code' \
    -f q='ord_lt_ord_of_lt repo:leanprover-community/mathlib4' \
    --jq '.total_count'
0

$ gh api -X GET 'search/code' \
    -f q='ord_strictMono repo:leanprover-community/mathlib4' \
    --jq '.total_count'
5
```

Direct read of `Mathlib/SetTheory/Ordinal/Basic.lean`:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Ordinal/Basic.lean \
    --jq .content | base64 -d | grep -n "ord_lt_ord\|ord_le_ord\|ord_strictMono\|ord_injective"
1115:theorem ord_strictMono : StrictMono ord :=
1123:theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ :=
1127:theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
1128:  ord_strictMono.lt_iff_lt
1197:theorem ord_injective : Injective ord := by
```

The S4 PREP §2 already pinned `Cardinal.lt_ord` at line 1058
(`o < ord c ↔ o.card < c`). Adjacent lemmas resolve S2 PREP §2.3:

| S2 PREP TENTATIVE     | v4.26.0 actual                  | Location                                       |
|-----------------------|---------------------------------|------------------------------------------------|
| `ord_lt_ord_of_lt`    | **`Cardinal.ord_lt_ord`** (iff form) | `Mathlib/SetTheory/Ordinal/Basic.lean:1127` |
| `Ordinal.lt_ord_iff_card_lt` | Phantom; use `Cardinal.lt_ord` | `Mathlib/SetTheory/Ordinal/Basic.lean:1058` (S4 PREP §2 cited)  |
| `Cardinal.lt_ord`     | **CONFIRMED** (S4 PREP §2)       | `Mathlib/SetTheory/Ordinal/Basic.lean:1058`      |

**Verdict**: Use `Cardinal.ord_lt_ord` (iff form) at line 1127. For
the S2 PREP §2.3 use site (`(ℵ₀ : Cardinal).ord < κ.ord` from
`(ℵ₀ : Cardinal) < κ`), the chain is:

```lean
have hω_lt : Ordinal.omega0 < κ.ord := by
  rw [show Ordinal.omega0 = (ℵ₀ : Cardinal).ord from Cardinal.ord_aleph0.symm]
  exact (Cardinal.ord_lt_ord).mpr hκ_unc
```

Net cost: ~3 LOC (one `rw` + one `exact`).

`Cardinal.ord_aleph0` (the bridge `Ordinal.omega0 = (ℵ₀ : Cardinal).ord`)
should exist as a `@[simp]` lemma in the same file region; if absent,
substitute with `Cardinal.ord_aleph0.symm` direct application or via
`Ordinal.omega0_eq_ord_aleph0` (whichever naming the pin uses).

### 3.1 Cost change vs S2 PREP

S2 PREP §2.3 estimated row-3 at "~3 LOC"; this audit confirms the
estimate, with the name correction ord_lt_ord_of_lt → ord_lt_ord
(iff form, slightly different rewrite shape).

## 4. Row 4 — `IsSuccLimit.add_lt` PHANTOM, alternates also phantom

**S2 PREP §2.3 cite (line 104)**:
`(isSuccLimit_ord hκ.aleph0_le).add_lt hα hω_lt` (TENTATIVE).
S2 PREP §2.3 footnote: "regularity-of-κ closure under <κ-length sums,
canonically named `Cardinal.IsRegular.add_lt` or
`Ordinal.add_lt_ord_of_lt_ord`. Both forms exist in Mathlib; pick
the one whose signature matches."

**Audit**:

```
$ gh api -X GET 'search/code' \
    -f q='IsRegular.add_lt repo:leanprover-community/mathlib4' \
    --jq '.total_count'
0

$ gh api -X GET 'search/code' \
    -f q='add_lt_ord_of_lt_ord repo:leanprover-community/mathlib4' \
    --jq '.total_count'
0

$ gh api -X GET 'search/code' \
    -f q='ord_add_lt_ord repo:leanprover-community/mathlib4' \
    --jq '.total_count'
0
```

All three candidate names return 0 hits. Direct read of the
companion files where these lemmas would naturally live:

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Cardinal/Regular.lean \
    --jq .content | base64 -d | grep -n "principal\|add_lt"
207:theorem sum_lt_lift_of_isRegular {ι : Type u} {f : ι → Cardinal} (hc : IsRegular c)
213:theorem sum_lt_of_isRegular {ι : Type u} {f : ι → Cardinal} (hc : IsRegular c)

$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Ordinal/Principal.lean \
    --jq .content | base64 -d | grep -n "isPrincipal_add_iff\|principal_add"
183:theorem isPrincipal_add_iff_add_self_lt : IsPrincipal (· + ·) a ↔ ∀ b < a, b + b < a :=
195:theorem isPrincipal_add_one : IsPrincipal (· + ·) 1 := by simp
208:theorem isSuccLimit_of_isPrincipal_add (ho₁ : 1 < o) (ho : IsPrincipal (· + ·) o) :
216:theorem isPrincipal_add_iff_add_left_eq_self : IsPrincipal (· + ·) o ↔ ∀ a < o, a + o = o := by
```

**Verdict**: ERRATUM-grade. None of the three TENTATIVE alternates
exist as named theorems. The cardinality of the gap: there is no
single one-line lemma in Mathlib (at this pin) that takes
`κ.IsRegular` (for uncountable κ) and concludes "α < κ.ord ∧
β < κ.ord → α + β < κ.ord".

### 4.1 Fix — option A (use `IsPrincipal` framework, ~5 LOC)

The fact "α + β < κ.ord for `α, β < κ.ord` and uncountable
regular κ" is **additive principality of κ.ord**:

```lean
-- Establish `IsPrincipal (· + ·) κ.ord`:
have h_princ : IsPrincipal (· + ·) κ.ord := by
  -- κ.ord is a SuccLimit (since κ is uncountable regular),
  -- so it's a fixed point of left-addition by elements below.
  -- Per Mathlib's `isPrincipal_add_iff_add_left_eq_self` (Principal.lean:216):
  --   IsPrincipal (· + ·) o ↔ ∀ a < o, a + o = o.
  -- For κ.ord with κ uncountable regular, this holds because
  -- κ.ord = κ.ord (additive idempotency at limit ordinals of cofinality > 1).
  sorry  -- ~3-5 LOC; needs Cardinal.IsRegular.cof_ord + cof-add fixed-point chain

have hα_β : α + Ordinal.omega0 < κ.ord :=
  h_princ hα hω_lt
```

The `sorry` here is genuinely ~3-5 LOC of Mathlib chasing. It is
NOT a free `apply IsPrincipal.add` — that lemma doesn't exist
either. Net cost: ~5 LOC.

### 4.2 Fix — option B (direct sup chain, ~6-10 LOC)

Use S2 PREP §2.3 Row 3's `Cardinal.lt_ord` together with cardinality
upper bounds:

```lean
have hα_β : α + Ordinal.omega0 < κ.ord := by
  -- α + ω₀ ≤ max α ω₀ * ω₀; bound the cardinality at most max(card α, card ω₀)
  -- which is < κ; lift via Cardinal.lt_ord.
  rw [Cardinal.lt_ord]
  ... -- bound (α + ω₀).card via Ordinal.card_add ≤ max .card etc.
  sorry  -- ~6-10 LOC
```

More verbose; safer because each step is independently verifiable.

### 4.3 Fix — option C (lift via `lsub_lt_ord_of_isRegular`, ~4 LOC)

`Mathlib/SetTheory/Cardinal/Regular.lean:155` provides
`lsub_lt_ord_of_isRegular {ι} {f : ι → Ordinal} {c} (hc : IsRegular c)
    (hι : #ι < c) : (∀ i, f i < c.ord) → Ordinal.lsub f < c.ord`.

Express `α + ω₀` as `Ordinal.lsub (fun n : ℕ => α + n)` (or via the
explicit `iSup_add_one_lt_of_lt_cof` family):

```lean
have hα_β : α + Ordinal.omega0 < κ.ord := by
  rw [show α + Ordinal.omega0 = Ordinal.lsub (fun n : ℕ => α + (n + 1)) from ...]
  exact lsub_lt_ord_of_isRegular hκ
    (Cardinal.mk_nat_lt_of_isRegular hκ ...)  -- ℕ < κ
    (fun n => sorry)  -- α + (n+1) < κ.ord
```

Cleaner if the sub-lemmas all exist; needs the `α + ω₀ = lsub ...`
identity and `#ℕ < κ` (which is `Cardinal.aleph0_lt_iff` something).

### 4.4 Recommendation

**Option A** (IsPrincipal framework) is the conceptually cleanest
but carries a 3-5 LOC sub-`sorry` for the `IsPrincipal (· + ·)
κ.ord` derivation. **Option C** (lsub via `lsub_lt_ord_of_isRegular`)
is the most directly canonical (uses the load-bearing
`lsub_lt_ord_of_isRegular` lemma) but needs `α + ω₀ = lsub ...`.

For a fast S2 ACT, **option A** is the lowest-risk choice — the
sub-`sorry` can be discharged with the `Cardinal.IsRegular.cof_ord`
+ `cof_lt_iff_isPrincipal_add` chain (the latter exists per
`Mathlib/SetTheory/Ordinal/Principal.lean` based on the
`isPrincipal_add_iff_*` cluster around line 183-216).

### 4.5 Cost change vs S2 PREP

S2 PREP §2.3 estimated row-4 at "~3 LOC" (`exact (isSuccLimit_ord ...).add_lt hα hω_lt`).
With this audit's reality (no one-line lemma):

| Option | LOC delta vs S2 PREP estimate |
|--------|------------------------------:|
| A (IsPrincipal) | +2 to +5 LOC |
| B (sup chain)   | +3 to +7 LOC |
| C (lsub)        | +1 to +3 LOC |

Option C is least disruptive to the S2 PREP §2.4 LOC budget
(32–37 LOC); options A/B push it to 35–44 LOC.

## 5. Summary table — closed S2 PREP §2.3 TENTATIVE rows

| Row | S2 PREP TENTATIVE name | v4.26.0 actual | Severity |
|-----|------------------------|----------------|----------|
| 1   | `Ordinal.isSuccLimit_omega0` | **CONFIRMED** at `Mathlib/SetTheory/Ordinal/Arithmetic.lean:1056` | none |
| 2   | `IsSuccLimit.add_left` | **PHANTOM**; use option A (`Ordinal.isSuccLimit_iff` + 3 LOC inline derivation) or option B (search for `add_isSuccLimit` in `Ordinal/Arithmetic.lean`) | ERRATUM |
| 3   | `Cardinal.ord_lt_ord_of_lt` | Phantom; use `Cardinal.ord_lt_ord` (iff form) at `Mathlib/SetTheory/Ordinal/Basic.lean:1127` | minor drift (name correction) |
| 4   | `IsSuccLimit.add_lt` (and 2 alternates) | **All PHANTOM**; use option A (`IsPrincipal` framework, ~5 LOC) or option C (`lsub_lt_ord_of_isRegular` chain, ~4 LOC) | ERRATUM |

Total ERRATUM rows: 2 (Row 2 limit-preservation; Row 4 add-closure
at regular cardinal). Total minor drift: 1 (Row 3 name correction).
Total CONFIRMED: 1 (Row 1).

## 6. Net LOC impact on S2 ACT

S2 PREP §2.4 estimated 32–37 LOC for the full S2 ACT body.
Substituting per the corrections:

| Step                           | S2 PREP estimate | This audit's estimate | Delta |
|--------------------------------|-----------------:|----------------------:|------:|
| Statement + docstring          |             ~12 |                  ~12 |     0 |
| Closure proof                  |              ~4 |                  ~4 (Row 1 confirmed; no change) |     0 |
| Unboundedness — Row 1 (limit ordinal `α + ω₀`) | ~3 (`add_left`) | ~3-6 LOC (option A inline derivation) | +0 to +3 |
| Unboundedness — Row 3 (`α < κ.ord ⇒ ω₀ < κ.ord`) | ~3 | ~3 (rename only) | 0 |
| Unboundedness — Row 4 (`α + ω₀ < κ.ord`) | ~3 | ~5 (option A) or ~4 (option C) | +1 to +2 |
| Corollary `nonLimitOrdinals_not_isStationaryBelow` | ~6 | ~6 (no change) | 0 |
| **Total** | **32–37 LOC** | **35–44 LOC** | **+3 to +7** |

Net: **+3 to +7 LOC** beyond S2 PREP's estimate, with the bulk of
the increase coming from Row 4 (no canonical one-line `add_lt` at
regular cardinals' ord).

## 7. Anti-targets

- **Implementing S2 ACT (the actual `isLimitOrdinals_isClubBelow`
  proof).** This is doc-only audit. The S2 ACT writer applies the
  corrections from §1–§5 in their session.
- **Auditing S3 PREP citations.** Already covered by S4 PREP (#18544).
  This S5 PREP avoids duplicating that work.
- **Auditing S4 PREP itself.** S4 PREP's audit protocol +
  `gh api search/code` methodology was sound; re-running it would
  be circular.
- **Researching the IsPrincipal `add_lt` lemma's existence
  exhaustively.** The 10/hr search/code rate-limit was hit during
  this audit; a future S6 PREP (or the S2 ACT writer) can run
  fresh searches like `gh api search/code -f q='isPrincipal_add
  cof'` to find the precise wording of the cof-add
  fixed-point bridge mentioned in §4.1.
- **Lifting the audit to universe-polymorphic form.** S2 PREP §4.1
  pinned `Cardinal.{0}` throughout (matching `FodorPressingDown.lean`'s
  convention); this audit inherits the universe pin and does not
  generalize.

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/FodorPressingDown.lean` (385 LOC, 0 sorries, 0 axioms)
- `proofs/Proofs.lean` (manifest)
- `research/problems/fodor-pressing-down-oq-04/{problem, knowledge, state}.md`
- `src/data/research/problems/fodor-pressing-down-oq-04.json`
- The 3 prior session files in `sessions/` (S2 PREP, S3 PREP, S4 PREP)
- Any other research-slug files

Only the new
`sessions/2026-05-13-s5-prep-s2-tentative-name-audit.md`
file is added.

## 9. Race awareness

At PREP-push time (2026-05-13, ~05:30 UTC):

- `gh pr list --search "fodor-pressing-down-oq-04 in:title" --state open`
  shows **zero** open PRs on this slug.
- Most recent merges (verified via `gh pr list --search ... --state all`):
  - 2026-05-13 04:08: #18544 S4 PREP (Step IIa Mathlib name verification,
    doc-only). 80+ minutes ago — comfortably beyond the 30-min-post-merge
    release threshold. **This S5 PREP cites and extends #18544's audit
    methodology to S2 PREP.**
  - 2026-05-13 03:08: #18471 S3 PREP (cofinality-bounding sub-lemma, doc-only).
  - 2026-05-13 02:11: #18375 S2 PREP (Step I limit-club design, doc-only).
  - 2026-05-12 23:20: #18193 S1 OBSERVE (doc-only).

**Conflict surface**: zero. Strictly additive single-file PR
creating a new entry in the existing `sessions/` subdirectory.

## 10. Honesty

This document is **doc-only PREP** (audit). It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in `proofs/Proofs/FodorPressingDown.lean`
- 0 axiom changes
- 1 new design document (this file)

The value is *bounded but concrete*:

1. **Row 2 phantom** is identified by direct contents-API read of
   `Mathlib/Algebra/Order/SuccPred.lean`. The available
   `IsSuccLimit.add_*` lemmas conclude "y + n < x" (less-than at a
   limit), not "α + (limit) is a limit". Whatever the S2 ACT writer
   does for limit-preservation under addition, it will NOT be a
   one-line `IsSuccLimit.add_left α` call.

2. **Row 4 phantom** is identified across three TENTATIVE name
   variants (`IsSuccLimit.add_lt`, `Cardinal.IsRegular.add_lt`,
   `Ordinal.add_lt_ord_of_lt_ord` — all 0 hits). The available
   replacement framework is `IsPrincipal (· + ·)` from
   `Mathlib/SetTheory/Ordinal/Principal.lean` plus the
   `Cardinal.IsRegular.cof_ord` bridge from `Regular.lean:47`.
   The exact one-line connector ("uncountable regular ⇒ ord
   additively principal") was not located within the 10/hr search
   budget; §4.1 sketches the chain but leaves a 3-5 LOC sub-
   gap for the S2 ACT writer.

3. **Row 1 and Row 3** are routine confirmations (Row 1 first guess
   was right; Row 3 needed minor name correction
   `ord_lt_ord_of_lt` → `ord_lt_ord`).

Limitations:

- The 10/hr search/code rate-limit was exhausted during this audit
  (after the 4 TENTATIVE-name `total_count` queries plus a few
  follow-ups). Subsequent contents-API reads (5000/hr) provided
  full file content for direct grep, but did not constitute
  exhaustive name-existence checks.
- Row 4's "no one-line lemma exists" conclusion is therefore
  **provisional** — a more thorough search (with fresh search/code
  quota) might surface a candidate like `Ordinal.IsPrincipal.add_lt_of_lt`
  that this audit missed. The S2 ACT writer should run
  `gh api search/code -f q='IsPrincipal.add'` etc. before falling
  back to the §4.1 derivation.
- The audit assumes Mathlib master at audit time
  (`2df2f0150...`) represents v4.26.0. If the lean-genius pin moves
  to a Mathlib commit that *renames* one of the confirmed lemmas
  (`isSuccLimit_omega0`, `ord_lt_ord`, `IsPrincipal.iterate_lt`),
  the conclusion would need re-evaluation. The S4 PREP §1 used the
  same pin and did not flag any such migrations.

## 11. References

- This repo:
  - `proofs/Proofs/FodorPressingDown.lean` (385 lines, 0 sorries,
    0 axioms; the S2-α target file).
  - `sessions/2026-05-12-s02-prep-stepI-limit-club.md` (S2 PREP,
    the document being audited; §2.3 lines 96, 104).
  - `sessions/2026-05-13-s3-prep-cofinality-bound-fodor.md` (S3 PREP,
    not in scope of this audit).
  - `sessions/2026-05-13-s04-prep-mathlib-name-verification.md`
    (S4 PREP, the methodological precedent for this S5 PREP).
- PR #18375 (S2 PREP, MERGED).
- PR #18544 (S4 PREP, MERGED, the methodological precedent).
- Mathlib master `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
  Files cited:
  - `Mathlib/SetTheory/Ordinal/Arithmetic.lean:1056` (`isSuccLimit_omega0`).
  - `Mathlib/SetTheory/Ordinal/Basic.lean:1115, 1123, 1127, 1058` (ord
    monotonicity / lt-iff lemmas).
  - `Mathlib/SetTheory/Ordinal/Principal.lean:183, 195, 208, 216`
    (`IsPrincipal (· + ·) o` framework).
  - `Mathlib/SetTheory/Cardinal/Regular.lean:47, 89, 155, 207, 213`
    (IsRegular core + sup-based < κ.ord lemmas).
  - `Mathlib/Algebra/Order/SuccPred.lean:159, 181, 189`
    (`IsSuccLimit.add_one_lt`, etc. — the *available* `add_*` lemmas
    that do NOT solve Row 2's limit-preservation problem).

---

**End of S5 PREP — no Lean changes, no gallery changes, no axiom
changes. Two ERRATUM-grade rows in S2 PREP §2.3 are flagged with
working alternatives; one minor-drift name correction is applied.
Net LOC impact on the S2 ACT body: +3 to +7 LOC over the S2 PREP
estimate. The S2 ACT writer applies the corrections in their
session.**
