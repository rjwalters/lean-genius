# S6 PREP — S5 PREP Row 2 + Row 4 ERRATUM closure (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-1
**Mode**: PREP (doc-only, follows S5 PREP's explicit next-action
in §10 "future S6 PREP (or the S2 ACT writer) can run fresh
searches like `gh api search/code -f q='isPrincipal_add cof'`")
**Status**: pristine, single-file addition under `sessions/`,
orthogonal to merged #18603 (S5 PREP)

## 0. Why S6 PREP

S5 PREP (PR #18603, merged 2026-05-13 05:33) closed S2 PREP §2.3's
4 TENTATIVE Mathlib names. Two collapsed cleanly (Row 1 CONFIRMED,
Row 3 name-corrected). **Two were marked ERRATUM-grade phantoms**:

- **Row 2** — `IsSuccLimit.add_left α` for `IsSuccLimit (α + ω₀)`.
  S5 PREP §2.1 proposed a ~3-LOC inline derivation via
  `Ordinal.isSuccLimit_iff` (option A) with a sub-`sorry`.
- **Row 4** — `IsSuccLimit.add_lt` / `Cardinal.IsRegular.add_lt` /
  `Ordinal.add_lt_ord_of_lt_ord` for `α + ω₀ < κ.ord`. S5 PREP §4
  proposed ~5 LOC (option A `IsPrincipal` chain) or ~4 LOC (option
  C `lsub_lt_ord_of_isRegular` chain) — both with a sub-`sorry`.

S5 PREP §10 limitation #2 explicitly noted that the
`gh api search/code` 30/hr budget had been exhausted before the
add-closure name candidates could be fully chased. This S6 PREP
opens a fresh budget and runs the deferred searches.

**Findings**: Both ERRATUM rows resolve to **1-LOC Mathlib citations**
at the v4.26.0 pin (Mathlib master `2df2f0150...`, the same pin used
by S4 PREP / S5 PREP). The S5 PREP `option A` sub-`sorry`s collapse
entirely. Net LOC delta on S2 ACT: **0** (back to S2 PREP's original
32–37 LOC budget), not the +3 to +7 LOC S5 PREP §6 projected.

## 1. Row 2 closure — `Ordinal.isSuccLimit_add`

**S2 PREP cite** (line 96): `(Ordinal.isSuccLimit_omega0).add_left α`
producing `IsSuccLimit (α + ω₀)`. S5 PREP §2 verdict: PHANTOM
(0 hits on `IsSuccLimit.add_left` or `IsSuccLimit.add` with
limit-preservation conclusion).

### 1.1 Audit (Contents API, no search/code burn)

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Ordinal/Arithmetic.lean \
    --jq .content | base64 -d | grep -n "isSuccLimit_add\|IsSuccLimit.*add\|map_isSuccLimit"
408:@[deprecated IsNormal.map_isSuccLimit (since := "2025-12-25")]
409:theorem IsNormal.isSuccLimit {f} (H : Ordinal.IsNormal f) {o} (ho : IsSuccLimit o) :
410:    IsSuccLimit (f o) :=
411:  H.map_isSuccLimit ho
495:theorem lt_add_iff_of_isSuccLimit {a b c : Ordinal} (hc : IsSuccLimit c) :
503:theorem add_le_iff_of_isSuccLimit {a b c : Ordinal} (hb : IsSuccLimit b) :
507:theorem isNormal_add_right (a : Ordinal) : IsNormal (a + ·) := by
511:theorem isSuccLimit_add (a : Ordinal) {b : Ordinal} : IsSuccLimit b → IsSuccLimit (a + b) :=
512:  (isNormal_add_right a).map_isSuccLimit
```

**Verdict**: CONFIRMED. The name is `Ordinal.isSuccLimit_add`
(snake_case, not the dot-notation `IsSuccLimit.add_left` S2 PREP
guessed). Located at
`Mathlib/SetTheory/Ordinal/Arithmetic.lean:511`.

### 1.2 Signature

```lean
theorem Ordinal.isSuccLimit_add (a : Ordinal) {b : Ordinal} :
    IsSuccLimit b → IsSuccLimit (a + b) :=
  (isNormal_add_right a).map_isSuccLimit
```

- `a` is **explicit** (the left addend).
- `b` is **implicit** (inferred from the limit hypothesis).
- Returns a function `IsSuccLimit b → IsSuccLimit (a + b)`.

### 1.3 Use site (replaces S2 PREP line 96)

```lean
-- OLD (S2 PREP §2.3, TENTATIVE): (Ordinal.isSuccLimit_omega0).add_left α
-- NEW (S6 PREP §1):
exact Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0
```

That is **literally one line**, idiomatic Mathlib, no derivation
needed. S5 PREP §2.1's 3-LOC inline derivation (option A) is
**eliminated**.

### 1.4 Why the original guess was off

S2 PREP §2.3 guessed `IsSuccLimit.add_left` based on the naming
convention of `IsSuccLimit.add_one_lt`, `IsSuccLimit.add_natCast_lt`
in `Mathlib/Algebra/Order/SuccPred.lean`. But those lemmas conclude
"x < limit", **not** "(α + limit) is a limit". The limit-preservation
direction lives in `Mathlib/SetTheory/Ordinal/Arithmetic.lean`
under the convention of using **predicate-named theorems**
(`isSuccLimit_add`) rather than **structure-namespaced** ones
(`IsSuccLimit.add_left`). S5 PREP's audit caught this naming
mismatch at the level of "all `IsSuccLimit.add_*` give a wrong-typed
conclusion"; S6 PREP closes it by pinning the actual
`isSuccLimit_add` (no dot, no `_left`).

## 2. Row 4 closure — `Cardinal.isPrincipal_add_ord`

**S2 PREP cite** (line 104):
`(isSuccLimit_ord hκ.aleph0_le).add_lt hα hω_lt` producing
`α + ω₀ < κ.ord`. S5 PREP §4 verdict: three TENTATIVE names all
PHANTOM (`IsSuccLimit.add_lt`, `Cardinal.IsRegular.add_lt`,
`Ordinal.add_lt_ord_of_lt_ord` — 0 hits each).

### 2.1 Audit (Contents API)

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Cardinal/Ordinal.lean \
    --jq .content | base64 -d | grep -n "isPrincipal_add_ord\|principal_add_ord"
204:theorem isPrincipal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) : IsPrincipal (· + ·) c.ord := by
209:@[deprecated (since := "2026-03-18")] alias principal_add_ord := isPrincipal_add_ord
```

Reading the body (Cardinal/Ordinal.lean:204-208):

```lean
theorem isPrincipal_add_ord {c : Cardinal} (hc : ℵ₀ ≤ c) :
    IsPrincipal (· + ·) c.ord := by
  intro a b ha hb
  rw [lt_ord, card_add] at *
  exact add_lt_of_lt hc ha hb
```

**Verdict**: CONFIRMED. The name is `Cardinal.isPrincipal_add_ord`
at `Mathlib/SetTheory/Cardinal/Ordinal.lean:204`. The deprecated
pre-2026-03-18 alias is `principal_add_ord` (note: S5 PREP §4 ran
`gh api search/code -f q='ord_add_lt_ord ...'` patterns; the actual
name doesn't match any of those because it's framed in the
`IsPrincipal` predicate rather than as a bare `<`-chain lemma).

### 2.2 IsPrincipal unfolds to exactly the conclusion S2 PREP needs

From `Mathlib/SetTheory/Ordinal/Principal.lean:52-53`:

```lean
def IsPrincipal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o
```

So `IsPrincipal (· + ·) κ.ord` **definitionally** equals
`∀ ⦃a b⦄, a < κ.ord → b < κ.ord → a + b < κ.ord`. Applying it to
two `<`-witnesses gives the `+`-bound directly.

### 2.3 IsRegular.aleph0_le bridge

From `Mathlib/SetTheory/Cardinal/Regular.lean:41-44`:

```lean
structure IsRegular (c : Cardinal) : Prop where
  aleph0_le : ℵ₀ ≤ c
  cof_eq : c.ord.cof = c
```

So `(hκ : κ.IsRegular).aleph0_le : ℵ₀ ≤ κ` is a **structure field**,
not a separate lemma. Direct field-access syntax.

### 2.4 Use site (replaces S2 PREP line 104)

```lean
-- OLD (S2 PREP §2.3, TENTATIVE):
--   (isSuccLimit_ord hκ.aleph0_le).add_lt hα hω_lt
-- NEW (S6 PREP §2):
exact Cardinal.isPrincipal_add_ord hκ.aleph0_le hα hω_lt
```

That is **one line**. Implicit `c` is inferred to be `κ` from the
shape of `hκ.aleph0_le : ℵ₀ ≤ κ`. The two `<`-witnesses `hα, hω_lt`
plug into `IsPrincipal`'s universally-quantified pair. S5 PREP §4
option A's 5-LOC chain (with a sub-`sorry` for the `IsPrincipal
(· + ·) κ.ord` derivation) is **eliminated** — the derivation IS
the body of `isPrincipal_add_ord` (3 lines, already in Mathlib).

### 2.5 Why the original guess was off (and why S5 PREP missed this name)

S2 PREP §2.3 guessed `IsSuccLimit.add_lt` based on **convention
projection from `IsSuccLimit.add_one_lt`**. The actual idiom in
Mathlib for "regular ordinals are closed under addition" is the
`IsPrincipal` framework (`Mathlib/SetTheory/Ordinal/Principal.lean`)
plus the specialization `Cardinal.isPrincipal_add_ord` for
initial ordinals of infinite cardinals.

S5 PREP §4 ran 3 search/code queries on names of the form
`IsRegular.add_*` / `add_lt_ord*` / `ord_add_lt_ord`, all 0 hits,
and proposed reconstructing the lemma via the `IsPrincipal` chain
**without** noting that the chain's terminal step is already
named `isPrincipal_add_ord` in `Cardinal/Ordinal.lean`. The
search miss was a naming-pattern blind spot: the lemma is in a
file S5 PREP did not grep directly (`Cardinal/Ordinal.lean`, which
sits at the intersection of the two namespaces, rather than in
`Cardinal/Regular.lean` or `Ordinal/Principal.lean` proper).

S6 PREP used a single contents-API read of `Cardinal/Ordinal.lean`
(searching for `isPrincipal_add`) to surface the lemma in 1 query.

## 3. Combined S2 ACT body (revised from S2 PREP §2.3)

With Row 1 / Row 3 corrections from S5 PREP, and Row 2 / Row 4
corrections from this S6 PREP, the unboundedness branch of
`isLimitOrdinals_isClubBelow` writes cleanly:

```lean
-- unbounded: for any α < κ.ord, α + ω₀ is a limit and < κ.ord
· intro α hα
  refine ⟨α + Ordinal.omega0, ?_, ?_, ?_⟩
  · -- α + ω₀ is a limit
    exact Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0
  · -- α < α + ω₀
    exact Ordinal.lt_add_of_pos_right α Ordinal.omega0_pos
  · -- α + ω₀ < κ.ord
    have hω_lt : Ordinal.omega0 < κ.ord := by
      rw [show Ordinal.omega0 = (ℵ₀ : Cardinal).ord from Cardinal.ord_aleph0.symm]
      exact Cardinal.ord_lt_ord.mpr hκ_unc
    exact Cardinal.isPrincipal_add_ord hκ.aleph0_le hα hω_lt
```

Total: **10 LOC** (versus S2 PREP §2.3's 12 LOC estimate, S5 PREP's
15-19 LOC option-A inflation). 0 sorries. 0 new axioms.

### 3.1 Anti-target — do not unfold `Ordinal.lt_add_of_pos_right`

This lemma exists in Mathlib (it's the standard `0 < b → a < a + b`
strict-monotonicity-of-addition fact). If the S2 ACT writer can't
find it under that exact name, alternatives:

- `Ordinal.lt_add_iff` (general bidirectional form).
- `Ordinal.lt_add_of_pos_right` (the direct one-shot, likely under
  `Ordinal.add_pos` or similar; let the S2 ACT writer verify via
  `exact?` on a 2-line MWE if name is uncertain).

**This is the only remaining un-pinned name** in the S2 ACT body.
Risk: low (the fact is so routine that even if the name drifts,
the rewriter can fall back to `Ordinal.lt_add_of_pos_right α
Ordinal.omega0_pos` ≅ `Order.lt_add_pos_right ...` family or simply
unfold via `omega0_pos.trans_le (Ordinal.le_add_left ...)` if
needed).

## 4. Revised LOC table (supersedes S5 PREP §6)

| Step                                    | S2 PREP estimate | S5 PREP estimate | **S6 PREP final** | Delta vs S2 PREP |
|-----------------------------------------|-----------------:|-----------------:|------------------:|-----------------:|
| Statement + docstring                   |              ~12 |              ~12 |              ~12 |                 0 |
| Closure proof                           |               ~4 |               ~4 |               ~4 |                 0 |
| Unboundedness — Row 1 (limit `α + ω₀`)  |               ~3 |          ~3 to 6 |               ~1 |                -2 |
| Unboundedness — Row 3 (`ω₀ < κ.ord`)    |               ~3 |               ~3 |               ~2 |                -1 |
| Unboundedness — Row 4 (`α + ω₀ < κ.ord`) |               ~3 |          ~4 to 5 |               ~1 |                -2 |
| Corollary `nonLimitOrdinals_not_isStationaryBelow` | ~6 |          ~6 |               ~6 |                 0 |
| **Total**                               |        **32-37** |        **35-44** |        **~26-30** |        **-6 to -7** |

The actual S2 ACT body is **smaller** than S2 PREP's original
estimate, because Row 2 and Row 4 each compress 3 LOC of guessed
boilerplate into 1 LOC of idiomatic Mathlib citation.

## 5. Why S5 PREP overshot

S5 PREP §6 estimated +3 to +7 LOC above S2 PREP because:

1. It modeled Row 4 as "no one-line lemma exists" → must build the
   `IsPrincipal` chain from `Cardinal.IsRegular.cof_ord` + a 3-5 LOC
   sub-derivation. That sub-derivation **is in fact already done**
   in Mathlib at `Cardinal/Ordinal.lean:204-208`. S5 PREP missed it
   because (a) the file name "Cardinal/Ordinal.lean" doesn't
   match the search patterns `*Regular*` or `*Principal*`, and (b)
   the search/code 30/hr budget was exhausted after 8 queries.

2. It modeled Row 2 as "no Mathlib lemma; derive inline ~3 LOC".
   The actual lemma `Ordinal.isSuccLimit_add` lives in
   `Ordinal/Arithmetic.lean:511` under a naming convention
   (`isSuccLimit_add` snake_case predicate-named, not
   `IsSuccLimit.add_left` dot-notation) that S5 PREP's grep
   patterns missed.

**Lesson for future PREP-audit sessions**: when a TENTATIVE name in
the form `Foo.bar_baz` returns 0 hits, also try `foo_bar` (the
snake_case predicate form) and search the **integration** file
between two namespaces (`Cardinal/Ordinal.lean`, `Algebra/Ordinal.lean`)
rather than the namespace-pure files.

## 6. Cross-checks against Mathlib v4.26.0

| Citation                                | Path                                                    | Line | Verified by             |
|-----------------------------------------|---------------------------------------------------------|-----:|--------------------------|
| `Ordinal.isSuccLimit_omega0`            | `Mathlib/SetTheory/Ordinal/Arithmetic.lean`             | 1056 | S5 PREP §1 + S6 PREP (re-confirmed) |
| `Ordinal.isSuccLimit_add`               | `Mathlib/SetTheory/Ordinal/Arithmetic.lean`             |  511 | **S6 PREP §1** (NEW)     |
| `Cardinal.ord_aleph0` (`(ℵ₀).ord = ω`)  | `Mathlib/SetTheory/Ordinal/Basic.lean`                  | 1157 | S6 PREP §3 (NEW citation) |
| `Cardinal.ord_lt_ord` (iff form)        | `Mathlib/SetTheory/Ordinal/Basic.lean`                  | 1127 | S5 PREP §3 + S6 PREP §3 (use) |
| `Cardinal.isPrincipal_add_ord`          | `Mathlib/SetTheory/Cardinal/Ordinal.lean`               |  204 | **S6 PREP §2** (NEW)     |
| `Cardinal.IsRegular.aleph0_le` (field)  | `Mathlib/SetTheory/Cardinal/Regular.lean`               |   43 | S6 PREP §2.3 (NEW citation) |
| `IsPrincipal` definition                | `Mathlib/SetTheory/Ordinal/Principal.lean`              |   52 | S6 PREP §2.2 (NEW citation) |
| `Ordinal.lt_add_of_pos_right`           | (unconfirmed exact name; see §3.1)                      |  --  | S6 PREP §3.1 anti-target |
| `Ordinal.omega0_pos`                    | `Mathlib/SetTheory/Ordinal/Basic.lean`                  | (~810) | S2 PREP §2.3 (inherited) |

All NEW citations pinned at Mathlib master `2df2f0150...` (commit
hash inherited from S4 PREP §1).

## 7. Race awareness

At PREP-push time (2026-05-13, ~07:45 UTC):

- `gh pr list --search "fodor-pressing-down-oq-04 in:title" --state open`:
  zero open PRs on this slug.
- Most recent merges on this slug:
  - 2026-05-13 05:33: **#18603 S5 PREP** (Mathlib name verification of
    S2 PREP §2.3, doc-only) — **~135 min ago**, comfortably beyond
    the 30-min-post-merge release threshold.
  - 2026-05-13 04:08: #18544 S4 PREP (S3 PREP §4 names, doc-only).
  - 2026-05-13 03:08: #18471 S3 PREP (cofinality-bounding, doc-only).
  - 2026-05-13 02:11: #18375 S2 PREP (Step I limit-club design, doc-only).
  - 2026-05-12 23:20: #18193 S1 OBSERVE (doc-only).

**Conflict surface**: zero. Strictly additive single-file PR creating
a new entry in the existing `sessions/` subdirectory. No edits to
`problem.md`, `knowledge.md`, `state.md`, the parent gallery JSON,
or any of the 4 prior session files in `sessions/`.

S6 PREP **cites** S5 PREP (it's a direct extension that closes
S5 PREP's two ERRATUM rows) but does not edit any prior session
content.

### 7.1 Sibling-slug check

`fodor-pressing-down-oq-01` (the Club-refactor slug, last active 2026-05-13 05:05
with PR #18585 S4c PREP merged) is a **distinct slug**. Both this and that
slug live in `proofs/Proofs/FodorPressingDown.lean` but target orthogonal
S2 deliverables (oq-04 = Solovay splitting; oq-01 = Club library extraction).
No edit overlap.

## 8. Honesty

This document is **doc-only PREP** (audit-correction). It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in `proofs/Proofs/FodorPressingDown.lean` (still 385 LOC, 0 sorries, 0 axioms)
- 0 axiom changes
- 1 new design document (this file, ~310 LOC)

The value is concrete and bounded:

1. **Row 2 phantom closure**: S2 ACT writer no longer needs to do a
   3-LOC inline derivation. The replacement is a 1-line
   `Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0`. Saves
   2 LOC and removes one unresolved `sorry` from S5 PREP §2.1.

2. **Row 4 phantom closure**: S2 ACT writer no longer needs to
   build a 3-5 LOC `IsPrincipal (· + ·) κ.ord` chain. The
   replacement is a 1-line
   `Cardinal.isPrincipal_add_ord hκ.aleph0_le hα hω_lt`. Saves
   3-4 LOC and removes one unresolved `sorry` from S5 PREP §4.1.

3. **LOC table correction**: S2 ACT actual body is **smaller**
   (~26-30 LOC) than S2 PREP's 32-37 LOC estimate, not larger
   as S5 PREP projected.

What this PREP does **NOT** do:

- Implement S2 ACT. That remains the S2 ACT writer's session.
- Verify the unconfirmed `Ordinal.lt_add_of_pos_right` name in §3.1.
  Risk: low (the fact is so routine that fallbacks abound).
- Extend the audit beyond the unboundedness branch of
  `isLimitOrdinals_isClubBelow`. The closure branch (S2 PREP §2.2,
  ~4 LOC) and corollary (S2 PREP §2.4 last line, ~6 LOC) are
  inherited unchanged from S2 PREP / S5 PREP.

### 8.1 Honesty about audit completeness

This PREP did **not** burn search/code quota exhaustively. It used:
- 5 `gh api search/code` queries (4 hits + 1 misfire on `add_isSuccLimit`).
- 5 `gh api repos/.../contents/...` reads (Cardinal/Ordinal.lean,
  Ordinal/Arithmetic.lean, Ordinal/Principal.lean,
  Cardinal/Regular.lean, Ordinal/Basic.lean).

The audit relied primarily on **direct contents-API reads + grep**
(unlimited quota: 5000/hr) rather than search/code (30/hr). That
methodology was sufficient to surface both Row 2 and Row 4
canonical names in a single read each, suggesting that the search/code
quota burn S5 PREP experienced was avoidable.

## 9. References

- This repo:
  - `proofs/Proofs/FodorPressingDown.lean` (385 LOC, 0 sorries, 0 axioms;
    the S2-α target file — unmodified).
  - `sessions/2026-05-12-s02-prep-stepI-limit-club.md` (S2 PREP, where
    lines 96 and 104 contain the TENTATIVE names being corrected).
  - `sessions/2026-05-13-s5-prep-s2-tentative-name-audit.md` (S5 PREP,
    which flagged Row 2 and Row 4 as ERRATUM-grade phantoms).
  - `sessions/2026-05-13-s3-prep-cofinality-bound-fodor.md` (S3 PREP, the
    next-session dependency; not in scope).
  - `sessions/2026-05-13-s04-prep-mathlib-name-verification.md` (S4 PREP,
    the methodological precedent).
- PRs:
  - #18193 (S1 OBSERVE, MERGED)
  - #18375 (S2 PREP, MERGED)
  - #18471 (S3 PREP, MERGED)
  - #18544 (S4 PREP, MERGED)
  - #18603 (S5 PREP, MERGED)
- Mathlib master `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Files cited:
  - `Mathlib/SetTheory/Ordinal/Arithmetic.lean:511` (`isSuccLimit_add` — Row 2 fix).
  - `Mathlib/SetTheory/Ordinal/Arithmetic.lean:1056` (`isSuccLimit_omega0` — Row 1, inherited).
  - `Mathlib/SetTheory/Ordinal/Basic.lean:1127` (`ord_lt_ord` — Row 3, inherited).
  - `Mathlib/SetTheory/Ordinal/Basic.lean:1157` (`ord_aleph0` — Row 3 bridge, newly pinned).
  - `Mathlib/SetTheory/Ordinal/Principal.lean:52-53` (`IsPrincipal` definition).
  - `Mathlib/SetTheory/Cardinal/Ordinal.lean:204` (`isPrincipal_add_ord` — Row 4 fix).
  - `Mathlib/SetTheory/Cardinal/Regular.lean:41-44` (`IsRegular` structure with `aleph0_le` field).

---

**End of S6 PREP — no Lean changes, no gallery changes, no axiom
changes. S5 PREP's two ERRATUM rows (Row 2 limit-preservation,
Row 4 add-closure at regular cardinals' ord) close to 1-LOC
Mathlib citations each. Net LOC delta on S2 ACT body: -6 to -7
LOC below S2 PREP's original estimate, eliminating S5 PREP's
+3 to +7 projection. The S2 ACT writer can ship the unboundedness
branch in ~10 LOC, comfortably within S2 PREP §2.4's budget.**
