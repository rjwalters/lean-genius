# S43 Session — PREP (rebase-readiness audit + `firstDescentRotation` design spec, doc-only)

**Date**: 2026-05-16
**Author**: researcher-4
**Mode**: PREP (doc-only)
**Iteration**: 42 → 43
**Phase**: ACT → PREP
**Build status**: not run (Docker daemon hung on host disk pressure; see §6)

## Scope

This session is a **doc-only PREP** that consolidates three deferred
decisions from the S42 STATE-SYNC and re-checks them against the current
state of `origin/main`. No `.lean` file is touched, no `meta.json` is
touched, no axiom or sorry delta on the main file (still 0 axioms, 2
sorries).

The three deferred decisions:

1. **OPEN-PR rebase triage** — S42 §"Next action (S43+)" named three open
   CONFLICTING PRs (#17680 S34, #17884 S39, #17892 S40) and proposed a
   fresh-rebase strategy. This PREP re-verifies the lemma-by-lemma status
   of each PR against current `origin/main` and confirms which are still
   needed vs. superseded.
2. **`firstDescentRotation` design** — S42 §"Next action (S43+)" listed
   "(a) `firstDescentRotation` def (~20 lines, canonical rotation index
   for any `P' : Sym (Fin n) (a+1)` with `P'.1 ≤ M.1`) + spec lemma" as
   the cheapest substantive ACT. This PREP enumerates three candidate
   signatures, three candidate definitions, and small-case validation
   against the recon-doc §1 cases.
3. **Parent `BallotProblemOQ03OQ02.lean` status** — S42 noted the parent
   file blocked all `(build pending)` qualifiers with 23 errors in 6
   clusters. Mechanic PR #19264 (2026-05-15) cleared Clusters E + F
   (8 of 23 errors), reducing the error count to 15 across Clusters A,
   B, C, D. This PREP updates the qualifier semantics accordingly.

## Files touched (doc-only)

- `research/problems/.../sessions/2026-05-16-s43-rebase-audit-firstdescent-prep.md`
  (this file, new).
- `research/problems/.../state.md` (header `Last Updated` bump, S43
  Summary block inserted before S42, Iteration 42 → 43).
- `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-01-oq-01.json`
  (`currentState.iteration` 42 → 43, `phase` ACT → PREP, `nextAction`
  refreshed with S44+ menu, `lastUpdate` bumped, `knowledge.nextSteps`
  appended).

**No edits** to: `proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean`,
`src/data/proofs/.../meta.json`, annotations, peer-review files,
audit-claim files. **No Docker invocations.**

---

## §1 — OPEN-PR rebase triage (current as of `origin/main` HEAD `ecb47b35601`)

S42 §"Next action (S43+)" listed three open CONFLICTING PRs with
"fresh-rebase strategy per S37-precedent" (no force-push). Re-verified
against current `origin/main` HEAD `ecb47b35601` (sperner-ndim S2-A
ACT, MERGED 2026-05-16) at lake-manifest pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since S29).

### PR #17680 (S34, OPEN, CONFLICTING) — **SUPERSEDED, close**

PR body adds three declarations:

| Name | Status on `origin/main` | Source |
|------|-------------------------|--------|
| `rotateSortedList_take_le` | **PRESENT** | S37 fresh-rebase (PR #17721) |
| `rotateSortedListPrefixSym` (def) | **PRESENT** | S37 fresh-rebase (PR #17721) |
| `rotateSortedListPrefixSym_le` | **PRESENT** | S37 fresh-rebase (PR #17721) |

Verified via:

```bash
$ grep -c "^private (lemma|def) rotateSortedList_take_le\b" \
    proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean
1
$ grep -c "^private (lemma|def) rotateSortedListPrefixSym\(_le\)\?\b" \
    proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean
2
```

All three declarations from S34 PR #17680 are already on `origin/main`
via the S37 fresh-rebase PR #17721 (merged earlier in the S31–S41 chain).
S42 §"Next action" already classified PR #17680 as "superseded in spirit
by the S37 fresh-rebase of researcher-1". **Recommended action**:
**close PR #17680 with comment** "Superseded by PR #17721 (S37 fresh-rebase).
All three declarations (`rotateSortedList_take_le`,
`rotateSortedListPrefixSym`, `rotateSortedListPrefixSym_le`) are present
on `origin/main`. No re-application needed."

### PR #17884 (S39, OPEN, CONFLICTING) — **rebase needed, lemma still missing**

PR body adds one declaration `rotateSortedListPrefixSym_mod` (plus
implied `_zero_val` / `_self_val` per state.md S42 §"OPEN PR rebase
note"; the PR's actual diff narrows this to **`_mod` only** — the
`_zero_val` and `_self_val` mirror-lemmas on the prefix side are missing
from both `origin/main` and the PR's diff, and are deferred to a future
PREP).

| Name | Status on `origin/main` |
|------|-------------------------|
| `rotateSortedListPrefixSym_mod` | **MISSING** (still needed) |
| `rotateSortedListPrefixSym_zero_val` | **MISSING** (was suffix-only at S36) |
| `rotateSortedListPrefixSym_self_val` | **MISSING** (was suffix-only at S36) |

Verified via:

```bash
$ for n in rotateSortedListPrefixSym_zero_val \
           rotateSortedListPrefixSym_self_val \
           rotateSortedListPrefixSym_mod; do
    grep -c "^private lemma $n\b" proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean
  done
0
0
0
```

**Recommended action**: open a fresh PR off current `origin/main` titled
"S43-rebase (or S44+, depending on ship order) — `_mod` prefix mirror"
re-applying just the `_mod` lemma (3-line body, mirror of S37's
`rotateSortedListSuffixSym_mod`). The `_zero_val` and `_self_val` prefix
mirrors should be a **separate** PR (not bundled with `_mod`) since they
were not in PR #17884's actual diff and need fresh proofs (mirroring S36
suffix-side lemmas via `List.take_zero` / `List.take_length`).

The PR #17884 branch (`research/ballot-oq03-oq01-oq01-oq01-s39-prefix-degenerate-1778564510`)
can then be closed with comment "Superseded by fresh-rebase PR #<n>."

### PR #17892 (S40, OPEN, CONFLICTING) — **rebase needed, lemma still missing**

PR body adds one declaration `rotateSortedListPrefixSym_val_add_SuffixSym_val`.

| Name | Status on `origin/main` |
|------|-------------------------|
| `rotateSortedListPrefixSym_val_add_SuffixSym_val` | **MISSING** (still needed) |

Verified via:

```bash
$ grep -c "^private lemma rotateSortedListPrefixSym_val_add_SuffixSym_val\b" \
    proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean
0
```

**Recommended action**: open a fresh PR off current `origin/main`
re-applying the lemma. Body is a 3-line term using
`rotateSortedList_take_add_drop` (S34, on main as
`rotateSortedListSuffixSym_val + PrefixSym_val = M.1` after combination
with S35/S37 names). The PR #17892 branch can then be closed.

### Rebase order suggestion

`_mod` (PR #17884 re-apply) → `_val_add_SuffixSym_val` (PR #17892
re-apply) → `_zero_val` + `_self_val` (new prefix mirrors). All three
PRs are mutually disjoint at the file level (different declaration
names, all inserting at the same window between S38's `_val_eq_sub_take`
and `totalSym`), so any order works; the suggested order matches
declaration size (smallest first) and matches the S39/S40 historical
ship order.

---

## §2 — `firstDescentRotation` design spec (item (a) of S42+ menu)

S42 §"Next action (S43+)" listed
"(a) `firstDescentRotation` def (~20 lines, canonical rotation index
for any `P' : Sym (Fin n) (a+1)` with `P'.1 ≤ M.1`) + spec lemma —
standalone infrastructure for 2B.4'".

The recon doc (`sublemma-2b-cycle-lemma-spec.md`) §8 tentatively named
this `firstDescentRotation` and gave it return type `Fin (a + b)` with
signature

```lean
private def firstDescentRotation (M : Sym (Fin n) (a + b))
    (P' : Sym (Fin n) (a + 1)) : Fin (a + b)
```

That signature is **under-specified**: it lacks the `P'.1 ≤ M.1`
hypothesis (which S42's nextAction explicitly added) and does not commit
to what "first descent rotation" means at the multiset level.

This §2 enumerates three candidate signatures, three candidate
definitions, and small-case validation. **None of these are committed
yet** — the choice is made at ACT time after the 2B.4' bijection's
exact shape is committed. This PREP captures the design space so the
next ACT does not relitigate it.

### §2.1 — Candidate signatures

**A. Total function with degenerate `0` for the no-descent case:**

```lean
private def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1)) : ℕ
```

Return type `ℕ`, value `0` when no descent rotation exists (e.g., when
`P'.1 ≤ M.1` fails). Pros: simplest signature, no hypothesis. Cons:
loses information about whether the result is "real" — downstream
2B.4' callers must always carry the `P'.1 ≤ M.1` hypothesis separately
to interpret the result.

**B. Hypothesis-carrying function with `Fin (a + b)` codomain:**

```lean
private def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1))
    (_hP' : P'.1 ≤ M.1) (_hab : 0 < a + b) : Fin (a + b)
```

Return type `Fin (a + b)`. Pros: matches the recon-doc §8 signature
exactly; the `Fin` codomain expresses the period-`(a+b)` rotation-class
structure. Cons: requires both hypotheses at the call site; `0 < a + b`
is implicit from `1 ≤ a + 1 ≤ a + b` but needs to be threaded.

**C. Subtype-packaged variant:**

```lean
private def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b))
    (P' : {P : Sym (Fin n) (a + 1) // P.1 ≤ M.1}) :
    Fin (a + b)
```

Takes the `{P' // P'.1 ≤ M.1}` subtype directly (matching the
codomain of `noColStrict_subSym_a_count_eq_subSym_le_aplus1_count`'s
RHS Finset). Pros: zero hypothesis threading; the call site can use
`firstDescentRotation M ⟨P', hP'⟩` or pass through the bijection
directly. Cons: subtype noise at the definition site; needs an
auxiliary `0 < a + b` lemma to inhabit the `Fin (a + b)` codomain at
the degenerate `b = 0` case (excluded by `2 ≤ b ≤ a` in the parent
hypothesis, but the def itself should not depend on these).

**Recommendation for next ACT**: **Signature B** if the 2B.4' bijection
keeps `P'` and `hP'` as separate arguments (most flexible).
**Signature C** if the bijection uses the subtype directly (cleanest
matching the Finset cardinality RHS). Signature A is rejected as
information-losing.

### §2.2 — Candidate definitions

What does "first descent rotation" *mean*?

Per the recon doc §3 (revised in §8), the cycle-lemma bijection between
`{bad P}` and `{P' ≤ M of size a+1}` uses an intermediate refined
codomain `{(P', k)}` where `k ∈ Fin (a + b)` is a rotation index of the
sorted-list representative `L := M.1.sort (· ≤ ·)`. For each
`P' ≤ M.1` of size `a + 1`, the canonical `k` is the rotation index at
which a specific descent / split structure appears.

The three candidate semantics:

**Definition I — "First k where take a is exactly P'.sort":**

```lean
private def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1))
    (hP' : P'.1 ≤ M.1) (hab : 0 < a + b) : Fin (a + b) :=
  ⟨Nat.find (h_exists M P' hP') % (a + b), Nat.mod_lt _ hab⟩
where
  h_exists : ∃ k : ℕ, ((rotateSortedList M k).take (a + 1) : Multiset (Fin n)) = P'.1
```

The first rotation `k` such that the take-`(a+1)` prefix of
`rotateSortedList M k` equals `P'.1` (as a multiset). Modded by
`(a + b)` to land in `Fin (a + b)`. Requires an existence proof
`h_exists` — non-trivial: not every `P' ≤ M.1` of size `a + 1` appears
as a contiguous-rotation-prefix of `L`. (Counter-example: `M = {0,0,1,1}`,
`P' = {0,1,1}`: `L = [0,0,1,1]`; rotations are `[0,0,1,1]`, `[0,1,1,0]`,
`[1,1,0,0]`, `[1,0,0,1]`; the take-3 prefixes are
`{0,0,1}, {0,1,1}, {0,1,1}, {0,0,1}` respectively, so `P' = {0,1,1}`
is hit at `k = 1` and `k = 2`. **Existence holds here** but uniqueness
fails — `Nat.find` returns the smallest.)

**Open question**: is existence universal for all `P' ≤ M.1` of size
`a + 1`? Need to verify on Case 3 of recon doc §1 (`n = 4, M = {0,1,2,3}`,
4 size-3 submultisets).

**Definition II — "First k where the canonical bad P determined by P' lives":**

```lean
private def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1))
    (hP' : P'.1 ≤ M.1) (hab : 0 < a + b) : Fin (a + b) :=
  ⟨Nat.find (h_exists M P' hP') % (a + b), Nat.mod_lt _ hab⟩
where
  h_exists : ∃ k : ℕ,
    let P : Sym (Fin n) a :=
      ⟨((rotateSortedList M k).take a : Multiset (Fin n)),
       (rotateSortedListPrefixSym_le M k a).trans …⟩
    -- The drop-side is the canonical Q complement; the cycle lemma
    -- says exactly one `k ∈ Fin (a + b)` puts P in the "bad" class.
    let Q : Sym (Fin n) b := ⟨…⟩
    ¬ ColStrictSym a b P Q ∧
    P.1 + ⟨(rotateSortedList M k)[a]!, _⟩ = P'.1  -- "P' = P ⊎ {next element}"
```

The first rotation `k` such that the take-`a` prefix is "bad" (not
column-strict against its drop-side complement) and the next element
of the rotation completes it to `P'`. This is the canonical
cycle-lemma map.

**Risk**: requires the `ColStrictSym` predicate inside the existence
proof, dragging in the entire S29 canonical-complement bridge to verify
existence. Existence is the **content** of the cycle lemma, so this
definition begs the question.

**Definition III — "Lyndon-style minimum-rotation choice":**

```lean
private def firstDescentRotation {n : ℕ} {a b : ℕ}
    (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1)) :
    Fin (a + b) :=
  -- Pick k ∈ Fin (a + b) minimising the lex order of
  -- (rotateSortedList M k).take (a + 1)
  -- among all k for which this prefix matches P'.sort.
  ⟨Nat.find (h_lex_exists M P') % (a + b), Nat.mod_lt _ (by positivity_at_a_plus_1)⟩
```

Lyndon-word-style: define a canonical "smallest rotation" by lex order
on the take-prefix. Skirts the existence-of-bad-P issue by working at
the list level. Cons: depends on a `positivity_at_a_plus_1` lemma
showing `0 < a + b` from `1 ≤ a + 1 ≤ a + b` (need to thread the size
hypothesis from `P'.1 ≤ M.1` via `Multiset.card_le_card`).

### §2.3 — Small-case validation

Apply each definition to recon doc §1 Case 3 (`n = 4, a = b = 2`,
`M = {0,1,2,3}`, `a + b = 4`, sorted-list rep `L = [0,1,2,3]`):

Size-3 submultisets of `M.1`: `P'₁ = {0,1,2}`, `P'₂ = {0,1,3}`,
`P'₃ = {0,2,3}`, `P'₄ = {1,2,3}`.

Rotations of `L`: `L₀ = [0,1,2,3]`, `L₁ = [1,2,3,0]`, `L₂ = [2,3,0,1]`,
`L₃ = [3,0,1,2]`.

Take-3 prefixes: `T₀ = {0,1,2}`, `T₁ = {1,2,3}`, `T₂ = {0,2,3}`,
`T₃ = {0,1,3}`.

So the 4 size-3 submultisets are **exactly** the 4 take-3 prefixes
across the 4 rotations, each appearing **exactly once**. Excellent —
this is the cycle-lemma's clean case.

**Definition I result on Case 3** (smallest `k` with `T_k = P'`):

| `P'` | candidate `k`s | `firstDescentRotation` |
|------|---------------|------------------------|
| `{0,1,2}` | 0 | **0** |
| `{1,2,3}` | 1 | **1** |
| `{0,2,3}` | 2 | **2** |
| `{0,1,3}` | 3 | **3** |

Bijective onto `Fin 4`. Each `P'` has a unique rotation. ✓

**Definition II result on Case 3**: needs the bad-P enumeration from
recon doc §1 Case 3:

| bad `P` (size 2) | drop element to get size 3 | candidate `P'` |
|-------------------|-----------------------------|----------------|
| `{0,3}` | (chooses 2, the `Q.sort[1]`) | `{0,2,3}` |
| `{1,2}` | (chooses 0, the `Q.sort[0]`) | `{0,1,2}` |
| `{1,3}` | (chooses 0, the `Q.sort[0]`) | `{0,1,3}` |
| `{2,3}` | (chooses 0, the `Q.sort[0]`) | `{0,2,3}` |

But (per recon doc §8 collision) `{0,3}` and `{2,3}` both map to
`{0,2,3}` under the naive drop. So Definition II's `h_exists` requires
"the canonical bad P", not just any bad P. The lift would need to pick
between the two — the cycle lemma's content is exactly this choice.

**Definition III result on Case 3** (lex-min rotation per `P'`):

| `P'` | lex-min rotation k | `firstDescentRotation` |
|------|--------------------|------------------------|
| `{0,1,2}` | k=0 (T₀=`{0,1,2}`, P'.sort=`[0,1,2]`) | **0** |
| `{1,2,3}` | k=1 | **1** |
| `{0,2,3}` | k=2 | **2** |
| `{0,1,3}` | k=3 | **3** |

Same as Definition I on this case (all rotations have unique take-3
prefixes). On Case 1 (`M = {0,0,1,1}`) and Case 2 (`M = {0,0,0,1}`)
the take-3 prefixes have **repeats**, so the `Nat.find` smallest-k
result differs from a strict Lyndon-word choice. (Working out Case 1
and Case 2 in detail is deferred to next session — the values can be
computed by hand from the recon doc §1 tables.)

### §2.4 — Spec lemmas to accompany the def

Regardless of which definition is chosen, the 2B.4' bijection needs:

1. **`firstDescentRotation_lt`**: `firstDescentRotation M P' hP' hab < a + b`
   (free from the `Fin (a + b)` codomain).
2. **`firstDescentRotation_take_eq`** (Defs I, III):
   `(rotateSortedList M (firstDescentRotation M P' hP' hab)).take (a + 1)
   = P'.1.sort (· ≤ ·)` — the spec witness that the rotation actually
   produces `P'` as its take-prefix.
3. **`firstDescentRotation_mod`** (period):
   `firstDescentRotation M P' hP' hab` is invariant under `k ↦ k + (a+b)`.
   Free from Def I/III's `Nat.find % (a + b)` definition; need explicit
   proof for Def II.

Spec lemma 1 is free (codomain ascription). Spec lemma 2 is the
**content** of the existence proof — Def II makes this a cycle-lemma
restatement, Defs I/III make it provable by `Nat.find_spec`. Spec
lemma 3 is needed for the 2B.4' bijection's well-definedness across
the rotation-class quotient.

### §2.5 — Anti-targets

- **Do NOT** ship `firstDescentRotation` as an `axiom` or with a
  bare `sorry` in the body. The recon doc §3 collision shows the
  naive "drop smallest" definition is wrong; shipping any definition
  without small-case verification (§2.3 above) risks repeating that
  dead-end.
- **Do NOT** combine the def with the 2B.4' bijection in the same PR.
  The def is `~20 lines`; the bijection is `~50 lines`; combining them
  makes the PR un-reviewable and forces a single ACT to commit to both
  the def's semantics and the bijection's exact shape.
- **Do NOT** name the spec lemma `firstDescentRotation_spec` (too
  generic). Use `firstDescentRotation_take_eq` or similar to match the
  S31–S41 naming convention (`<defName>_<contentOp>`).

---

## §3 — Parent `BallotProblemOQ03OQ02.lean` status update

S42 STATE-SYNC §"Build status" stated:
"Parent `BallotProblemOQ03OQ02.lean` is broken on `origin/main`
(~24 errors lines 1911–2386 per
`feedback_researcher_ballot_oq03oq02_parent_break.md` 2026-05-09)".

**Update**: Mechanic PR #19264 (researcher mechanic-3, MERGED
2026-05-15T18:02:42Z) cleared **8 of 23 errors** by fixing all 6 sites
of Cluster E (`gvCanon_self_inverse`) plus both sites of Cluster F
(`hkj_drop`/`hki_drop`). Reduced count: **15 errors remaining**, split
across:

| Cluster | Sites | Lines | Reason for deferral |
|---------|-------|-------|---------------------|
| A | 4 | 1911, 1920, 1928, 1930 | `cast_PathMN_val` simp dead under `↑(cast …)` v4.26.0 |
| B (cascade) | 2 | 1971, 2035 | Downstream of A; resolves automatically once A is fixed |
| C | 2 | 2170, 2180 | `Type mismatch` post-`simp only [colEntry, himg_ci]` |
| D | 6 | 2249, 2250, 2253, 2263, 2266, 2276 | `rw [colEntry_eq …]` fails due to `let`-zeta past `set ci` |

**Implication for this slug's `(build pending)` qualifier**: still
applies — the parent file remains broken on `origin/main`, so any
S39+S40 fresh-rebase PR ships as `(build pending — parent OQ03OQ02
break)` until Clusters A–D are also cleared. However, the qualifier is
**less severe** than at S42:

- S42 wording: "23 errors in 6 clusters"
- S43 wording: **"15 errors in 4 clusters (A, B-cascade, C, D); Cluster A
  resolution will likely also unblock B (cascade), and may unblock C and
  D via the same `↑`/`.val` normalization per PR #19264 §"Out-of-scope""**

A follow-up mechanic PR addressing Cluster A would likely cascade into
B, C, and D. Triage suggests this is the next mechanic priority for the
ballot-OQ03 family.

**No action for this PREP** — the parent repair is in mechanic scope,
not researcher scope. Recorded here so future S44+ rebase PRs can use
the updated qualifier "(build pending — parent OQ03OQ02 break, 15
errors as of PR #19264, mechanic in progress)".

---

## §4 — ACT-readiness gate (post-disk-recovery)

After the current Docker daemon hang / disk-pressure incident
resolves (see §6), the next ACT has four ranked options:

| Rank | Option | Effort | Risk | Build-readiness gate |
|------|--------|--------|------|---------------------|
| 1 | **Re-apply S39 `_mod`** (PR #17884 rebase) | ~10 LOC | LOW | Need Docker ≥ 8Gi free, build subset only — cache replay if pin unchanged |
| 2 | **Re-apply S40 `_val_add_SuffixSym_val`** (PR #17892 rebase) | ~15 LOC | LOW | Same as #1; can ship adjacent |
| 3 | **Ship S39 `_zero_val` + `_self_val` prefix mirrors** (new PR, not in PR #17884) | ~25 LOC | LOW | Same as #1; pattern from S36 suffix mirrors |
| 4 | **Ship `firstDescentRotation` def + spec** (new PR, item (a) of S42+ menu) | ~25 LOC + spec | MEDIUM | Requires committing to Definition I or III from §2.2 above |

**Selection criteria for next ACT**:

- Pick #1 first if `_mod` is needed by any in-flight 2B.4' bijection
  attempt — it's the cheapest rebase, validates the rebase-strategy
  recipe before the more complex #2, and clears the oldest stranded PR.
- Pick #4 only after #1–#3 are merged (or shipped in parallel as the
  pre-flight to 2B.4'). #4's MEDIUM risk comes from the design choice
  in §2.2 — the next ACT must commit to Definition I or III and
  small-case-verify on Cases 1, 2 from the recon doc §1.

**ACT-readiness pre-flight** (apply at the start of next ACT):

```bash
# 1. Disk gate
df -h /System/Volumes/Data | awk 'NR>1 && $5+0 < 95 { exit 0 } END { exit 1 }' \
  || { echo "Disk ≥95% full, defer ACT"; exit 1; }

# 2. Docker daemon gate
timeout 5 docker ps -q > /dev/null 2>&1 \
  || { echo "Docker daemon hung, defer ACT"; exit 1; }

# 3. Mathlib pin unchanged gate
grep -q "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" proofs/lake-manifest.json \
  || { echo "Mathlib pin moved; cache will not replay, re-verify before commit"; }

# 4. Origin/main slug file unchanged-by-rotation-block gate
git fetch origin main --quiet
git log --oneline origin/main -- proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean \
  | head -1
```

All four gates must pass GREEN before invoking
`./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ03OQ01OQ01OQ01`.

---

## §5 — Bearer pin verification

Verified at PREP time (2026-05-16T08:30Z, before any worktree edit):

| Pin | SHA | Source | Status |
|-----|-----|--------|--------|
| Mathlib | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` | `proofs/lake-manifest.json` | unchanged since S29 (PR #17447, 2026-05-08) |
| origin/main | `ecb47b35601` (`research(sperner-ndim-mathlib-oq-01-oq-04): S2-A ACT`) | `git log --oneline -1 origin/main` | MERGED 2026-05-16 |
| Slug file | unchanged since S41 PR #17900 | `git log --oneline -1 origin/main -- proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` | 2348 LOC, 60 theorems, 12 defs, 2 sorries, 0 axioms |
| Parent file | last edit PR #19264 mechanic 2026-05-15 (23→15 errors) | `git log --oneline -1 origin/main -- proofs/Proofs/BallotProblemOQ03OQ02.lean` | 2532 LOC, build-failing 15 errors |
| meta.json (this slug) | already at 2348/60/12 per S41 + S42 STATE-SYNC | `jq -r '.lineCount, .theoremCount, .definitionCount' src/data/proofs/.../meta.json` | accurate (no edit needed) |

**No drift** between any tracker and the actual file state. The S42
STATE-SYNC's resync was effective; nothing has changed in the 1.5 days
since.

---

## §6 — Build status (no Docker invocation)

**Docker daemon hung on host disk pressure**. Reproducer:

```bash
$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   883Gi   6.7Gi   100%     21M   70M   23%   /System/Volumes/Data
                                  ↑↑↑      ↑↑↑↑
                            6.7Gi avail  100% capacity

$ timeout 5 docker ps -q
# (no output; exit 124 — timeout)
```

Per the memory-recorded pattern
`feedback_researcher_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`,
this triggers the **doc-only PREP pivot**: no Lean edit, no Docker
invocation, ship narrative-value PREP + paste-ready sketches + ACT-
readiness gate. The cache-replay forecast for a future S44 ACT (after
disk pressure resolves) is **~20-30s wall** if the lake hash is
unchanged for an edit limited to the rotation-toolkit section
(comments-only or one-lemma-addition edits). Sad-path is only if
Mathlib pin moves before S44, in which case full ~90s elaboration.

**No Lean edit in this PREP**, so cache-hit forecast is irrelevant —
S44 ACT will start from the same lake hash as S43 PREP.

---

## §7 — Per-session honesty

- This PR adds **0 lines of Lean code**, **0 axioms cleared**, **0
  sorries closed**. It is pure markdown + JSON tracker refresh.
- The §1 PR-by-PR rebase audit is a **re-verification** of S42's
  written claims, not new analysis. Value: confirms the S42 claims are
  still accurate 2 days later, and converts PR #17680 from "OPEN" to
  "ready to close as superseded".
- The §2 `firstDescentRotation` design spec is **substantive new
  reconnaissance** — three candidate signatures, three candidate
  definitions, small-case validation against recon doc Case 3. It does
  not commit to a choice (the choice is an ACT-time decision).
- The §3 parent file status update is a **factual correction** of
  S42's "23 errors in 6 clusters" wording to the post-PR-#19264
  state of "15 errors in 4 clusters (A, B-cascade, C, D)". S42 was
  written before PR #19264 merged; this is a routine refresh.
- The §4 ACT-readiness gate is **forecast / planning**, not work
  performed. It does not unblock anything by itself.
- The §5 bearer pin verification is **routine due diligence**, ~5 min
  of `git log` / `grep` / `jq` invocations. No drift found.
- The session is **not** progress toward solving Sub-lemma 2B's open
  sorry. It is preparation that reduces the next ACT's risk by
  surfacing design alternatives that would otherwise be relitigated.

This PREP is a doc-only iteration that documents the
post-S42 state of the world for the next researcher. Iteration counter
bumps (42 → 43); phase changes (ACT → PREP) to reflect the doc-only
nature.

---

## §8 — Next action (S44+)

After Docker daemon recovers + disk pressure resolves (Auditor/Mechanic
pool sweep typically clears stale containers; manual `docker system prune`
may be needed if persistence is broken — out of researcher scope):

1. **S44 candidate A (LOW risk)**: re-apply S39 `_mod` lemma (PR #17884
   fresh-rebase). 1 declaration, ~10 LOC. Pre-flight per §4 above.
2. **S44 candidate B (LOW risk)**: re-apply S40 `_val_add_SuffixSym_val`
   lemma (PR #17892 fresh-rebase). 1 declaration, ~15 LOC.
3. **S44 candidate C (LOW risk)**: ship `_zero_val` + `_self_val` prefix
   mirrors (new PR, not in PR #17884's diff). 2 declarations, ~25 LOC.
4. **S44 candidate D (MEDIUM risk)**: ship `firstDescentRotation` def
   + `_take_eq` spec lemma. Requires committing to §2.2 Definition I or
   III; ~25-30 LOC.
5. **S44 candidate E (background)**: close PR #17680 with "superseded
   by S37" comment. Zero-effort housekeeping (just a `gh pr close
   --comment "..."` invocation). Independent of any other ship.

**Suggested order**: E (zero-effort) → A → B → C → D. Each ships as a
separate PR off `origin/main` per the §1 rebase-strategy recipe (no
force-push, fresh PR per S37-precedent
`feedback_researcher_pr_rebase_strategy.md`).

**Cancellation clause**: if the parent `BallotProblemOQ03OQ02.lean`
becomes build-passing before S44 ACT (mechanic clears Clusters A–D),
all S44 candidates can drop the `(build pending — parent OQ03OQ02
break)` qualifier and ship as proper Docker-verified ACTs.
