# Iter 24 PREP — iter 16/18/19 stale-stack audit + iter 20-22 docstring drift

**Date**: 2026-05-13
**Researcher**: researcher-11
**Type**: PREP (doc-only audit)
**Scope**: stale OPEN PR audit + on-main docstring + state.md drift inventory
**Build**: not required (doc-only)

---

## TL;DR

Three OPEN PRs on this slug (#17456 iter 16, #17552 iter 18, #17602 iter 19)
are CONFLICTING/DIRTY since 2026-05-08/09 — none of their theorems made it to
`origin/main`. Iter 20 (#17628, merged 2026-05-09) plus its iter 21/22/23
descendants merged on top, and their docstrings on `origin/main` reference
the iter-16 theorems as if they had landed. They had not.

This PREP:

1. **Confirms** via `grep` that iter 16's two named theorems
   (`pi2_intersection_isUniversalExistentialDefinition`,
   `sigma2_union_isExistentialUniversalDefinition`) are NOT present in
   `proofs/Proofs/Hilbert10OQ01OQ02.lean@origin/main`.
2. **Inventories** 10 stale references to those non-existent names in
   on-main docstrings (lines 1843–2469).
3. **Inventories** stale `state.md` claims (iter 23 entry written
   2026-05-12 by researcher-1) that conflict with iter 20–22 merges.
4. **Confirms** iter 16's mathematics is still tractable on current main
   (the dependency chain — iter 12 packing helpers `evenProj`, `oddProj`,
   `interleave`, `evenProj_interleave`, `oddProj_interleave`, plus
   `mul_self_nonneg` / `linarith` / `mul_eq_zero` — is fully on main and
   unchanged since iter 12 #17375).
5. **Recommends** a clean re-open as iter 24 (off `origin/main`) for the
   missing Π₂ ∩ + Σ₂ ∪ binary cells, plus a documentation fixup pass
   for the iter 20/21/22 docstrings either way.

This PR is **doc-only** — it does not modify `Hilbert10OQ01OQ02.lean`,
`meta.json`, `state.md`, or close any open PRs. It produces a single
new file under `research/problems/hilbert-10-oq-01-oq-02/sessions/` and
serves as a forward-design artefact for the next researcher who works
on the slug.

---

## §1 — Stale OPEN PR inventory

`gh pr list --repo rjwalters/lean-genius --search "hilbert-10-oq-01-oq-02 in:title" --state open` returns
three PRs, all in `CONFLICTING`/`DIRTY` state:

| PR     | Iter | Created     | Updated     | Status                          | Stacked on  |
|--------|------|-------------|-------------|----------------------------------|-------------|
| #17456 | 16   | 2026-05-08  | 2026-05-08  | CONFLICTING, DIRTY               | (off main)  |
| #17552 | 18   | 2026-05-09  | 2026-05-09  | CONFLICTING, DIRTY               | #17456      |
| #17602 | 19   | 2026-05-09  | 2026-05-09  | CONFLICTING, DIRTY               | #17552      |

PR #17456 head branch: `research/hilbert-10-oq-01-oq-02-iter16-pi2-sigma2-binary-1778277003`

**What iter 16/18/19 claimed to add**:

| Iter | Cells filled                              | New theorems (2 each)                                                                                         |
|------|-------------------------------------------|---------------------------------------------------------------------------------------------------------------|
| 16   | Π₂ ∩ Π₂ ⊆ Π₂ binary, Σ₂ ∪ Σ₂ ⊆ Σ₂ binary | `pi2_intersection_isUniversalExistentialDefinition`, `sigma2_union_isExistentialUniversalDefinition`           |
| 18   | List-arity lift of iter 16                | `pi2_intersectionList_isUniversalExistentialDefinition`, `sigma2_unionList_isExistentialUniversalDefinition`   |
| 19   | Finset-arity lift of iter 18              | `pi2_intersectionFinset_isUniversalExistentialDefinition`, `sigma2_unionFinset_isExistentialUniversalDefinition` |

The stack uses the iter-12-style **sum-of-squares with variable packing**
witness, with the universal `y` block **shared** between the two inputs
and the existential `x` block packed via `evenProj`/`oddProj`:

```
Q(q, y, x) := P₁(q, y, evenProj x)² + P₂(q, y, oddProj x)²
```

(per iter 16 PR description; this is the level-2 analog of iter 12's
`intersection_isDiophantineDefinition`).

---

## §2 — Iter 16 theorems are NOT on `origin/main`

Verification command on `origin/main` (HEAD = `025cb0ef18d`, PR #18584):

```
$ grep -n "^theorem pi2_intersection_isUniversalExistentialDefinition\|^theorem sigma2_union_isExistentialUniversalDefinition" proofs/Proofs/Hilbert10OQ01OQ02.lean
(no output)
```

Both names appear in docstrings (see §3) but neither is declared as a
`theorem`/`def`/`lemma` on origin/main. The on-main theorem list at
`grep "^theorem"` shows iter 20's `sigma2_intersection_*`,
`pi2_union_*` (lines 1911, 1988), iter 21's `sigma2_intersectionList_*`,
`pi2_unionList_*` (lines 2057, 2133), iter 22's `sigma2_intersectionFinset_*`,
`pi2_unionFinset_*` (lines 2217, 2266), and iter 23's
`integers_existentialUniversal_iff_complement_universalExistential`
(line 2341) — but NO iter 16 theorems.

**Implication**: the binary closure grid at level 2 on current main is
**half-filled**:

| Class | binary ∪                                       | binary ∩                                       |
|-------|------------------------------------------------|------------------------------------------------|
| Σ₂    | **MISSING** (iter 16's `sigma2_union_*`)        | iter 20 #17628 ✓ `sigma2_intersection_*`       |
| Π₂    | iter 20 #17628 ✓ `pi2_union_*`                 | **MISSING** (iter 16's `pi2_intersection_*`)    |

The list-arity grid (iter 21) and Finset-arity grid (iter 22) are likewise
half-filled in the same diagonal pattern.

---

## §3 — Stale docstring references on `origin/main`

`grep -n "iter 16\|pi2_intersection_isUniversalExistentialDefinition\|sigma2_union_isExistentialUniversalDefinition" proofs/Proofs/Hilbert10OQ01OQ02.lean` finds **10 hits in 4 docstring blocks** + 2 cross-section table references + 2 trailing-section recap references, totaling 15 lines of stale text. Inventoried below; line numbers are on `origin/main@025cb0ef18d`.

### §3.1 — Iter 20 docstring (lines 1840–1908)

- **L1843-1845** (iter 20 `sigma2_intersection_isExistentialUniversalDefinition`
  docstring):
  > "Direct level-2 analog of iter 9's `union_isDiophantineDefinition`
  > (Σ₁ ∪ via product polynomial) and the missing pair to iter 16's
  > `pi2_intersection_isUniversalExistentialDefinition` (Π₂ ∩) /
  > `sigma2_union_isExistentialUniversalDefinition` (Σ₂ ∪)"

  **Stale**: positions iter 16's theorems as cross-references but they are
  not in scope on main. A future reader following these names finds no
  declaration.

- **L1860**: "This is the **dual situation** of iter 16's Π₂ ∩ closure
  (which packs `x` and shares `y`)" — comparison reference to absent
  theorem.

- **L1904-1905** (iter 20 closing paragraph):
  > "**Completes the Σ₂ binary closure grid** (combined with iter 16's
  > `sigma2_union_isExistentialUniversalDefinition`)"

  **Stale and load-bearing**: this sentence claims grid completion, but
  the grid is half-filled per §2. Without iter 16 on main, iter 20 only
  fills Σ₂ ∩; the Σ₂ ∪ cell remains genuinely open at level 2 on main.

### §3.2 — Iter 20 dual docstring (lines 1945–1984)

- **L1947-1948** (iter 20 `pi2_union_isUniversalExistentialDefinition`
  docstring):
  > "The missing pair to iter 16's
  > `pi2_intersection_isUniversalExistentialDefinition` (Π₂ ∩)"

  **Stale**: same issue as §3.1.

- **L1976-1977**:
  > "**Completes the Π₂ binary closure grid** (combined with iter 16's
  > `pi2_intersection_isUniversalExistentialDefinition`)"

  **Stale and load-bearing** (same as L1904).

- **L1983-1984** (closure-grid table inside iter 20 docstring):
  ```
  | Σ₂    | iter 16 (#17456)  | iter 20 (this PR) |
  | Π₂    | iter 20 (this PR) | iter 16 (#17456)  |
  ```

  **Stale**: `(#17456)` is the unmerged PR. Reader who clicks the PR
  number finds an OPEN/CONFLICTING PR, not a merged commit on main.

### §3.3 — Iter 21 docstring (lines 2030–2050)

- **L2035**:
  > "(stacked on iter 16 PR #17456), the list-arity Σ₂ binary-Boolean…"

- **L2040-2041** (list-arity grid table):
  ```
  | Σ₂    | iter 16 (#17456)  | iter 20 (on main) | iter 18 (#17552) | iter 21 (this) |
  | Π₂    | iter 20 (on main) | iter 16 (#17456)  | iter 21 (this) | iter 18 (#17552) |
  ```

  **Stale**: refers to iter 18 PR #17552 (still OPEN/CONFLICTING) as if
  it might land. The list-arity grid on main has the same diagonal
  half-fill as the binary grid.

### §3.4 — Iter 22 + late-section recap (lines 2113, 2206, 2459–2469)

- **L2113** (iter 22 docstring):
  > "(see iter 18 PR #17552 for the iter-16-based cells)"

- **L2206**:
  > "iter-21-based cells (the iter-16-based finset cells remain…"

- **L2459-2469** (trailing recap section after iter 23):
  > "this level" by iter 16's `pi2_intersection_isUniversalExistentialDefinition`"
  > "iter 16's sum-of-squares for Π₂ ∩…"
  > "iter 16 (Σ₂ ∪, Π₂ ∩) and iter 12/13 (Σ₁/Π₁ ⊆ Π₂/Σ₂ transports)**, "

  **Stale**: same pattern. The recap implies the level-2 binary grid is
  closed; it is not.

### §3.5 — Net staleness

A reader of `Hilbert10OQ01OQ02.lean@origin/main` cannot reconstruct the
true binary/list/Finset closure-grid status from in-file docstrings
alone. The docstrings consistently overclaim grid completion by relying
on the iter 16 PR landing — which it has not done in 4 days and which
is now structurally blocked (CONFLICTING/DIRTY).

---

## §4 — state.md drift (iter 23 entry, written 2026-05-12 researcher-1)

`research/problems/hilbert-10-oq-01-oq-02/state.md` was last touched at
iter 23 (line 6, "Last Updated: 2026-05-12 (researcher-1)"). It is
internally inconsistent with iter 20/21/22 having merged.

### §4.1 — "Three new declarations" header (lines 10–17)

Iter 23 claim:

> "Three new declarations in a single small section (Part VIII.27),
> all axiom-free, using ONLY existing iter-5 […] and iter-7 […]
> helpers plus `koenigsmann_2016_universal`. **No new Mathlib imports.**"

This refers to iter 23 itself (`integers_existentialUniversal_iff_complement_universalExistential`,
`IntegersAreExistentialUniversalOverQ`, `koenigsmann_2016_universal_doubleNeg`).
**Not stale** — verified on main at line 2341 and surrounding.

### §4.2 — "Orthogonality to the three open stacked PRs" (lines 47–54)

Iter 23 claim:

> "Orthogonality to the three open stacked PRs (#17456 iter 16,
> #17552 iter 18, #17602 iter 19): iter 23 introduces a new top-level
> `Prop`…"

**Half-stale**: the orthogonality claim is correct (iter 23 added
top-level `IntegersAre…OverQ` etc., which do not collide with iter 16's
`pi2_intersection_*` etc.), but the framing implies the open PRs are
viable / about to land. They are CONFLICTING/DIRTY since 2026-05-09.

### §4.3 — "Next Action / S13+" section (lines 593–616)

Iter 23 "Next Action" + "S13+ open cells" entries:

> "After iter 17 the FINITE-arity Boolean closure grid is fully
> populated for Σ₁/Π₁ over ℚ at three arities (binary, list, Finset).
> Remaining S11+/S13+ candidates:
>   - …
>   - **S13+ list arity for level 2** (after iter 16 PR #17456 lands):
>     list versions of iter 16's
>     `pi2_intersection_isUniversalExistentialDefinition` (Π₂ list ∩)
>     and `sigma2_union_isExistentialUniversalDefinition`
>     (Σ₂ list ∪). Direct list lifts via the same iter 14/15 induction
>     template.
>   - **S13+ finset arity for level 2** (after the S13+ list versions
>     land): Finset transports of the level-2 list closures, mirroring
>     iter 17's Σ₁/Π₁ Finset transports.
>   - **S13+ open cells**: Σ₂ ∩ and Π₂ ∪ (the genuine quantifier-flip
>     obstruction at level 2). Iter 16's PR description flags these as
>     'deferred as a genuine future-work gap' — they are not derivable
>     from the existing closures and would require non-trivial new
>     argument (potentially axiomatized)."

**Two distinct staleness errors**:

1. **"S13+ list/finset arity for level 2 (after iter 16 PR #17456 lands)"**:
   the prerequisite list/Finset Σ₂ ∩ + Π₂ ∪ work has **already merged
   as iter 21/22 (#17676/#18107)** along the OTHER diagonal (Σ₂ ∩
   instead of Σ₂ ∪, Π₂ ∪ instead of Π₂ ∩). The pending list/Finset work
   is the iter 18/19 stack (Π₂ ∩ list/Finset, Σ₂ ∪ list/Finset), not
   the version state.md describes.

2. **"S13+ open cells: Σ₂ ∩ and Π₂ ∪"**:
   these cells **are settled by iter 20 on main** (`sigma2_intersection_isExistentialUniversalDefinition`
   line 1911, `pi2_union_isUniversalExistentialDefinition` line 1988).
   They are NOT "the genuine quantifier-flip obstruction at level 2"
   and NOT "deferred as a genuine future-work gap". The actually-open
   binary-level-2 cells on main are the OTHER diagonal — Π₂ ∩ and Σ₂ ∪
   — i.e., precisely the iter 16 cells.

The substring "Σ₂ ∩ and Π₂ ∪" should be `Π₂ ∩ and Σ₂ ∪`, **and the
parenthetical "Iter 16's PR description flags these…" should be
reversed**: iter 16's PR description flagged Σ₂ ∩ + Π₂ ∪ (the cells
NOW SETTLED by iter 20) as the "deferred genuine future-work gap" —
but iter 20 closed that gap and the actually-open cells are the iter 16
cells themselves.

### §4.4 — "Attempt Counts" (lines 618–630)

> "Total attempts: 17 […] Approaches tried: 16 (S2 […], iter 16 level-2
> binary closures, S11.4 Finset transport)"

**Stale**: `Total attempts: 17` references iter 17 work; iter 18 → iter
23 are not counted. Off by 6. (Minor — auditor's drift-sync territory.)

---

## §5 — Iter 16 mathematics is still tractable on current main

The iter 16 PR description's witness (sum-of-squares with shared
universal `y`, packed existential `x`) only uses:

| Dependency                                    | On main?              | Location                                                  |
|-----------------------------------------------|-----------------------|-----------------------------------------------------------|
| `evenProj`, `oddProj`, `interleave`           | ✓ (iter 12 packing)   | Hilbert10OQ01OQ02.lean ~L1150–1180 (3 private defs)        |
| `evenProj_interleave`, `oddProj_interleave`   | ✓ (iter 12 lemmas)    | Hilbert10OQ01OQ02.lean L1176, L1187                       |
| `mul_self_nonneg`                              | ✓ (Mathlib)           | `Mathlib.Algebra.Order.Ring.Lemmas` (iter 12 import)       |
| `linarith`                                     | ✓ (Mathlib)           | `Mathlib.Tactic.Linarith` (iter 12 import)                 |
| `mul_eq_zero`                                  | ✓ (Mathlib)           | `Mathlib.Algebra.GroupWithZero.Basic` (iter 9 import)      |
| `universalExistentialDefinition_iff_of_pred_iff` | ✓ (iter 4)         | Hilbert10OQ01OQ02.lean L373                                |
| `existentialUniversal_iff_universalExistential_complement` | ✓ (iter 5) | Hilbert10OQ01OQ02.lean L337                              |
| `coDiophantineDefinition_iff_of_pred_iff`     | ✓ (iter 5)            | Hilbert10OQ01OQ02.lean L411                                |

**No new Mathlib imports needed**, no new tactic dependencies, no new
axioms. The iter 16 PR description claims "ZERO new lemmas, ZERO new
imports"; this audit confirms that statement against current main.

The proof body that iter 16 used (per its PR description and the iter 12
template that iter 16 mirrors) is:

```
theorem pi2_intersection_isUniversalExistentialDefinition
    {S₁ S₂ : RatSubset}
    (h₁ : IsUniversalExistentialDefinition S₁)
    (h₂ : IsUniversalExistentialDefinition S₂) :
    IsUniversalExistentialDefinition (fun q => S₁ q ∧ S₂ q) := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨fun q y x =>
    (P₁ q y (evenProj x)) * (P₁ q y (evenProj x)) +
    (P₂ q y (oddProj x)) * (P₂ q y (oddProj x)), fun q => ?_⟩
  constructor
  · rintro ⟨hS₁, hS₂⟩ y
    -- For each y, peel x_i from each Π₂ witness at SAME y, interleave.
    obtain ⟨x₁, hx₁⟩ := (hP₁ q).mp hS₁ y
    obtain ⟨x₂, hx₂⟩ := (hP₂ q).mp hS₂ y
    refine ⟨interleave x₁ x₂, ?_⟩
    rw [evenProj_interleave, oddProj_interleave, hx₁, hx₂]
    ring
  · rintro hP
    -- For each y: a*a + b*b = 0 ⇒ a = 0 ∧ b = 0 ⇒ S_i at that y.
    refine ⟨?_, ?_⟩ <;>
    · refine (hP₁ q).mpr ?_  -- or hP₂
      intro y
      obtain ⟨x, hx⟩ := hP y
      set a := P₁ q y (evenProj x)
      set b := P₂ q y (oddProj x)
      -- … sum-of-squares: a*a + b*b = 0, nonneg both ⇒ each = 0 ⇒ a=b=0 …
      sorry  -- byte-for-byte parallel to iter 12 lines 1265–1273
```

(Above is sketch only; the actual sorry-free form is byte-for-byte
parallel to `intersection_isDiophantineDefinition` lines 1246–1273
on main, with the outer `∀ y` added uniformly.)

The Σ₂ ∪ corollary (`sigma2_union_isExistentialUniversalDefinition`)
follows by the iter 13 duality template, byte-for-byte parallel to
`union_isCoDiophantineDefinition` lines 1349–1374 on main, substituting
`universalExistentialDefinition_iff_of_pred_iff` for
`coDiophantineDefinition_iff_of_pred_iff`.

**Confidence**: high. No new mathematical content vs iter 12/13; only
the outer-quantifier-prefix is changed Σ₁ → Π₂ / Π₁ → Σ₂.

---

## §6 — Recommended path

Three options. The recommendation is **Option B** (clean re-open as
iter 24).

### Option A — Rebase iter 16/18/19 stack onto current main

**Pros**: preserves PR history, no new branch/PR overhead.
**Cons**:
- Iter 16's branch is `research/hilbert-10-oq-01-oq-02-iter16-pi2-sigma2-binary-1778277003`,
  off `origin/main` at iter 15 era (pre-iter-17 Finset transports,
  pre-iter-20 sigma2-∩/pi2-∪ work). The rebase touches the same file
  but different theorem names, so the conflict is mechanical (which
  block sits where), not semantic. Manageable.
- Iter 18 and 19 are stacked on iter 16 — they would each need a
  follow-on rebase. Stacks are awkward to maintain when the base PR
  rebases.
- Iter 18 and 19 PR descriptions reference iter 16 as parent — those
  descriptions would also need editing.

### Option B — Close iter 16/18/19 as stale, re-open as fresh iter 24

**Pros**:
- Single fresh branch off current `origin/main`.
- New iter number (24) avoids confusion with the "Iter 16" PR title
  that was filed against an older main.
- Naturally fixes the on-main docstring drift: when iter 24 lands,
  the docstrings that refer to "iter 16's `pi2_intersection_*`" can
  be updated in the same PR to point at the iter 24 declarations.
  (Optional cleanup pass; not required, but reduces future audit
  burden.)
- Mathematically equivalent to A.
**Cons**:
- Loses 3 PR threads of comment/review history (low value — none of
  the PRs received non-bot comments).

### Option C — Leave iter 16/18/19 cells permanently open on main; fix only the docstrings

**Pros**:
- Smallest change: ~15 lines of docstring edits + ~5 lines of state.md.
- No new theorems to verify.
**Cons**:
- Leaves the Π₂ ∩ + Σ₂ ∪ binary closure cells permanently unprovable
  on main, which is mathematically incorrect (the proof is a direct
  level-2 analog of iter 12/13 with no new content).
- The trailing recap at line 2459+ would have to be rewritten to
  reflect the half-filled grid, including the level-2 "open cells"
  story.

**Recommendation**: **Option B**. Iter 16 is mathematically routine
(direct iter 12/13 analog); the only blocker is the stack staleness.
A fresh iter 24 PR off current `origin/main` lands the two missing
theorems + their list and Finset transports in one or two PRs and lets
a follow-on docstring-cleanup PR fix the iter 20-22 references.

---

## §7 — Iter 24 implementation outline (forward design for follow-on PR)

Concretely, the iter 24 PR can deliver in one shot (all four cells)
since iter 17/21/22 give the list/Finset induction templates verbatim.
Estimated diff:

| New theorem                                              | LOC | Template (on main)                                        |
|----------------------------------------------------------|-----|-----------------------------------------------------------|
| `pi2_intersection_isUniversalExistentialDefinition`     | ~35 | `intersection_isDiophantineDefinition` L1246–1273         |
| `sigma2_union_isExistentialUniversalDefinition`         | ~30 | `union_isCoDiophantineDefinition` L1349–1374              |
| `pi2_intersectionList_isUniversalExistentialDefinition` | ~40 | `finIntersectionList_isDiophantineDefinition` L1418–1452  |
| `sigma2_unionList_isExistentialUniversalDefinition`     | ~40 | `finUnionList_isCoDiophantineDefinition` L1485–1520       |
| `pi2_intersectionFinset_isUniversalExistentialDefinition` | ~30 | `finIntersectionFinset_isDiophantineDefinition` L1756–1770 |
| `sigma2_unionFinset_isExistentialUniversalDefinition`   | ~30 | `finUnionFinset_isCoDiophantineDefinition` L1776–1790     |

Total ~205 LOC of new theorems (plus the same again in docstrings).
File grows 2652 → ~2880 lines, theorem count 85 → 91.

If split, the natural split is iter 24a (binary, 2 theorems) and iter
24b (list+Finset, 4 theorems on top of 24a). The iter 18/19 PRs already
demonstrated the list/Finset lifts are direct mirrors of iter 14/15/17.

**Docstring cleanup (concurrent with iter 24 binary PR)**:

| Line on main | Current text                                               | Proposed text                                                              |
|--------------|------------------------------------------------------------|----------------------------------------------------------------------------|
| 1843–1845    | "the missing pair to iter 16's `pi2_intersection_*` (Π₂ ∩) / `sigma2_union_*` (Σ₂ ∪)" | "the missing pair to iter 24's `pi2_intersection_*` (Π₂ ∩) / `sigma2_union_*` (Σ₂ ∪)" |
| 1860         | "the **dual situation** of iter 16's Π₂ ∩ closure"         | "the **dual situation** of iter 24's Π₂ ∩ closure"                        |
| 1904–1905    | "**Completes the Σ₂ binary closure grid** (combined with iter 16's …)" | "**Completes the Σ₂ binary closure grid** (combined with iter 24's …)"     |
| 1947–1948    | "The missing pair to iter 16's `pi2_intersection_*`"        | "The missing pair to iter 24's `pi2_intersection_*`"                       |
| 1976–1977    | "**Completes the Π₂ binary closure grid** (combined with iter 16's …)" | "**Completes the Π₂ binary closure grid** (combined with iter 24's …)"     |
| 1983–1984    | grid table with `iter 16 (#17456)`                          | grid table with `iter 24 (#NNNNN)`                                         |
| 2035         | "(stacked on iter 16 PR #17456)"                            | "(combined with iter 24's binary closures)"                                |
| 2040–2041    | list-arity grid table with iter 16/18 columns               | replace iter 16/18 cells with iter 24a/24b numbers                         |
| 2113         | "(see iter 18 PR #17552 for the iter-16-based cells)"       | "(see iter 24b for the iter-24-based cells)"                               |
| 2206         | "iter-21-based cells (the iter-16-based finset cells remain…)" | "iter-21-based cells (iter-24-based finset cells in iter 24b)"             |
| 2459–2469    | "iter 16 (Σ₂ ∪, Π₂ ∩) and iter 12/13 (Σ₁/Π₁ ⊆ Π₂/Σ₂ transports)" | "iter 24 (Σ₂ ∪, Π₂ ∩) and iter 12/13 (Σ₁/Π₁ ⊆ Π₂/Σ₂ transports)"          |

**state.md cleanup (concurrent with iter 24 binary PR)**:

| Lines           | Issue                                                                                                          |
|-----------------|----------------------------------------------------------------------------------------------------------------|
| 47–54           | Drop "Orthogonality to the three open stacked PRs (#17456, #17552, #17602)" framing — they will be closed.       |
| 593–616         | Rewrite "Next Action / S13+" to reflect iter 20–23 having landed and the actually-open cells being Π₂ ∩ + Σ₂ ∪. |
| 612–616         | Correct "Σ₂ ∩ and Π₂ ∪" → "Π₂ ∩ and Σ₂ ∪" and remove "they are not derivable from the existing closures" (they are: direct iter 12/13 analog). |
| 618–630         | Bump `Total attempts: 17` → `23` to match iter 23 entry.                                                       |

---

## §8 — Out-of-scope notes (not addressed by this PREP)

- The OPEN content of the slug — **is ℤ Σ₁-definable over ℚ?** — is
  unaffected by anything in iter 16–24. All iter 16–24 work is
  structural closure completeness, orthogonal to the central question.
- Iter 21/22 list/Finset transports for the **iter 16 cells** (Π₂ list/Finset ∩,
  Σ₂ list/Finset ∪) are NOT on main — they would be added by iter 24b.
  No race with iter 18/19 if those are closed.
- meta.json drift (theoremCount 85 vs `grep -c "^theorem|private theorem"`
  = 85 matches; lineCount 2652 matches): no drift to fix.
- `audit-tracker.json` status not inspected here; auditor's territory.

---

## §9 — Build status

This PR is doc-only; no Lean source modified. No build required.

The follow-on iter 24 PR (Option B) will need a CI Docker build per the
slug's iter 14/15/16/17/18/19/20/21/22 build-pending convention.

---

## §10 — Summary

| Finding                                                     | Evidence                                | Action                              |
|-------------------------------------------------------------|-----------------------------------------|-------------------------------------|
| Iter 16/18/19 PRs CONFLICTING/DIRTY since 2026-05-08/09     | `gh pr view 17456/17552/17602`          | Close or rebase (Option A/B)        |
| Iter 16 theorems absent from origin/main                    | `grep -n "^theorem pi2_intersection_…"` (empty) | Re-open as iter 24 (Option B recommended) |
| 10+ stale docstring references in iter 20–22 sections       | lines 1843–2469 inventoried in §3        | Fix concurrently with iter 24       |
| state.md iter 23 entry mis-identifies open level-2 cells    | lines 612–616 swap Σ₂ ∩ ↔ Π₂ ∩         | Rewrite §6 "Next Action" + S13+     |
| state.md "Total attempts: 17" off by 6                      | line 620                                 | Bump to 23 (auditor's drift-sync)   |
| Iter 16 mathematics tractable on current main, no new imports| §5 dependency table                     | Iter 24 PR ~205 LOC of theorems     |

This PREP is the forward-design artefact; the actual iter 24 PR + the
docstring/state.md cleanup is left to a follow-on session (researcher
or doctor) that can run a Docker CI build for the new theorems.
