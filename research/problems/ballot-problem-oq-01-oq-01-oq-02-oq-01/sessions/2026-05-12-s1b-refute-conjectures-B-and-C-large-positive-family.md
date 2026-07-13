# S1b OBSERVE — refuting refined conjectures **B** and **C** via the large-positive-step family `[K, -m]` (doc-only)

**Slug**: `ballot-problem-oq-01-oq-01-oq-02-oq-01`
**Phase**: OBSERVE (sub-step b — refinement of the S1 OBSERVE landscape)
**Author**: researcher-5
**Date**: 2026-05-12
**Scope**: doc-only. Touches **only** this new session file. No edits to
`problem.md`, `knowledge.md`, `state.md`, Lean source, gallery JSON, or
research JSON. Conflict-free against the just-merged S2 ACT (PR #18381,
~16 min old at session start) and the S3 PREP (PR #18424).

The S1 OBSERVE (PR #18253, researcher-1) recorded the refined-conjecture
landscape **A**–**E** (`knowledge.md` lines 61–105 / `problem.md` lines
86–98) as candidates for S2/S3 work after refuting the parent meta's
`openQuestions[0]` (`⌈S/m⌉ ≤ |goodRotations|`). This session note
**refutes conjectures B and C** with a single dual counterexample family
and suggests the appropriately-strengthened replacement.

## 1. Position vs in-flight and recently-merged PRs

| PR # | Status | Slug touch | What it changes |
| ---- | ------ | ---------- | --------------- |
| #18253 | MERGED 2026-05-12 12:00 UTC | Yes | S1 OBSERVE — created `problem.md`, `knowledge.md`, `state.md` |
| #18381 | MERGED 2026-05-13 02:10 UTC | Yes | S2 ACT — new file `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` (123 LOC, m-jump downward IVT, "build pending") + `Proofs.lean` import |
| #18424 | MERGED 2026-05-13 (earlier today) | Yes | S3 PREP — new doc `sessions/2026-05-12-s3-prep-conjecture-e-bridge-to-parent.md` |
| _(this)_ | NEW | Yes | S1b OBSERVE — single new doc `sessions/2026-05-12-s1b-refute-conjectures-B-and-C-large-positive-family.md` |

**No file collision.** The S2 ACT (#18381) touches Lean only; the S3 PREP
(#18424) created a different session file. This PR creates a different
session file in the same `sessions/` directory.

**Why S1b and not S1c.** The S1 OBSERVE landscape is being refined *in
the same direction* the original refutation pointed (mechanism-of-failure
analysis was *almost* sufficient but stopped one step short of refuting
B/C). This is a refinement of S1, not a new orientation phase.

## 2. The refined-conjecture landscape (verbatim from S1 OBSERVE)

From `problem.md` lines 86–98 (and `knowledge.md` lines 61–105):

| # | Statement | Status as of S1 OBSERVE |
|---|-----------|--------------------------|
| **A** | `0 < l.sum → 0 < (goodRotations l).card` (no `m` needed) | Already proven in parent (`goodRotations_nonempty`) |
| **B** | `(∀ x ∈ l, -m ≤ x) → 0 < l.sum → l.sum ≤ m · card + (m - 1) · n` | "Open; loose but provable using D plus a level-counting argument" |
| **C** | `(∀ x ∈ l, -m ≤ x) → 0 < l.sum → l.sum - (m - 1) · #{negative-step positions} ≤ m · card` | "Open; sharper, charges the slack per negative step" |
| **D** | m-jump downward IVT (the genuine m-generalization of `unit_decrement_downward_ivt`) | **Now proven** (PR #18381, build pending) |
| **E** | `\|goodRotations\| ≥ ⌈l.sum / m⌉` under the *additional* hypothesis `∀ x ∈ l, x ≠ 0 → x ≥ 1` | "Open; restores the {+1, -m} regime" — discharge plan written in PR #18424 |

Throughout, `n := l.length` and `card := (goodRotations l).card`.

## 3. The refuting family

For any `m ≥ 2` and any integer `K ≥ 1`, define
```
l := [K, -m]   ∈ List ℤ
```
with `n = l.length = 2`.

**Hypothesis checks.**
- `∀ x ∈ l, -(m : ℤ) ≤ x`: `K ≥ 1 ≥ -m` ✓; `-m ≥ -m` ✓.
- `0 < l.sum`: `l.sum = K - m`, positive iff `K > m`.

**`goodRotations` count.**
- `i = 0`: `cyclicRotation l 0 = l = [K, -m]`. Prefix sums:
  - `j = 1`: `K > 0` ✓ (since `K ≥ 1`).
  - `j = 2`: `K - m`. For `K > m` this is `> 0`. ✓
  So `i = 0 ∈ goodRotations l` whenever `K > m`.
- `i = 1`: `cyclicRotation l 1 = l.drop 1 ++ l.take 1 = [-m] ++ [K] = [-m, K]`.
  Prefix sum at `j = 1`: `-m < 0`. ✗
  So `i = 1 ∉ goodRotations l`.

Therefore `(goodRotations l).card = 1` for all `K > m`, `m ≥ 2`.

## 4. Conjecture **B** is refuted by `[K, -m]` for `K ≥ 4m - 1`

Conjecture B asserts
```
l.sum ≤ m · card + (m - 1) · n.
```
Substituting `l.sum = K - m`, `card = 1`, `n = 2`:
```
K - m ≤ m · 1 + (m - 1) · 2 = m + 2m - 2 = 3m - 2.
```
Equivalent: `K ≤ 4m - 2`. Hence any `K ≥ 4m - 1` refutes B.

**Smallest integer witness** (`m = 2`):
```
l = [7, -2]    sum = 5,   card = 1,   n = 2.
RHS = 2·1 + 1·2 = 4.       5 ≤ 4 is FALSE.
```

**For `m = 3`**:
```
l = [11, -3]   sum = 8,   card = 1,   n = 2.
RHS = 3·1 + 2·2 = 7.       8 ≤ 7 is FALSE.
```

**For arbitrary `K`**:
```
l = [K, -m]    sum = K - m.
RHS = m + 2(m - 1) = 3m - 2.
LHS - RHS = (K - m) - (3m - 2) = K - 4m + 2.
LHS > RHS  ⇔  K > 4m - 2.
```

## 5. Conjecture **C** is refuted by `[K, -m]` for `K ≥ 3m`

Conjecture C asserts
```
l.sum - (m - 1) · #{negative-step positions} ≤ m · card.
```
For `l = [K, -m]`: there is exactly one negative-step position (the second
entry, with value `-m`), so `#{negative-step positions} = 1`.
Substituting:
```
(K - m) - (m - 1) · 1 ≤ m · 1
⇔  K - 2m + 1 ≤ m
⇔  K ≤ 3m - 1.
```
Hence any `K ≥ 3m` refutes C.

**Smallest integer witness** (`m = 2`):
```
l = [6, -2]    sum = 4,   card = 1,   #neg = 1.
LHS of C: 4 - 1·1 = 3.    RHS: 2·1 = 2.    3 ≤ 2 is FALSE.
```

**For `m = 3`**:
```
l = [9, -3]    sum = 6,   card = 1,   #neg = 1.
LHS: 6 - 2 = 4.            RHS: 3.            4 ≤ 3 is FALSE.
```

Note `3m ≤ 4m - 1` for `m ≥ 1`, so **every** witness for B (`K ≥ 4m - 1`)
is also a witness for C. The conjecture C threshold is slightly weaker:
the smallest refutation is `m = 2, K = 6` (vs `m = 2, K = 7` for B).

## 6. Why both refutations work — the dual mechanism

The original S1 OBSERVE refutation used the family `l = [-m, m + S]` —
**concentrated negative mass at the start**, allowing prefix sums to vault
straight from `0` down to `-m` (skipping `m - 1` intermediate levels). The
present S1b refutation uses `l = [K, -m]` — **concentrated positive mass
at the start**, allowing prefix sums to vault straight from `0` up to `K`
(*also* skipping `K - 1` intermediate levels, this time on the way up).

In both cases the failure mechanism is the same: **a single step skips
intermediate prefix-sum levels**, so the level-counting that powers the
parent's `cycle_lemma` (each integer level in `[minPrefixSum, 0]` is
realised at least once) breaks. The unit-decrement IVT
(`unit_decrement_downward_ivt`) hides this because consecutive prefix sums
differ by at most `1` on *both* sides:
* steps `≥ -1` (lower bound) — proved
* steps `≤ 1` (implicit upper bound when alphabet is `{+1, -k}`)

The refined conjectures B and C drop only the *upper* bound and retain
the lower bound, so they remain vulnerable to upward skips. This is
exactly the residual loss flagged in `knowledge.md` lines 56–59:
> "Allowing larger *positive* steps … removes the level-visitation
> guarantee on the way up, while allowing larger *negative* steps removes
> it on the way down. The refuted conjecture only addressed the second
> loss; **the first matters too**."

The S1 OBSERVE recognised the loss and even named the asymmetry, but did
not propagate it to conjectures B and C in the refined landscape. This
session note completes that propagation.

## 7. The properly-restored conjectures

There are three natural fixes — listed in increasing order of strength.

### 7.1 **B'**: two-sided step bound

Replace the one-sided hypothesis `∀ x ∈ l, -m ≤ x` with a two-sided one:
```
(∀ x ∈ l, -(m : ℤ) ≤ x ∧ x ≤ (m : ℤ))  ∧  0 < l.sum  →
  l.sum ≤ m · card + (m - 1) · n.
```
With both bounds in place, consecutive prefix sums differ by at most `m`
on either side, restoring the level-counting argument. This conjecture is
**not refuted** by `[K, -m]` because `K ≤ m` and `0 < l.sum = K - m`
together give `K = m + ε > m`, contradicting the new upper bound.

**Status**: Conjectural — would need a new S2 plan distinct from #18381.
Level-counting argument via the m-jump IVT (now in Lean) plus its dual
m-jump *upward* IVT (would need to be proved) plausibly gives B', but no
discharge plan exists yet.

### 7.2 **B''**: restrict the *positive* part of the alphabet to {+1}

Equivalent to conjecture **E** (`x = 1 ∨ x = -(m : ℤ)`) — the
{+1, -m} regime. PR #18424's S3 PREP lays out a 50–70 LOC discharge plan
via the parent's `cycle_lemma`. This is the strongest restriction but
makes B's slack term `(m - 1) · n` superfluous (the cycle lemma gives the
*tight* bound `card = a - m·b = l.sum`, so `l.sum ≤ m · card + 0 · n` —
much better than `m · card + (m - 1) · n`).

### 7.3 **B'''**: charge slack per *positive* step too

Replace the per-negative slack of conjecture C with a per-each-large-step
correction:
```
l.sum - (m - 1) · #{|x| ≥ 2 positions} ≤ m · card.
```
For `l = [K, -m]` with `K ≥ 2`: `#{|x| ≥ 2} = 2`, so
LHS - middle = `(K - m) - (m - 1) · 2 = K - 3m + 2`, RHS = `m`. We need
`K ≤ 4m - 2`. So **B''' is also refuted by `[K, -m]` for `K ≥ 4m - 1`**
— the same threshold as B. This shows that per-step linear slack is
**not enough** to absorb single-step skipping; the slack must scale with
the **excess height per skip** (`|x| - 1`), not the count of large
positions:
```
l.sum - ∑_{i : |l[i]| ≥ 1}(|l[i]| - 1) ≤ m · card.
```
For `[K, -m]`: `∑(|x| - 1) = (K - 1) + (m - 1) = K + m - 2`,
LHS - middle = `(K - m) - (K + m - 2) = -2m + 2 = 2(1 - m) ≤ 0 ≤ m`.
So this *survives* — but it collapses to a triviality (LHS ≤ 0 ≤ RHS).
A version with `m - 1` capped excess is the genuinely interesting one.

These three replacements are listed for completeness; this S1b session
does **not** pick an S2 target. Selecting among B', B'', B''' is a
separate decision for the next phase.

## 8. Counterexample summary table

| `m` | `l` | `l.sum` | `card` | `n` | `#neg` | B-RHS | C-LHS | C-RHS | B refuted? | C refuted? |
|----:|-----|--------:|-------:|----:|-------:|------:|------:|------:|-----------:|-----------:|
| 2 | `[-2, 5]` | 3 | 1 | 2 | 1 | 4 | 2 | 2 | ✓ NO (3 ≤ 4) | ✓ NO (2 ≤ 2) |
| 2 | `[6, -2]` | 4 | 1 | 2 | 1 | 4 | 3 | 2 | ✓ NO (4 ≤ 4) | **YES (3 ≤ 2)** |
| 2 | `[7, -2]` | 5 | 1 | 2 | 1 | 4 | 4 | 2 | **YES (5 ≤ 4)** | **YES (4 ≤ 2)** |
| 3 | `[9, -3]` | 6 | 1 | 2 | 1 | 7 | 4 | 3 | ✓ NO (6 ≤ 7) | **YES (4 ≤ 3)** |
| 3 | `[11, -3]` | 8 | 1 | 2 | 1 | 7 | 6 | 3 | **YES (8 ≤ 7)** | **YES (6 ≤ 3)** |

(Where ✓ NO = conjecture holds, YES = conjecture violated.)

The first row is the original S1 OBSERVE counterexample `[-m, m+S]` for
`m = 2, S = 3`. Note it satisfies **both** B and C — concentrated
*negative* mass refutes only the original `⌈S/m⌉` conjecture, not the
refined bounds.

The next four rows are the new family. The threshold pattern:
* **B**: `K ≥ 4m - 1` (smallest: `(m,K) = (2,7)`)
* **C**: `K ≥ 3m` (smallest: `(m,K) = (2,6)`)

## 9. Implications for the slug's research plan

1. **`knowledge.md` line 90** describes conjecture B as "loose but
   provable using D plus a level-counting argument". As shown above,
   this is **incorrect** — B is loose enough to be flat-out wrong, not
   just hard to prove. The level-counting argument doesn't survive
   unrestricted positive steps.

2. **`knowledge.md` line 91** describes conjecture C as "sharper, charges
   the slack per negative step". As shown above, C is **even more
   strongly refuted than B** (smaller threshold: `K ≥ 3m` vs `K ≥ 4m - 1`).

3. **`problem.md` lines 90–91** carry the same claims and would need
   matching updates if the maintainer chooses to revise.

4. **PR #18381 (S2 ACT)** is unaffected. Conjecture D is the m-jump
   downward IVT, which is purely about prefix-sum levels and makes no
   count claim — it's still infrastructure, not a count theorem. The
   refutation of B/C confirms (rather than challenges) the S1 OBSERVE
   prediction that D would be "infrastructure, not a result".

5. **PR #18424 (S3 PREP for E)** is unaffected. E retains the
   `x = 1 ∨ x = -(m : ℤ)` alphabet restriction, which forbids
   the `[K, -m]` family (since `K ≥ 1` with `K ≠ 1` is excluded).

6. **The genuinely-open count conjecture** for unrestricted alphabets is
   now narrowed: any non-trivial bound on `card` in terms of `l.sum`
   needs **both** lower and upper step bounds, or the {+1, -m}
   restriction (E).

## 10. Anti-targets (do NOT attempt now)

* ❌ **Don't edit `problem.md`, `knowledge.md`, or `state.md`.** This is
  an S1b OBSERVE doc-only refinement; the maintainer chooses whether to
  propagate the refutation into the canonical landscape docs.
* ❌ **Don't refute conjecture E.** The `[K, -m]` family does *not*
  apply to E because E requires `x = 1 ∨ x = -m`, excluding `K ≥ 2`.
  PR #18424's S3 PREP discharge plan remains valid.
* ❌ **Don't refute conjecture D.** D is a prefix-sum-level statement,
  not a count statement; no count-related counterexample touches it.
* ❌ **Don't add new conjectures to the landscape without a discharge
  plan.** The three replacements in §7 (B', B'', B''') are *suggested*
  but not committed; the next S2 PREP must pick exactly one and write a
  Lean discharge sketch (analogous to #18424 for E).
* ❌ **Don't formalise the refutation in Lean.** A two-line `decide`-style
  counter-example proof in Lean is straightforward but premature; if
  added at all, it belongs in an S4 GALLERY pass alongside the meta.json
  describing the resolved/refuted parent question (see knowledge.md
  line 142–145 "Next steps" §3).

## 11. No-edit guarantee

This PR creates **exactly one** new file:
```
research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/sessions/
  2026-05-12-s1b-refute-conjectures-B-and-C-large-positive-family.md
```

It does **not** modify:
* `problem.md`
* `knowledge.md`
* `state.md`
* the existing session file (`2026-05-12-s3-prep-conjecture-e-bridge-to-parent.md`)
* any Lean file in `proofs/Proofs/`
* any gallery JSON in `src/data/proofs/` or `src/data/research/problems/`
* `proofs/Proofs.lean` import list
* the candidate pool, claim files, or any agent state files

Conflict-free against #18381 (Lean only) and #18424 (different session
file in the same directory).

## 12. Honesty notes

1. **Elementary refutation.** The `[K, -m]` counterexample is as
   elementary as the original `[-m, m + S]` family from S1 OBSERVE — a
   2-element list with one large positive and one `-m`. No new
   mathematics; just propagating the failure mechanism the S1 OBSERVE
   itself identified (`knowledge.md` lines 56–59) one step further into
   the refined landscape.

2. **Doesn't advance the proof.** This refines the *negative* knowledge
   — what cannot be proved as stated. It does not produce or sketch a
   new lower-bound theorem on `card`. The constructive output is the
   list of suggested replacements (B', B'', B''') in §7, but those are
   informal and need a separate S2 PREP to pick one and write a
   discharge plan.

3. **Doesn't validate the S2 ACT (PR #18381) build.** PR #18381 is
   "build pending"; this PREP makes no claim about whether
   `m_jump_downward_ivt` compiles, only about what it implies (or
   does not imply) for the count conjectures.

4. **The C-refutation is slightly tighter** (threshold `K ≥ 3m` vs
   `K ≥ 4m - 1` for B). Both refutations use the same family, but the
   C-witness with `K = 3m` does **not** refute B; only `K ≥ 4m - 1`
   refutes both. This is recorded in the §8 table and matters for
   anyone trying to choose between the two when picking a replacement
   to strengthen.

## 13. References

- Parent file: `proofs/Proofs/BallotProblemOQ01OQ01OQ02.lean`
  (the abstract cycle lemma, unit-decrement + all-positive cases).
- Grandparent file: `proofs/Proofs/BallotProblemOQ01.lean`
  - `cyclicRotation` (line 264), `prefixSum` (line 353),
    `isGoodRotation` (line 368), `goodRotations` (line 382),
    `goodRotations_nonempty` (line 494), `cycle_lemma` (line 763).
- S1 OBSERVE: `2026-05-12-s1b-...` (this file) follows on from PR #18253
  (`knowledge.md`, `problem.md`, `state.md` of this slug).
- S2 ACT: PR #18381 — `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean`,
  m-jump downward IVT, build pending.
- S3 PREP: PR #18424 — `sessions/2026-05-12-s3-prep-conjecture-e-bridge-to-parent.md`,
  Conjecture E bridge to parent's `cycle_lemma`.
- Parent meta `openQuestions`:
  `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02/meta.json` —
  `openQuestions[0]` is the conjecture refuted in S1 OBSERVE (#18253).
- Mohanty, *Lattice Path Counting and Applications*, Academic Press,
  1979 — cited in `problem.md` as the canonical reference for
  multi-step alphabets `{+a, -b}` (relevant when picking among the §7
  replacements).
