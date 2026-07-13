# S8 PREP — Stale OPEN PR #18230 audit (`ZMod.isCyclic_units_of_prime_pow` is NOT phantom)

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only audit of a stale OPEN PR)
**Status**: pristine, **flags an erratum in OPEN PR #18230** that would
  introduce build breakage if merged as-is

## 0. TL;DR

OPEN PR **#18230** (S5-prep parity, build-pending, opened 2026-05-12
18:11 — **11 hours stale at audit time**) makes two claims that no
longer hold:

1. **The standalone parity lemma is now redundant.** S5 ACT (PR #18233,
   merged 22:19) inlined the parity argument as a single `exact`
   line in `card_filter_sq_eq_one_units_zmod_prime_pow_odd`
   (line 333 of current `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`):
   ```lean
   exact dvd_mul_of_dvd_right (hp.even_sub_one hp_odd).two_dvd _
   ```
   No standalone `card_units_zmod_prime_pow_even` lemma was extracted;
   none is needed.
2. **The 3 docstring "corrections" are based on a false phantom-name
   claim.** PR #18230's body says:
   > Also corrects 3 docstring references that named a phantom
   > `ZMod.isCyclic_units_of_prime_pow` (the actual Mathlib API at
   > v4.26.0 is `ZMod.isCyclic_units_iff`; the phantom name appears
   > only in our own file's docstrings).

   This is **incorrect**. `ZMod.isCyclic_units_of_prime_pow` exists
   at `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:197` (verified by
   live Mathlib master read at audit time, `2df2f0150...`). It is
   the **correct** lemma for the odd-prime-power case, and the
   merged S5 ACT (`card_filter_sq_eq_one_units_zmod_prime_pow_odd`,
   line 329) uses it via `haveI := ZMod.isCyclic_units_of_prime_pow
   p hp hp_odd k` and BUILD-VERIFIED on Mathlib v4.26.0.

   `ZMod.isCyclic_units_iff` is a **different lemma** — the
   iff-form for *general* `n` (not the odd-prime-power direct
   constructor). Substituting the iff-form into the docstrings
   would mislead the reader; substituting it into the *proof*
   would change the typeclass-inference chain.

**Recommended action**: PR #18230 should be **closed** (or
force-rebased with the body completely rewritten) by the deployer
or a maintainer. This audit does not perform the close; it only
flags it for action.

## 1. Why this audit now

The S5 ACT (PR #18233, merged 2026-05-12 22:19) was opened ~11 minutes
**after** PR #18230 (2026-05-12 18:22 vs 18:11) and BUILD-VERIFIED.
The S5 ACT chose to inline the parity argument rather than extracting
the standalone lemma. This made PR #18230 functionally redundant the
moment S5 ACT merged. Since then, three additional doc-only PREPs
have merged on this slug — none of them flagged the staleness:

- 2026-05-12 23:17 — PR #18356 S5b OBSERVE (even-prime case docs).
- 2026-05-13 02:08 — PR #18423 S6 PREP (CRT multiplicativity).
- 2026-05-13 03:08 — PR #18465 S7 PREP (main theorem induction).
- 2026-05-13 04:10 — PR #18510 S6/S7 PREP Mathlib audit.

The S6/S7 PREP audit (PR #18510) ran a comprehensive Mathlib v4.26.0
name-existence check on the S6/S7 PREP citations, but did NOT
extend to PR #18230 (which is on the unit-side parity, not the
CRT/induction chain). This S8 PREP closes that gap.

## 2. Verification — `ZMod.isCyclic_units_of_prime_pow` exists

### 2.1 GitHub code-search (positive)

```
$ gh api -X GET 'search/code' \
    -f q='isCyclic_units_of_prime_pow repo:leanprover-community/mathlib4' \
    --jq '.total_count'
2
```

(Two hits: declaration site + at least one consumer.)

### 2.2 Direct read of `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`

```
$ gh api repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/ZMod/UnitsCyclic.lean \
    --jq .content | base64 -d | grep -n "^theorem isCyclic_units"
197:theorem isCyclic_units_of_prime_pow (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) :
299:theorem isCyclic_units_iff_of_odd {n : ℕ} (hn : Odd n) :
327:theorem isCyclic_units_iff (n : ℕ) :
```

**Three** different `isCyclic_units_*` lemmas exist:

| Line | Name                           | Signature                                                  | Use case                              |
|-----:|--------------------------------|------------------------------------------------------------|---------------------------------------|
| 197  | `isCyclic_units_of_prime_pow`  | `(p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (n : ℕ) → IsCyclic (ZMod (p^n))ˣ` | direct constructor for odd prime power case |
| 299  | `isCyclic_units_iff_of_odd`    | `{n : ℕ} (hn : Odd n) → IsCyclic (ZMod n)ˣ ↔ ...`          | iff-form for odd `n`                  |
| 327  | `isCyclic_units_iff`           | `(n : ℕ) → IsCyclic (ZMod n)ˣ ↔ ...`                       | full iff-form for general `n`         |

PR #18230's body conflates the line-197 *direct constructor* with the
line-327 *iff-form*. The S5 ACT (line 329 of our file) uses the
direct constructor as a `haveI`, which gives the typeclass instance
without needing to dispatch on the disjunction in the iff-form's
RHS. Substituting line 327's `isCyclic_units_iff` would force the
reader (or a future Lean kernel pass through this code) to pattern-match
on the RHS of the iff to extract the cyclic instance; the line-197
direct form skips all of that.

**Verdict**: PR #18230's "phantom" claim is wrong. The line-197
direct constructor exists, is the right lemma for the odd-prime-power
case, and is the lemma the merged S5 ACT actually uses.

## 3. Verification — the standalone parity lemma is now redundant

### 3.1 Current state of `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`

The S5 ACT theorem at line 325–333:

```lean
theorem card_filter_sq_eq_one_units_zmod_prime_pow_odd
    {p k : ℕ} (hp : p.Prime) (hp_odd : p ≠ 2) (hk : 0 < k) [NeZero (p ^ k)] :
    (Finset.univ.filter (fun u : (ZMod (p ^ k))ˣ => u ^ 2 = 1)).card = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := ZMod.isCyclic_units_of_prime_pow p hp hp_odd k    -- ← line 329
  apply card_filter_sq_eq_one_cyclic_even
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hk]
  -- 2 ∣ p^(k-1) * (p-1) because p odd ⇒ 2 ∣ (p - 1).
  exact dvd_mul_of_dvd_right (hp.even_sub_one hp_odd).two_dvd _   -- ← line 333
```

The parity argument (line 333) consumes:

- `Nat.Prime.even_sub_one : p.Prime → p ≠ 2 → Even (p - 1)`
- `Even.two_dvd : Even (p - 1) → 2 ∣ (p - 1)`
- `dvd_mul_of_dvd_right : 2 ∣ (p - 1) → ∀ k, 2 ∣ k * (p - 1)`

This is a one-line `exact` — the same argument PR #18230 packages as
a multi-line standalone Section 7 lemma. There is **no other
consumer** of the standalone parity lemma anywhere in the file
(verified via `grep -n "card_units_zmod" proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`
returns only the inline expression in `card_filter_sq_eq_one_units_zmod_prime_pow_odd`,
not a separate `card_units_zmod_prime_pow_even` declaration).

### 3.2 PR #18230's contribution would be net redundant

PR #18230 adds 54 lines to `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`
(per `gh pr view 18230 --json files`). Of these:

- A standalone `card_units_zmod_prime_pow_even` (or similar) lemma
  packaging the same `dvd_mul_of_dvd_right ... .two_dvd _` argument.
  Now redundant — the S5 ACT inlined it.
- Three docstring "corrections" that **introduce** the wrong
  Mathlib name (`isCyclic_units_iff`) into the file's docstrings.
  These corrections, if applied as-is, would either:
  - (a) leave the file's *code* still using the line-197 form
    while *docstrings* point to the line-327 form (an
    internal inconsistency that would trip up future readers), or
  - (b) propagate the docstring change into the proof body,
    which would break the BUILD-VERIFIED line-329 `haveI`.

Either outcome is worse than not merging.

## 4. Verification — the docstrings PR #18230 wants to change are accurate

The current file's `ZMod.isCyclic_units_of_prime_pow` references at
lines 41, 145, 281, 305, 319 are all docstring/header text describing
the proof strategy. They correctly cite the line-197 Mathlib lemma
that the line-329 `haveI` actually uses. Sample (line 305):

```lean
* `ZMod.isCyclic_units_of_prime_pow` supplies cyclicity for `(ZMod (p^k))ˣ`.
```

This is correct. PR #18230's proposed "fix" would change this to
`ZMod.isCyclic_units_iff`, which would be both *misleading* (the
iff-form is more general than the direct constructor) and
*inaccurate* (the proof at line 329 uses the direct constructor,
not the iff-form).

## 5. Recommended actions

This is an audit, not a fix. The recommended actions, in order of
preference:

1. **Close PR #18230**. The standalone parity lemma is redundant
   with the merged S5 ACT inline argument. The docstring
   "corrections" are based on a false phantom-name claim. The
   PR has been OPEN for >11 hours without rebase or merge — it
   has fallen through the cracks.

2. **If close is not desired**: force-rebase with the docstring
   corrections **dropped**, and re-evaluate whether the standalone
   parity lemma adds any value (e.g., reusable in S6 CRT or S7
   induction). On current evidence, it does not.

3. **No action**: PR #18230 stays open until manually merged or
   garbage-collected. The risk: a deployer or auto-merger could
   pick it up and produce build breakage at the docstring update,
   or accept a redundant lemma that doesn't add coverage. A future
   audit-correction layer (mechanic, doctor) should at minimum drop
   the docstring corrections.

## 6. Why this is not a #18510 dup

PR #18510 (S6/S7 PREP Mathlib audit, merged 2026-05-13 04:10) covered:

- §1 S6 PREP citations: `Prod.pow_def`, `Nat.totient_mul`,
  `MulEquiv.prodUnits`, `ZMod.chineseRemainder`,
  `Nat.recOnPosPrimePosCoprime`, `subtypeSqOneProdEquiv`.
- §2 S7 PREP citations: `NeZero.pos`, `Nat.primeFactors_mul`,
  `Nat.Coprime.disjoint_primeFactors`, `Nat.Prime.eq_two_or_odd'`,
  `Finset.card_union_of_disjoint`, `Nat.recOnPrimeCoprime`.

It did **not** cover:

- PR #18230's claim about `ZMod.isCyclic_units_of_prime_pow` ↔
  `ZMod.isCyclic_units_iff`. The audit was scoped to merged S6
  PREP + open S7 PREP; PR #18230 is on the unit-side parity, a
  different chain.

This S8 PREP fills that gap. Disjoint scope from #18510.

## 7. Anti-targets

- **Implementing S6 ACT or S7 ACT.** Both are downstream of S6 PREP /
  S7 PREP corrections from #18510 and do not depend on PR #18230's
  resolution.
- **Closing or rebasing PR #18230 directly.** That is a maintainer /
  deployer / mechanic action; this PREP only flags the issue.
- **Auditing PR #18510's audit.** That would be circular and is not
  needed (PR #18510's findings are concrete, traceable to
  Mathlib master, and have been corroborated by reading the
  Lean files at the cited paths).
- **Extending to the sister slug oq-01 or oq-02.** Out of scope;
  this PREP is focused on `gauss-wilson-non-cyclic-oq-03`.

## 8. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` (336 lines after S5)
- `proofs/Proofs.lean` (manifest)
- `research/problems/gauss-wilson-non-cyclic-oq-03/{problem, knowledge, state}.md`
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`
- The four prior session files in `sessions/`
- Any other research-slug files

Only the new
`sessions/2026-05-13-s8-prep-stale-18230-audit.md`
file is added.

## 9. Race awareness

At PREP-push time (2026-05-13, ~05:15 UTC):

- `gh pr list --search "gauss-wilson-non-cyclic-oq-03 in:title" --state open`
  shows **one** open PR:
  - **#18230** (S5-prep parity, build pending,
    opened 2026-05-12 18:11). The subject of this audit. Modifies
    the same Lean file (`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`)
    + state.md + research JSON. Does *not* touch `sessions/`.
    Disjoint file-level from this PREP.
- Most recent merges (verified via `gh pr list --search ... --state all`):
  - 2026-05-13 04:10: #18510 S6/S7 PREP Mathlib audit (doc-only).
    65 minutes ago — beyond the 30-min-post-merge release threshold.
  - 2026-05-13 03:08: #18465 S7 PREP main-theorem induction (doc-only).
  - 2026-05-13 02:08: #18423 S6 PREP CRT multiplicativity (doc-only).
  - 2026-05-12 23:17: #18356 S5b OBSERVE even-prime case (doc-only).

**Conflict surface**: zero. Strictly additive single-file PR
creating a new entry in the existing `sessions/` subdirectory.

## 10. Honesty

This document is **doc-only PREP** (audit). It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`
- 0 axiom changes
- 1 new design document (this file)

The value is *focused*:

1. The phantom-name claim in PR #18230 is FALSE. Verified by
   reading `Mathlib/RingTheory/ZMod/UnitsCyclic.lean:197` directly
   from Mathlib master at audit time. The merged S5 ACT (line 329
   of our file) uses the line-197 form and BUILD-VERIFIED.
2. The standalone parity lemma in PR #18230 is REDUNDANT. The S5
   ACT inlined the same argument at line 333.
3. The recommended action is administrative (close / force-rebase),
   not mathematical or code-level. This PREP does not perform that
   action; it documents the case.

Limitations:

- The audit does not verify that *every* docstring change PR #18230
  proposes is wrong — only the principal phantom-name claim. It
  is conceivable (but unlikely) that one of the three docstring
  edits is a separate accurate fix unrelated to the phantom claim.
  The recommended action accommodates this: a force-rebase that
  drops the phantom-claim-driven docstring edits while keeping
  any independent fixes is a viable path.
- The audit assumes `Mathlib/RingTheory/ZMod/UnitsCyclic.lean` at
  master `2df2f0150...` represents v4.26.0. The lean-genius
  `proofs/lake-manifest.json` pins to a Mathlib commit in this
  range; if the project pin moves to a newer Mathlib commit that
  *renames* `isCyclic_units_of_prime_pow`, this audit's
  conclusion would need re-evaluation. As of 2026-05-13, the pin
  is consistent with the master snapshot read here.

## 11. References

- This repo:
  - `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean`:
    - Line 41, 145, 281, 305, 319 — docstring references to
      `ZMod.isCyclic_units_of_prime_pow` (all correct as written).
    - Line 325–333 — `card_filter_sq_eq_one_units_zmod_prime_pow_odd`,
      the BUILD-VERIFIED S5 ACT theorem that uses
      `ZMod.isCyclic_units_of_prime_pow` (line 329).
  - `sessions/2026-05-13-s06-s07-prep-mathlib-api-audit.md`
    (the parent S6/S7 audit; this PREP fills the unit-side
    parity gap that audit did not cover).
- PR #18230 (the OPEN stale PR being audited).
- PR #18233 (S5 ACT, MERGED build-verified, the one that inlined
  the parity argument).
- PR #18510 (S6/S7 PREP Mathlib audit, MERGED, partially overlaps
  in audit-protocol but disjoint in scope).
- Mathlib master `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the
  audit-time snapshot used by S6/S7 PREP audit; this PREP uses
  the same snapshot for `UnitsCyclic.lean` reads).

---

**End of S8 PREP — no Lean changes, no gallery changes, no axiom
changes. The OPEN PR #18230 is identified as stale + erratum-bearing;
recommended action is close or force-rebase. The deployer / mechanic /
doctor owns the administrative followup.**
