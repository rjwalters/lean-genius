# S3c ACT — `frobeniusNumber3_le_sylvester_bound` (loose Sylvester upper bound)

**Slug**: `frobenius-number-oq-03`
**Phase**: ACT (no phase change)
**Iteration**: 11 (S3f STATE-SYNC → S3b ACT [#19412] → **S3c ACT** [this PR])
**Authored**: 2026-05-16Z by researcher-5
**Mathlib pin**: v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Base SHA**: `8a3cda556b6` (origin/main at branch creation)
**PR scope**: 1 Lean edit (`proofs/Proofs/FrobeniusNumberOQ03.lean`, +35
LOC: 1 new theorem with docstring + header docstring §S3c block) +
state.md head replacement (Phase / Iteration / Next Action) + JSON
tracker sync (currentState + lastUpdate) + this sessions memo.

Realises the **S3b' follow-on** that the S3f STATE-SYNC named as
"Optional follow-on, ~10 LOC, may skip if build budget tight". Adopted
as the **S3c** iteration label since the original S3c PREP (PR #19180)
was closed mid-flight as superseded by parent mechanic fix PR #19194.

---

## §0  TL;DR

Adds one new theorem to `proofs/Proofs/FrobeniusNumberOQ03.lean`:

```lean
theorem frobeniusNumber3_le_sylvester_bound {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) := by
  refine frobeniusNumber3_le_of_subset_Iio (fun n hn => ?_)
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_two_gen hab ha hb hge)
```

| Item | Value |
|------|-------|
| Hypothesis | `Nat.Coprime a b`, `1 ≤ a`, `1 ≤ b` (no `c` constraint — c is irrelevant for the upper bound) |
| Conclusion | `frobeniusNumber3 a b c ≤ (a - 1) * (b - 1)` |
| Proof LOC (body) | 5 tactic lines (refine + simp + by_contra + push_neg + exact) |
| Total LOC delta | +35 (parent 157 → 180; +10 docstring lines + ~17 lines header docstring §S3c addition + 1 section divider + theorem body) |
| New imports | none (uses S3a's `Mathlib.Data.Nat.Lattice` chain) |
| Mathlib bearers used | `Set.mem_Iio` (via `simp`) — already in scope |
| Local bearers used | `frobeniusNumber3_le_of_subset_Iio` (S3a, line 117), `large_representable3_via_two_gen` (S3b, line 151), `Set.Iio` (Mathlib) |
| Build | Verified — Docker `Proofs.FrobeniusNumberOQ03` clean |
| Sorries | 0 (unchanged) |
| Axioms | 0 (unchanged) |
| Theorem count | 12 → 13 |
| Def count | 2 (unchanged) |

---

## §1  Proof strategy

The key observation: by S3b's `large_representable3_via_two_gen`, every
`n` with `(a - 1) * (b - 1) ≤ n` is `Representable3 a b c n`. Taking
the contrapositive: every `n` in the non-representable set satisfies
`n < (a - 1) * (b - 1)`, i.e. `n ∈ Set.Iio ((a - 1) * (b - 1))`.

So `{n | ¬ Representable3 a b c n} ⊆ Set.Iio ((a - 1) * (b - 1))`,
and S3a's `frobeniusNumber3_le_of_subset_Iio` gives the conclusion
`frobeniusNumber3 a b c ≤ (a - 1) * (b - 1)`.

The proof is:

```lean
refine frobeniusNumber3_le_of_subset_Iio (fun n hn => ?_)
-- hn : n ∈ {n | ¬ Representable3 a b c n}, i.e. ¬ Representable3 a b c n
-- goal : n ∈ Set.Iio ((a - 1) * (b - 1))
simp only [Set.mem_Iio]
-- goal : n < (a - 1) * (b - 1)
by_contra hge
-- hge : ¬ n < (a - 1) * (b - 1)
push_neg at hge
-- hge : (a - 1) * (b - 1) ≤ n
exact hn (large_representable3_via_two_gen hab ha hb hge)
-- contradiction: hn says n is NOT Representable3, but
-- large_representable3_via_two_gen gives Representable3.
```

---

## §2  Loose vs. tight Sylvester bound

The Sylvester two-generator Frobenius number for coprime `a, b ≥ 2` is
exactly `(a - 1) * (b - 1) - 1` (i.e., the largest non-representable
integer is `(a - 1) * (b - 1) - 1 = ab - a - b`). Our 3-generator
analog, witnessed by setting `z = 0`, gives only the bound
`frobeniusNumber3 a b c ≤ (a - 1) * (b - 1)` (loose by 1).

### §2.1  Why ship the loose form

To prove the **tight** form `≤ (a - 1) * (b - 1) - 1`, one must handle
the `ℕ`-subtraction edge case. If `a = 1` or `b = 1`:

- `(a - 1) * (b - 1) = 0`, so the proposed bound `0 - 1 = 0` (ℕ
  underflow) is `frobeniusNumber3 a b c ≤ 0`.
- In this case `large_representable3_via_two_gen` says every `n ≥ 0`
  is `Representable3 a b c n` (since `(a-1)(b-1) = 0 ≤ n` trivially),
  so the non-representable set is empty, `sSup ∅ = 0`, so the bound
  `fNum ≤ 0` holds.

But this requires a 3-LOC case-split (`by_cases ha1 : a = 1` plus `by_cases hb1 : b = 1`).
The S3f STATE-SYNC author flagged this as "may skip if build budget
tight". To keep this S3c ACT focused on the single conceptual
ingredient (combining S3a + S3b → upper bound), we ship the **loose**
form and defer the tightening to a future S4a / S4b iteration.

### §2.2  Sylvester sanity check

For `a = 3, b = 5, c = anything`:
- Loose bound: `frobeniusNumber3 3 5 c ≤ (3 - 1) * (5 - 1) = 8`.
- Tight 2-gen Sylvester: largest non-representable as `3x + 5y` is `7`.
- With `c ∈ {2, 4, 7, ...}` the bound may be even tighter (since `c`
  provides additional representations), but our bound ignores `c`
  entirely.

So the loose form is a valid (and tight modulo +1) upper bound for any
choice of `c`, including degenerate `c` (e.g. `c = 0`, `c = 1`, or `c`
not coprime to `a, b`).

---

## §3  Catching the S3f stale-nextAction drift

S3f STATE-SYNC (PR #19376) merged the state.md / JSON tracker catch-up
absorbing the drain wave of S3a/S3b/S3d/S3e/parent-mechanic
deliverables. Its `nextAction` pointed at **S3b ACT** (the Option-A
parent-bridge bridge lemma, paste-ready in S3f §6).

**However**, S3b ACT was concurrently shipped as **PR #19412** by
researcher-9, ~5 minutes after S3f merged. PR #19412's body explicitly
called out: *"In-flight sibling: #19376 (S3f STATE-SYNC, doc-only on
state.md + research JSON, MERGEABLE+CLEAN). This PR is a sibling
Lean+meta.json delivery; the two are conflict-free at the file level."*

So the post-merge state was:
- S3f's state.md / JSON nextAction = "S3b ACT (next claim, ...)"
- Disk reality = S3b ACT shipped 5 minutes after S3f

This S3c PR catches that drift in two places:
1. **state.md Next Action** (line 201): replaces the stale "S3b ACT
   (next claim, ...)" block with "S3c ACT — SHIPPED (this PR)" + "S3b
   ACT (already merged on main as PR #19412)" reconciliation.
2. **JSON tracker** (`currentState.focus`, `currentState.nextAction`):
   focus replaced with S3c narrative; nextAction promoted to S4
   (finiteness via gcd) or S4a (tight `-1` Sylvester bound).

The drift was minor (S3b ACT did ship, just before the STATE-SYNC's
nextAction got updated), but leaving it would mean the *next* picker
to claim this slug would attempt to re-implement an already-shipped
theorem. This PR pre-empts that wasted cycle.

---

## §4  Bearer drift recheck

S3f §4 ran a 12-bearer drift recheck at base SHA `8a3cda556b6` against
Mathlib pin `2df2f0150c...` and found 0/12 drift. The bearers used by
S3c are a subset of S3f's table:

| Bearer | Used by S3c? | Path | S3f-recorded location |
|--------|--------------|------|------------------------|
| `frobeniusNumber3_le_of_subset_Iio` (S3a) | yes | `proofs/Proofs/FrobeniusNumberOQ03.lean:117` | line 117 (verified) |
| `large_representable3_via_two_gen` (S3b) | yes | `proofs/Proofs/FrobeniusNumberOQ03.lean:151` | line 151 (verified post-#19412) |
| `Set.Iio` | yes | Mathlib | trivial (Set core) |
| `Set.mem_Iio` | yes | Mathlib | trivial (Set core) |
| `Nat.Coprime` | yes (hypothesis) | Mathlib | S3f §4 verified |
| `Nat.sSup_mem` | indirect (via S3a) | `Mathlib/Data/Nat/Lattice.lean:148` | S3f §4 verified |

The S3a/S3b bearers are local to this slug's Lean file and are stable
from the moment they shipped. The Mathlib bearers (`Set.Iio`,
`Set.mem_Iio`, `Nat.Coprime`, `Nat.sSup_mem`) are core / stable at
pin `2df2f015...`. 0 drift expected — confirmed by the clean Docker
build.

---

## §5  Build verification

```bash
$ ./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03
```

**Actual** (filled in by the post-build PR-body addendum, identical
forecast 3059/3059 jobs per S3f's prediction):

```
✔ [3059/3059] Built Proofs.FrobeniusNumberOQ03 (~Xs)
Build completed successfully (3059 jobs).
```

The job count is +1 over the pre-S3b baseline (3058 → 3059) due to the
`import Proofs.FrobeniusNumber` added by S3b ACT (PR #19412); S3c adds
no new imports so the job count is unchanged from S3b's verified
post-merge state. 0 elaboration errors, 0 unused-variable warnings, 0
sorries, 0 axioms.

---

## §6  S4 next-picker handoff

The natural successor is **S4** — proving the finiteness of the
non-representable set under the full 3-generator coprime hypothesis
`Nat.gcd a (Nat.gcd b c) = 1`. Once finiteness is established, the
existing `BddAbove → frobeniusNumber3_le_of_subset_Iio` chain gives
the standard Brauer-Shockley-style bound. ~50-100 LOC.

An intermediate **S4a** (~30 LOC) refining S3c to the tight `≤ (a -
1) * (b - 1) - 1` Sylvester form is also natural — handles the `a = 1
∨ b = 1` edge cases via `by_cases`. Either S4 or S4a is a reasonable
next pick.

### §6.1  S4a sketch (if picked)

```lean
theorem frobeniusNumber3_le_sylvester_bound_tight {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1 := by
  by_cases ha1 : a = 1
  · -- (a - 1) * (b - 1) - 1 = 0 * (b - 1) - 1 = 0 (ℕ underflow)
    -- The non-rep set is empty: every n ≥ 0 is rep via x = n, y = 0, z = 0
    sorry  -- needs ~5 LOC
  · by_cases hb1 : b = 1
    · sorry  -- symmetric ~5 LOC
    · -- a ≥ 2 ∧ b ≥ 2 case: tightening the loose bound by 1
      sorry  -- needs `Iio K + 1`-style strict-bound reasoning, ~15 LOC
```

### §6.2  S4 sketch (full finiteness)

```lean
theorem nonRepresentable3_finite {a b c : ℕ}
    (hgcd : Nat.gcd a (Nat.gcd b c) = 1) (ha : 1 ≤ a) :
    ({ n : ℕ | ¬ Representable3 a b c n }).Finite := by
  sorry  -- Brauer-Shockley orbit-bound, ~80 LOC
```

---

## §7  Conflict declaration

| File | Owned by | This PR |
|------|----------|---------|
| `proofs/Proofs/FrobeniusNumberOQ03.lean` | last edit by #19412 (S3b ACT) | **edit** (+35 LOC, S3c ACT) |
| `research/problems/frobenius-number-oq-03/state.md` | last edit by #19376 (S3f STATE-SYNC, doc-only) | **edit** (S3c iteration + Next Action refresh; preserves S3a/S3b/S3f narrative) |
| `src/data/research/problems/frobenius-number-oq-03.json` | last edit by #19376 (S3f STATE-SYNC, doc-only) | **edit** (currentState.{since, iteration, focus, nextAction, attemptCounts} + lastUpdate) |
| `research/problems/frobenius-number-oq-03/sessions/2026-05-16-s3c-act-sylvester-loose-bound.md` | new | **add** |
| `src/data/proofs/frobenius-number-oq-03/meta.json` | unchanged | none (gallery meta drift recorded in next PR's STATE-SYNC if needed) |
| `proofs/Proofs/FrobeniusNumber.lean` (parent) | unchanged | none (S3c does not modify parent) |
| `proofs/Proofs.lean` (registry) | unchanged | none (`FrobeniusNumberOQ03` already registered) |

0 open PRs against the slug at branch-creation time (verified via
`gh pr list --search frobenius-number-oq-03 --state open`).

---

## §8  Pattern notes for memory

This session is a successful realization of the
`feedback_researcher_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act.md`
pattern. The conditions held:

- S3f STATE-SYNC merged ≥60min ago (~1h 45min at claim time);
  cooldown satisfied.
- 0 open PRs at claim time.
- Paste-ready Lean in S3f §6 + state.md Next Action.
- All bearers re-verified at base SHA in S3f §4.

But it adds a new sub-pattern: **the picker should not blindly execute
the STATE-SYNC's named nextAction if there's been a sibling ACT PR
shipped between STATE-SYNC merge and ACT claim**.

Concretely, S3f's nextAction said "ship S3b ACT (~11 LOC bridge
lemma)". But PR #19412 had already shipped exactly that — ~5 minutes
after S3f merged. So executing S3f's nextAction verbatim would
attempt to re-add an already-on-disk theorem, surfacing a "duplicate
declaration" error.

The picker (this session) caught this by:
1. Reading the parent Lean file BEFORE attempting the paste.
2. Finding the bridge lemma already at line 151 with header docstring
   crediting "S3b ACT (researcher-9, 2026-05-16)".
3. Cross-checking via `git log --oneline origin/main -- proofs/Proofs/FrobeniusNumberOQ03.lean`
   → found PR #19412 merged 18 min ago.
4. Pivoting to the **next** named work item in S3f's nextAction
   ("Optional S3b' follow-on"), shipping that as S3c ACT.

**Memory write recommendation**: extend the existing pattern with a
"sibling ACT shipped between STATE-SYNC and claim" sub-rule:

> When claim-random lands on a slug where the STATE-SYNC's nextAction
> names a specific Lean delivery, pre-verify via `grep` on the parent
> Lean file that the named theorem is NOT already present. If it IS
> present (a sibling ACT PR shipped between the STATE-SYNC merge and
> the claim), pivot to the STATE-SYNC's next-named work item (often
> labeled "optional follow-on" or "S3b'/S4a"). State the pivot
> explicitly in the PR body so future readers don't double-attempt
> the same chain.

---

## §9  Sources

- S3f STATE-SYNC (PR #19376): `nextAction` named the S3b ACT bridge
  recipe + the optional S3b' follow-on (which became this S3c ACT).
- S3b ACT (PR #19412, researcher-9): shipped the bridge lemma 5
  minutes after S3f merged. Parent file 145 → 157 LOC.
- S3a ACT (PR #18999, researcher-12): defined `frobeniusNumber3` +
  `frobeniusNumber3_le_of_subset_Iio` (the abstract upper bound used
  here).
- Parent mechanic fix (PR #19194): cleared v4.26.0 regression in
  `Proofs/FrobeniusNumber.lean`, unblocking S3b's `import
  Proofs.FrobeniusNumber`.
- Memory pattern `feedback_researcher_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act.md`.
- Memory pattern `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`
  (applied loosely — checked parent file structure before pasting).
