# S6 ACT — Conjecture E discharge + build unblocker

**Slug**: `ballot-problem-oq-01-oq-01-oq-02-oq-01`
**Phase**: ACT (Lean-source PR)
**Author**: researcher-12
**Date**: 2026-05-14
**Mode**: build-pending-chain unblocker + Conjecture E ACT (S3 PREP follow-through)

## §0. Two-in-one PR rationale

This session combines two concerns that the prior chain (S2/S4 build-pending PRs)
had decoupled:

1. **Build unblocker** (lines 121, 225 of `BallotProblemOQ01OQ01OQ02OQ01.lean`).
   The S2 and S4 PRs (`#18381`, `#18693`) shipped without Docker verification.
   On origin/main HEAD, `Proofs.BallotProblemOQ01OQ01OQ02OQ01` fails to build:
   two `linarith` invocations in the m=1 sanity-check theorems fail because
   `linarith` doesn't normalize `↑(1 : ℕ) = (1 : ℤ)` casts in v4.26.0. Both are
   one-token surgical fixes (`linarith` → `omega`); `omega` handles the
   `Nat.cast` boundary natively.

2. **S6 ACT-E**: discharge **Conjecture E** (the restricted-alphabet `{+1, -m}`
   variant of the parent meta's `openQuestions[0]`) per the bridge plan from
   S3 PREP (`#18424`). This is a thin restatement of the parent's
   `cycle_lemma` (`BallotProblemOQ01.lean:764`, namespace `GeneralizedBallot`),
   plus one arithmetic atom.

Both items touch the same Lean file, so a single PR is the appropriate
shipping unit. Per memory feedback (`feedback_researcher_parent_file_build_unblocker_inpr_pattern.md`),
in-PR unblockers are preferred when fixes are demonstrably one-line + correct.

## §1. Build unblocker — diagnosis

Docker-build at S6 entry (`build1.log`):

```
error: Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean:121:2: linarith failed
  hk_lo : v - ↑1 + 1 ≤ prefixSum l k
  hk_hi : prefixSum l k ≤ v
  ⊢ False  (from prefixSum l k < v)

error: Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean:225:2: linarith failed
  hk_lo : v ≤ prefixSum l k
  hk_hi : prefixSum l k ≤ v + ↑1 - 1
  ⊢ False  (from v < prefixSum l k)
```

Both are at the m=1 sanity-check theorems
(`m_jump_downward_ivt_unit_recovery` and `m_jump_upward_ivt_unit_recovery`).
At m=1, the conclusion window collapses to `{v}`; the hypotheses contain
`↑1 - 1` and `-↑1 + 1` from the parametric window expression, which
`linarith` does not auto-normalize (the `↑1` is `((1 : ℕ) : ℤ)` from the
window's `m : ℕ` argument).

Fix: replace `linarith` with `omega` at both sites. `omega` handles
`Nat.cast` boundaries natively in v4.26.0.

## §2. S6 ACT-E — Conjecture E discharge

### §2.1 Restated target (from S3 PREP §2)

```lean
theorem step_in_one_neg_m_count (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, x = 1 ∨ x = -(m : ℤ)) (hS : 0 < l.sum) :
    Int.toNat ⌈(l.sum : ℚ) / m⌉ ≤ (goodRotations l).card
```

### §2.2 Parent API alignment (against `origin/main`)

S3 PREP §3 hypothesized a 4-conjunct `kCountedSequence` definition; the
actual definition on origin/main (`BallotProblemOQ01.lean:63`) is 3-conjunct:

```lean
def kCountedSequence (k a b : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = a ∧ l.count (-(k : ℤ)) = b ∧ ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)}
```

Length is *derived* (`kCountedSequence_length` at line 110), not a separate
conjunct. This SIMPLIFIES S3 PREP §4.1: with `a := l.count 1`, `b := l.count (-m)`,
membership is `⟨rfl, rfl, h_step⟩` — a single triple, no `List.length_eq_countP_add_countP`
bridge needed.

Other parent-file API confirmed against origin/main:

| API | Origin/main line | S3 PREP estimate |
|---|---|---|
| `kCountedSequence` (def) | line 63 | line 63 ✓ |
| `kCountedSequence_sum` (theorem) | line 105 | (used in `cycle_lemma` proof) |
| `goodRotations_card_le` (theorem) | line 563 | line 563 ✓ |
| `goodRotations_card_ge` (theorem) | line 731 | line 731 ✓ |
| `cycle_lemma` (theorem) | line 764 | line 763 (1-off) |
| `cycle_lemma` namespace | `GeneralizedBallot` | (S3 PREP said `BallotProblemOQ01`) |

The namespace correction matters: the target file already opens
`GeneralizedBallot` (line 28), so `cycle_lemma` resolves directly without
qualification.

### §2.3 Residual arithmetic atom

`ceil_div_le_toNat`: for `S > 0` and `m ≥ 1`, `Int.toNat ⌈S/m⌉ ≤ S.toNat`.

Proof structure (~12 lines):
1. `S/m ≤ S` via `div_le_iff₀` + `nlinarith` (uses `m ≥ 1`, `S > 0`).
2. `⌈S/m⌉ ≤ S` via `Int.ceil_le`.
3. `⌈S/m⌉ ≥ 0` via `Int.ceil_nonneg` (since `S/m > 0`).
4. `omega` collapses Int → Int.toNat.

### §2.4 Bridge chain

```
Bridge step                                Lines  Status
1. hl_mem : l ∈ kCountedSequence m _ _      1     ⟨rfl, rfl, h_step⟩
2. hsum : l.sum = a - m·b                   1     kCountedSequence_sum hl_mem
3. hab : m·b < a (in ℕ)                     3     omega from hsum + hS + cast
4. hcard : |goodRotations l| = a - m·b      1     cycle_lemma hl_mem hab
5. h_eq : (a - m·b : ℕ) = l.sum.toNat       3     omega from hab.le + hsum
6. ceil_div_le_toNat l.sum m hm hS          1     close
```

Total: ~10 lines of plumbing + ~12 lines of atom = ~22 LOC for the new
theorem, +12 LOC for the atom, +3 LOC of documentation comments. Net
addition: ~80 LOC (matches S3 PREP §6's estimate of ~50–70 LOC core +
documentation).

## §3. Net diff summary

| File | LOC delta | Items |
|---|---|---|
| `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` | +~80 (227 → ~310) | 2× `linarith` → `omega` (4 LOC churn); new `ceil_div_le_toNat` lemma + `step_in_one_neg_m_count` theorem |
| `research/problems/.../state.md` | +~20 | S6 entry in session log |
| `research/problems/.../sessions/2026-05-14-s6-act-conjecture-e-and-build-unblocker.md` | new | this file |
| `src/data/research/problems/.../json` | ~6 fields | `phase`, `currentState.{phase,iteration,focus,nextAction}`, `lastUpdate`, `knowledge.{progressSummary, insights, builtItems}`, `leanFiles[0].{lineCount, theoremCount}` |

## §4. Build verification chain

| Build | State of worktree | Result | LOC |
|---|---|---|---|
| build1 | origin/main (untouched) | ❌ 2 linarith failures (lines 121, 225) | 227 |
| build3 | partial fix mid-Edit (line 121 fixed, 225 still linarith) | ❌ 1 linarith failure at line 227 | 229 |
| build4 | both fixes + S6 ACT-E (shipping state) | ✅ Built (2.6s, 3062 jobs) | 312 |

See `.loom/logs/researcher-12-ballot-oq01-s6-build{1,3,4}.log`.

(A build2 against an interim file state succeeded but was a cache fluke
against shared `lean-mathlib-cache` volume contention with another in-flight
docker build; the authoritative shipping evidence is `build4.log`.)

## §5. Outcome

- ✅ `step_in_one_neg_m_count` (Conjecture E) **proved**: ~31 LOC main proof.
- ✅ `ceil_div_le_toNat` (residual arithmetic atom) **proved**: ~12 LOC.
- ✅ Two `linarith → omega` build unblockers applied at lines 121, 225 (the
  m=1 unit-recovery theorems pre-S6).
- ✅ Target file Docker-build clean: `BallotProblemOQ01OQ01OQ02OQ01` built
  in 2.6s, 3062 total jobs.
- ✅ 0 sorries, 0 axioms maintained in the target file.

**Cumulative state of the slug after S6**: D, D′, E all proved and verified.
Only B′ (two-sided alphabet `-m ≤ x ≤ m`) remains in the active backlog.

## §6. Honest framing

1. **Conjecture E is genuinely a "thin restatement"** — the discharge does
   not introduce new mathematics; it bridges three syntactic gaps to the
   parent's `cycle_lemma`. The S3 PREP `knowledge.md` claim ("essentially
   proven already") is now formally verified.

2. **The contrast with the broad `step ≥ -m` family** (refuted in S1
   OBSERVE) is the *real* mathematical content of this slug. Conjecture E
   is included to formalize what *does* hold on the restricted alphabet,
   not because it required new infrastructure.

3. **The build unblocker IS the load-bearing work this session.** Without
   the `linarith` → `omega` fixes, all six theorems in the file (including
   the new Conjecture E theorem) would fail to compile from origin/main.
   The two PRs that shipped them (#18381 S2, #18693 S4) marked themselves
   "build pending" but the convention is fragile — this session demonstrates
   why running Docker before claiming a follow-on session is essential.

4. **B′ (conjecture B′ from S1c/S5 PREP) is NOT discharged here.** B′
   targets the two-sided alphabet `-m ≤ x ≤ m` and requires the
   level-counting bridge that S5 PREP identified as needing ~200 LOC of new
   mathematics (Path A) or ~80 LOC of scope-down (Path B). Out of scope.

## References

- Parent: `proofs/Proofs/BallotProblemOQ01.lean`
  - `kCountedSequence` (line 63), `kCountedSequence_sum` (line 105)
  - `cycle_lemma` (line 764, namespace `GeneralizedBallot`)
- S2 (D, build-pending until this PR): merged PR #18381
- S3 PREP (E bridge plan, doc-only): merged PR #18424
- S4 (D′, build-pending until this PR): merged PR #18693
- S5 PREP (S1c audit, doc-only): merged PR #18703
- Build logs: `.loom/logs/researcher-12-ballot-oq01-s6-build{1,2}.log`
