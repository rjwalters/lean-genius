# S5 PREP — Audit of S1c §3.2 discharge sketch + corrected scope for B′

**Date**: 2026-05-13 (~08:35 UTC)
**Researcher**: researcher-1
**Mode**: PREP (doc-only — audits the §3.2 "level-counting bridge" sketched in
S1c PREP PR #18487 and identifies three concrete gaps before any S5/S6 ACT)
**Status**: pristine new sessions file. Orthogonal to all prior PRs on this
slug.

| PR | Status | Touches |
|---|---|---|
| #18253 (S1 OBSERVE, researcher-1) | MERGED | `problem.md`, `knowledge.md`, `state.md`, new gallery JSON |
| #18381 (S2 ACT D, researcher-12) | MERGED (build pending) | `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` |
| #18424 (S3 PREP E, researcher-12) | MERGED | `sessions/2026-05-12-s3-prep-conjecture-e-bridge-to-parent.md` |
| #18480 (S1b OBSERVE B/C refute, researcher-5) | OPEN | `sessions/2026-05-12-s1b-refute-conjectures-B-and-C-large-positive-family.md` |
| #18487 (S1c PREP B′, researcher-8) | MERGED | `sessions/2026-05-13-s1c-prep-conjecture-b-prime-two-sided-alphabet.md` |
| #18693 (S4 ACT D′, researcher-3) | OPEN | edits `BallotProblemOQ01OQ01OQ02OQ01.lean` + new `sessions/2026-05-13-s4-act-m-jump-upward-ivt.md` |
| **#? (this PREP)** | new | new `sessions/2026-05-13-s5-prep-discharge-sketch-audit.md` |

No file overlap with any open PR. This PREP touches a unique sessions file and
nothing else.

## §0. Why an audit before S5 ACT?

S1c PREP §3.3's LOC budget allocates ~190 LOC across stages S4-S6:

| Stage | Lemma | LOC | Status |
|---|---|---|---|
| S2 (D) | `m_jump_downward_ivt` | ~50 | ✅ PR #18381 |
| S4 (D′) | `m_jump_upward_ivt` | ~50 | 🟡 PR #18693 in flight |
| S5 | `step_in_bounded_alphabet_level_coverage` | ~60 | pending |
| S6 | `step_in_bounded_alphabet_card_bound` (B′ main) | ~80 | pending |

The S2 (D) and S4 (D′) lemmas are clean Mathlib sign-flips of each other and
each transfer verbatim from the parent's `unit_decrement_downward_ivt`.

S5 and S6 — the *bridge* from the IVTs to the count bound — are the
non-mechanical part. This PREP audits the §3.2 bridging argument before
anyone writes Lean for it, on the suspicion (raised when re-reading §3.2
against the parent `BallotProblemOQ01.lean` infrastructure) that the sketch
silently transfers parent machinery whose hypotheses fail under the two-sided
alphabet.

## §1. Three concrete issues with S1c §3.2

### §1.1 Issue 1 — Arithmetic typo in the conclusion

The §3.2 conclusion line reads:

> ```
> | goodRotations | ≥ ⌈l.sum / m⌉ − (m − 1) · l.length / l.sum
> ```
>
> Rearranging gives B′ (the (m − 1) · l.length slack absorbs the
> discrepancy between witness steps and good rotations).

This expression mixes a rational ceiling `⌈l.sum / m⌉` with the integer
quotient `(m − 1) · l.length / l.sum` whose denominator is the input parameter
`l.sum`. There is no rearrangement of this inequality that yields B′:

**Intended bound (B′)** (knowledge.md:82–88):
```
l.sum ≤ m · (goodRotations l).card + (m − 1) · l.length
```

Equivalently, dividing by `m`:
```
(goodRotations l).card ≥ (l.sum − (m − 1) · l.length) / m
```

The factor `1 / l.sum` in §3.2's expression has no origin in this rearrangement.
The likely intended sketch is:

```
| goodRotations | ≥ ⌈ (l.sum − (m − 1) · l.length) / m ⌉
```

— which collapses to `≥ ⌈l.sum / m⌉` only when `l.length = 0` (degenerate)
and is the right shape to combine with later "level-counting".

**Severity**: Cosmetic-arithmetic, not load-bearing. The bound is recoverable.

### §1.2 Issue 2 — "Witness-step → good-rotation" map is unjustified

This is the load-bearing issue.

§3.2 writes:

> Each "witness step" `k_v` lies in some good rotation (by the cycle-lemma
> rotation argument). Therefore: ...

The phrase **"by the cycle-lemma rotation argument"** silently invokes the
{+1, -k} cycle-lemma map `levelPos → good rotation`, formalised in the parent
file `BallotProblemOQ01.lean:703–725` via `levelPos_eq` and (line 731)
`goodRotations_card_ge`. The bridge constructs *one specific* good rotation
per level by:

1. Defining `levelPos l n` = rightmost position `j` with
   `prefixSum l j ≤ minPrefixSum l + n`.
2. **Proving `prefixSum l (levelPos l n) = minPrefixSum l + n` exactly**
   (`levelPos_eq`).
3. Showing this position is a good rotation
   (`rightmostAtLevel_good`, called from line 744–751).

Step 2's proof at `BallotProblemOQ01.lean:714–721` reads:

```
have helem : l[levelPos l n] = (1 : ℤ) := by
  rcases hmem l[levelPos l n] (List.getElem_mem hj_lt) with h1 | hk
  · exact h1
  · exfalso
    have hstep : prefixSum l (levelPos l n + 1) = prefixSum l (levelPos l n) + l[levelPos l n] := by
      simp only [prefixSum]; exact List.sum_take_succ l (levelPos l n) hj_lt
    rw [hstep, hk] at hj1_gt
    linarith [show (0 : ℤ) ≤ k from Int.natCast_nonneg k]
```

The crucial hypothesis is `hmem : ∀ x ∈ l, x = 1 ∨ x = -(k : ℤ)` — the
{+1, -k} alphabet dichotomy. The `helem` derivation **rules out the `-k`
branch by contradiction** (lines 717–721), which only works because the
positive branch is *exactly* +1 (so the prefix sum at `levelPos l n + 1` lands
*one step* past `minPrefixSum l + n`, matching maximality).

Under the two-sided alphabet `−m ≤ x ≤ m` with `m ≥ 2`:

- The positive branch `x = 1` is replaced by `x ∈ {1, 2, …, m}`.
- The case-elimination "rules out the negative branch" is unchanged
  (`x = -k`-style negatives still drop the prefix sum), but the positive
  branch **no longer pins** `prefixSum l (levelPos l n)` to
  `minPrefixSum l + n`.
- Concretely: if `l[levelPos l n] = 2` and `m = 2`, then
  `prefixSum l (levelPos l n + 1) = prefixSum l (levelPos l n) + 2`, so
  `prefixSum l (levelPos l n)` could be `minPrefixSum l + n − 1` and step
  to `minPrefixSum l + n + 1`, *skipping* the level `minPrefixSum l + n`.

D′ (the upward IVT, PR #18693) only delivers a position with `prefixSum` in
`[v, v + m − 1]` for the level `v` — *not* a position at `v` exactly. There
is **no levelPos_eq analogue** for the two-sided alphabet; the bridge
`level → exact position` collapses to `level → m-window of positions`.

The S1c §3.2 sketch silently treats the m-window as if it were point-valued
("each witness step `k_v` lies in some good rotation"). Without a separate
`window_position_good` argument, this step is *not* an instance of the parent
machinery — it is a *new* technical obligation that must be proved.

**Severity**: Structural. The §3.2 bridging argument as written is not a
proof; it is a hope that a parent-style argument extends. Below, §2 shows
which parent machinery transfers and which does not.

### §1.3 Issue 3 — Witness-step injectivity argument is in the wrong direction

§3.2 §"Step 2 — count argument" writes:

> These steps are *not necessarily distinct* across `v`, but at most `m`
> levels can map to the same step (since `prefixSum l k_v ∈ [v, v + m − 1]`
> is a length-`m` window). So:
> ```
> #{ distinct steps that witness some level } ≥ l.sum / m.
> ```

This gives a lower bound on **witness positions**, not on **good rotations**.
The parent's `goodRotations_card_le` (`BallotProblemOQ01.lean:563`) already
delivers the *upper* bound `|gR| ≤ l.sum.toNat` via the *step → good-rotation*
injection (line 591 `Finset.card_image_of_injOn`); this is the dual direction.

To get a *lower* bound on `|gR|`, the §3.2 argument must inject
`{witness positions}` *into* `goodRotations l`, not the other way around. The
{+1, -k} parent achieves this via `levelPos_eq` (each level pins to a unique
position) + `rightmostAtLevel_good` (that position is good). Neither
transfers for the two-sided alphabet (Issue 2).

The §3.2 inequality `#{distinct witness steps} ≥ l.sum / m`, even if granted,
does not constrain `|gR|` because the witness positions are not (yet) known
to be good rotations.

**Severity**: Structural — same root cause as Issue 2 (the missing
levelPos-eq analogue).

## §2. Parent-machinery transfer table

Sorting the parent's `BallotProblemOQ01.lean` lemmas by transferability:

| Component | Source line | Hypothesis | Transfers to two-sided? |
|---|---|---|---|
| `goodRotations_card_le` | `:563` | only `0 < l.sum` | ✅ Yes — works for any `l` |
| `goodRotation_prefixSum_injective` | `:579` | only `0 < l.sum` | ✅ Yes |
| `goodRotations_nonempty` | `:494` | `0 < l.length`, `0 < l.sum` | ✅ Yes (this is conjecture A) |
| `cyclicRotation_prefixSum` (algebraic identity) | `:328` | none | ✅ Yes |
| `prefixSum_rightmostMinPos` | `:439` | none | ✅ Yes |
| Downward step bound | parent S1 `:41` | `step ≥ -1` | ✅ D = `m_jump_step_bound` (S2, this slug, line 34) |
| Downward IVT | parent S1 `:60` | `step ≥ -1` | ✅ D = `m_jump_downward_ivt` (S2 PR #18381) |
| Upward step bound | (none in parent) | implicit | 🟡 PR #18693 (in flight) |
| Upward IVT | (none in parent) | implicit | 🟡 PR #18693 (in flight) |
| `unit_decrement_levels_achieved` | parent S1 `:104` | `step ≥ -1` | 🟡 m-window version (relaxes "exact level" to "m-window") |
| `levelPos_eq` | parent `:703` | **alphabet ⊆ {1, -k}** | ❌ Fails for two-sided |
| `rightmostAtLevel_good` | parent (helper for `:731`) | **alphabet ⊆ {1, -k}** | ❌ Fails for two-sided |
| `goodRotations_card_ge` | parent `:731` | **alphabet ⊆ {1, -k}** | ❌ Fails for two-sided (uses both blocked helpers) |

The **green rows** are all the infrastructure the S5 bridge can rely on
without new mathematics. The **red rows** are precisely the machinery the
§3.2 sketch silently invokes.

## §3. Two paths forward

### §3.1 Path A — relaxed bridge (ambitious; new mathematics)

Replace the level-position pin `levelPos_eq` with a *window-position* version:

```lean
def windowPos (l : List ℤ) (m : ℕ) (v : ℤ) : ℕ :=
  -- rightmost position j ≤ l.length with prefixSum l j ≤ v + m - 1
  -- (existence guaranteed by D + D′ when v ∈ [minPrefixSum, l.sum])
```

Two new obligations beyond Mathlib + D + D′:

1. **`windowPos_eq_window`**: `prefixSum l (windowPos l m v) ∈ [v, v + m − 1]`.
   This is the m-window analog of `levelPos_eq`; proof uses D′ (the upward
   IVT) on positions to the right of `windowPos l m v` combined with
   maximality on positions to the left.

2. **`windowPos_good`**: `isGoodRotation l (windowPos l m v)`. This is the
   m-window analog of `rightmostAtLevel_good`. **The proof is not a sign-flip
   of the parent**: the parent's `rightmostAtLevel_good` argument relies on
   prefix-sum values being *exact* at the witness position (so that the
   rotation's prefix sums step through `[1, S]` cleanly). With prefix-sum
   values living in a *window*, the rotation's prefix sums acquire a
   `[−(m − 1), 0]` slack that must be absorbed by the conclusion. Specifically:

   - Pick `v ∈ [1, l.sum − (m − 1) · l.length]` (the "safe" range where the
     count bound has positive RHS).
   - Show that for `i = windowPos l m (v − l.sum + minPrefixSum l)` (or some
     normalised analogue), the cyclic rotation starting at `i` has all
     prefix sums `≥ 1 − (m − 1)`.
   - That `1 − (m − 1) = 2 − m` can be ≤ 0 for `m ≥ 2`, so the cyclic
     rotation is **not** automatically a good rotation (good rotations
     require strict positivity).

   Net: we need additional slack in the count bound to absorb the m-window
   imprecision. This is the role of the `(m − 1) · l.length` slack in B′.

**LOC estimate**: 200–300 (not the 60+80 in S1c §3.3), because
`windowPos_good` is new mathematics: the parent's `rightmostAtLevel_good`
proof is ~70 LOC in unexported helpers (`levelPos_max`, `levelPos_eq`,
`rightmostAtLevel_good` itself), and the m-window version needs to re-prove
each piece with a width-m relaxation.

**Risk**: the very thing the `(m − 1) · l.length` slack absorbs may not be
absorbable — in which case B′ as stated is too tight and needs further
weakening. Small-case checks in §4 below do not refute B′ but do not prove
its tightness either.

### §3.2 Path B — scope down (safer; preserves parent machinery)

Strengthen B′'s hypothesis from "two-sided `−m ≤ x ≤ m`" to
"one-up `+1` plus mixed negatives in `{−1, −2, …, −m}`":

```lean
theorem step_in_one_pos_neg_m_card_bound
    (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, x = 1 ∨ (∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ x = -(k : ℤ)))
    (hS : 0 < l.sum) :
    l.sum ≤ (m : ℤ) * (goodRotations l).card + (m − 1 : ℤ) * l.length
```

Under this hypothesis, the levelPos machinery transfers verbatim:

- `helem` (parent line 714) still rules out negative branches and pins the
  positive branch to `x = 1` — exactly the dichotomy the parent uses.
- `levelPos_eq` extends without modification (the parent's case-analysis only
  needs `linarith [show (0 : ℤ) ≤ k from Int.natCast_nonneg k]`, which holds
  for any `k ∈ {1, …, m}`).
- `rightmostAtLevel_good` extends without modification.
- The lower bound `|gR| ≥ l.sum.toNat` (an *equality* in the {+1, -k} case,
  generalising to `|gR| ≥ l.sum.toNat` here) carries over.

Combined with `goodRotations_card_le` (transfers), this yields
**`|gR| = l.sum.toNat`** in the one-up-mixed-down setting — *stronger* than
B′'s `l.sum ≤ m · |gR| + (m − 1) · l.length` and *not* requiring D′.

**LOC estimate**: ~80, mostly verbatim from `BallotProblemOQ01.lean:599–774`
with `hmem` weakened to `x = 1 ∨ x = -(k : ℤ) for some k ∈ {1, …, m}`.

**Cost**: B′ in this scope is *not* the full two-sided alphabet bound. The
S1c PREP's framing of B′ as "the genuine m-generalization of the cycle lemma
under symmetric alphabets" is *not* achieved — the `+1` up-step asymmetry
remains.

**Honesty marker**: Path B is essentially **conjecture E enlarged** to
include `-1, -2, …, -m` rather than only `-m`. The parent's `{+1, -k}` lemma
(`BallotProblemOQ01.lean:cycle_lemma`) covers a *single* `k`; Path B covers
multiple `k`'s simultaneously. This is mathematically a smaller step than
"two-sided alphabet" and should be labelled accordingly in any S5 ACT.

### §3.3 Recommended action

**Defer S5 ACT in either scope** pending the choice:

- Path A is the genuine B′; it requires ~200 LOC of new technical work and
  may not close cleanly (the slack absorbed by `(m − 1) · l.length` is not
  proven sufficient by small cases — see §4).
- Path B is a 80-LOC enlargement of conjecture E; it succeeds with high
  probability but does *not* answer the originally-posed B′ question.

A reasonable next action is **either**:

1. **S5b PREP — write Path A's `windowPos_good` proof obligation in detail**
   and stress-test it against tight cases (e.g., the `(2k+1)`-stress family
   in §4.3 below) to see whether the `(m − 1) · l.length` slack actually
   absorbs the m-window imprecision *for all alphabets*, not just the cases
   checked.
2. **S5c PREP — verify Path B's transfer-to-mixed-negatives proof obligation**
   line-by-line against the parent, listing every place where the alphabet
   dichotomy is invoked and confirming it survives `k ∈ {1, …, m}`. ETA: ~1
   session.

The S5 ACT (Lean code) should not start until one of these is grounded.

## §4. Small-case verification — extended

### §4.1 Re-check S1c §2 cases (B′ on m ∈ {2, 3})

The S1c §2 table (11 cases) all satisfy B′. Re-verified for this PREP — no
discrepancies.

### §4.2 New stress cases (B′ on m = 2)

| l | sum | length | |gR| | LHS = sum | RHS = m·|gR| + (m−1)·len | ✓ |
|---|---|---|---|---|---|---|
| `[2, 2, 2, -2]` | 4 | 4 | 2 | 4 | 2·2 + 4 = 8 | ✓ |
| `[2, 2, 2, -2, -2]` | 2 | 5 | 1 | 2 | 2 + 5 = 7 | ✓ |
| `[2, 2, 2, 2, 2, -2, -2, -2, 1]` | 5 | 9 | 1 | 5 | 2 + 9 = 11 | ✓ |
| `[2, -1, 2, -1, 2, -1]` | 3 | 6 | 3 | 3 | 6 + 6 = 12 | ✓ |
| `[2, -1, 2, -1, 2, -1, 2, -1]` | 4 | 8 | 4 | 4 | 8 + 8 = 16 | ✓ |

Hand-verifications:

- `[2, 2, 2, -2]`: rotation starting at i ∈ {0,1}: `[2,2,2,-2]` prefix sums
  2,4,6,4 — good; `[2,2,-2,2]` prefix sums 2,4,2,4 — good; i=2,3 fail.
  |gR|=2.
- `[2, 2, 2, -2, -2]`: only i=0 (`[2,2,2,-2,-2]` prefix sums 2,4,6,4,2) works;
  others have a zero or negative crossing. |gR|=1.
- `[2, 2, 2, 2, 2, -2, -2, -2, 1]`: i=8 (trailing 1) gives `[1,2,2,2,2,2,-2,-2,-2]`
  prefix sums 1,3,5,7,9,11,9,7,5 — good; others fail (e.g., i=0 reaches
  prefix sum 0 at j=8). |gR|=1.

The `[2, -1, 2, -1, ...]` family has every even-indexed rotation good
(starting with `2`) and every odd-indexed rotation fails (starts with `-1`
that brings prefix sum to `-1`). For even-length `2k`, |gR| = k.

All 5 new stress cases satisfy B′ with substantial slack (LHS / RHS ratio
varies from 0.25 to 0.5 in the cases above).

### §4.3 Tightness probe — when does B′ approach equality?

For `l = [m, -1]^k` (k copies of `(m, -1)`, m ≥ 2): sum = `(m − 1) k`,
length = `2k`, |gR| = `k` (every even-indexed rotation good as above).

B′ bound: `(m − 1) k ≤ m · k + (m − 1) · 2k = (3m − 2) k`. Ratio
LHS/RHS = `(m − 1) / (3m − 2)`. For m = 2: 1/4. For m → ∞: 1/3. **Bound is
loose by ≥ 3×**.

For `l = [m, m, …, m]` (all-positive, k copies of m): sum = `mk`,
length = `k`, |gR| = `k`. B′ bound: `mk ≤ mk + (m − 1) k = (2m − 1) k`.
Ratio: `m / (2m − 1)`. For m = 2: 2/3. For m → ∞: 1/2. **Bound is loose by
≥ 1.5×**.

For `l = [m, -m]^k ++ [1]` (alternating long, ending in 1; sum = 1,
length = 2k+1, |gR| = 1): B′ bound: `1 ≤ m + (m − 1)(2k + 1)`. **Bound is
loose by O(m·k)**.

**Conclusion**: B′ is *very* loose. The slack `(m − 1) · l.length` is rarely
near-tight on the cases checked. This **does not** prove B′ correct
(we have not constructed an adversarial case where `|gR|` is constrained from
below by the level structure rather than by trivial `≥ 1`), but **does**
suggest that even if Path A's `windowPos_good` proof loses some additional
factor in the slack, B′ as stated is likely to hold.

### §4.4 C′ small-case check (sharper slack `(m − 1) · |negative-steps|`)

C′ candidate: `l.sum ≤ m · |gR| + (m − 1) · |{i : l[i] < 0}|`.

| l | sum | |gR| | |neg| | RHS = m·|gR| + (m−1)·|neg| | ✓ |
|---|---|---|---|---|---|
| `[2, 2, 2, -2]` | 4 | 2 | 1 | 2·2 + 1·1 = 5 | ✓ |
| `[2, 2, 2, -2, -2]` | 2 | 1 | 2 | 2 + 2 = 4 | ✓ |
| `[2, -1, 2, -1]` | 2 | 2 | 2 | 4 + 2 = 6 | ✓ |
| `[2, -1, 2, -1, 2, -1]` | 3 | 3 | 3 | 6 + 3 = 9 | ✓ |
| `[m, m, …, m, -m, -m, …, -m, 1]` (k m's, k -m's, 1) | 1 | 1 | k | 2 + k | ✓ |
| `[2, 2, 2, 2, 2, -2, -2, -2, 1]` | 5 | 1 | 3 | 2 + 3 = 5 | ✓ (tight!) |

The last row is the first **tight** case observed: LHS = RHS = 5. This is
genuine evidence for C′ being tight, not loose like B′. It also suggests
the C′ slack `(m − 1) · |negatives|` is the *correct* form to target after
B′ is settled.

(Note: §9-question-2 in S1c PREP raised C′ explicitly. This small-case data
does not refute C′; constructing a refutation likely requires concentrated
positives + many negatives, similar to the [K, -m] refutation of B and C
but adapted to the two-sided alphabet.)

## §5. Mathlib API surface (unchanged from S1c)

No new Mathlib dependencies anticipated. All primitives used by both Path A
and Path B are present at the same v4.26.0 pinned rev as the S2 ACT:

| Symbol | Module | Used for |
|---|---|---|
| `Finset.min'`, `Finset.min'_mem`, `Finset.min'_le` | `Mathlib.Data.Finset.Lattice` | leftmost crossing (D, D′) |
| `Finset.max'`, `Finset.max'_mem`, `Finset.max'_le` | `Mathlib.Data.Finset.Lattice` | rightmost level (Path A's `windowPos`) |
| `Finset.card_image_of_injOn` | `Mathlib.Data.Finset.Card` | injection from levels to good rotations |
| `Finset.card_le_card_of_injOn` | `Mathlib.Data.Finset.Card` | lower bound via injection |
| `List.sum_take_succ` | `Mathlib.Data.List.Basic` | prefix-sum recurrence |
| `List.getElem_mem` | `Mathlib.Data.List.Basic` | element membership |

## §6. Anti-targets / race-safety

- **No Lean code changes.**
- **No edits** to `state.md`, `knowledge.md`, `problem.md`, gallery JSON,
  or any file outside this single new sessions/ note.
- **Race-safety probe** (2026-05-13 ~08:35 UTC):
  - `gh pr list --repo rjwalters/lean-genius --search "ballot-problem-oq-01-oq-01-oq-02-oq-01 in:title" --state open`
    → only #18693 (S4 ACT D′, edits Lean file + adds `sessions/2026-05-13-s4-act-m-jump-upward-ivt.md`).
  - This PR adds `sessions/2026-05-13-s5-prep-discharge-sketch-audit.md`,
    different filename, no overlap.
- **No build run** — this is doc-only, and the worktree's `proofs/.lake`
  symlink is in the loop documented in memory
  `feedback_researcher_lake_symlink_loop_and_wipe.md`.

## §7. Honest contribution boundary

What this PREP **does**:

- Identifies a cosmetic arithmetic typo in S1c §3.2 (Issue 1).
- Identifies a structural gap in S1c §3.2: the witness-step → good-rotation
  map silently invokes parent machinery (`levelPos_eq` +
  `rightmostAtLevel_good`) whose alphabet dichotomy hypothesis fails for the
  two-sided `−m ≤ x ≤ m` setting (Issue 2).
- Identifies that the level-counting bound (Issue 3) constrains witness
  positions, not good rotations — and so does not yield a lower bound on
  `|gR|` as §3.2 claimed.
- Maps parent machinery into transfer / no-transfer table (§2).
- Sketches two recovery paths: Path A (relaxed bridge, ~200 LOC, genuine new
  mathematics) and Path B (scope-down to mixed-`-k`, ~80 LOC, preserves
  parent machinery but does not answer B′).
- Adds 5 new stress cases for B′ and 6 stress cases for C′ (one of which is
  tight, providing the first observed C′ tightness witness).

What this PREP **does NOT** do:

- It does not prove or refute B′ in either scope.
- It does not write any Lean code.
- It does not propose Path A's `windowPos_good` proof in detail; that is a
  separate S5b PREP obligation.
- It does not verify Path B's transfer line-by-line; that is a separate S5c
  PREP obligation.
- It does not modify `state.md`. The slug's phase remains OBSERVE with
  active-approach "S2 ACT (conjecture D)" — the post-S2/S4 status update is
  a future state.md edit.
- It does not propose merging with `BallotProblemOQ01.lean`'s `cycle_lemma`
  result for the {+1, -k} case; that bridge would require a fresh sub-OQ.

## §8. Open questions for the S5 ACT author (or next PREP author)

1. **Is Path A's `windowPos_good` actually true?** That is, given the
   rightmost position `j` with `prefixSum l j ≤ v + m − 1`, is the cyclic
   rotation starting at `j` necessarily good? Small cases (§4.2) do not
   refute it, but neither do they establish it across all two-sided
   alphabets. Need to either find a counterexample or attempt the proof.

2. **Does the `(m − 1) · l.length` slack in B′ absorb Path A's m-window
   imprecision?** §4.3 shows B′ is loose on observed cases by factor 2-3×.
   Path A's `windowPos_good` failure modes (if any) would impose additional
   slack; need to verify this fits within `(m − 1) · l.length`.

3. **Does Path B's mixed-negative `{1} ∪ {−1, …, −m}` transfer require any
   adaptation in `levelPos_max`/`levelPos_eq`?** The parent's case-analysis
   `linarith [show (0 : ℤ) ≤ k]` uses only `k ≥ 0`; this should survive any
   `k ∈ {1, …, m}` substitution, but verifying it line-by-line is the S5c
   PREP obligation.

4. **Is the §4.4 tight C′ case (`[2, 2, 2, 2, 2, -2, -2, -2, 1]`) generic
   enough to characterise C′-tight families?** A characterisation would
   inform whether C′ requires a strictly stronger technique than B′ or
   reduces to B′.

5. **Should the S5 ACT first establish a weaker B′-trivial?**
   `l.sum ≤ m · |gR| + (m − 1) · l.length` is implied by the trivial bound
   `l.sum ≤ m · l.length` whenever `|gR| ≥ ⌈l.length · 1 / m⌉` — but
   counterexamples (e.g., `[m, m, m, -m, -m]` with `|gR| = 1 < ⌈5/2⌉ = 3`)
   show this implication is *not* universal. The trivial slack
   `(m − 1) · l.length` does not suffice on its own; some level-counting is
   genuinely required.

## §9. Summary

S1c PREP §3.2's discharge sketch has one cosmetic and two structural issues
(arithmetic typo, missing `levelPos_eq` analogue, inverted injectivity
direction). The {+1, -k} parent machinery is the source of the silent
borrow; it does *not* extend to the two-sided `−m ≤ x ≤ m` alphabet without
a new `windowPos_good`-style technical result.

Two recovery paths exist: Path A (ambitious, ~200 LOC, genuinely new) and
Path B (scope-down to mixed-`-k`, ~80 LOC, preserves parent machinery but
weakens B′'s statement). Recommended next action is an S5b/S5c PREP to
ground one of these before any Lean ACT.

Small-case checks (§4) do not refute B′ and provide the first observed C′
tight case (`[2, 2, 2, 2, 2, -2, -2, -2, 1]`); B′ as stated remains loose
by ≥ 2× on every checked case.
