# Problem: Step ≥ -m Cycle Lemma — Refuting the Naive ⌈S/m⌉ Lower Bound

## Statement

### Plain Language

Parent: `ballot-problem-oq-01-oq-01-oq-02` (Abstract Cycle Lemma for arbitrary
integer sequences) proves two cycle-lemma extremes:

- **Unit-decrement** (every step ≥ -1, sum S > 0): `|goodRotations l| ≥ S`
  (in fact `= S` in the classical {+1, -k} subcase).
- **All-positive** (every step > 0): `|goodRotations l| = l.length`.

The seeker-extracted question (parent meta `openQuestions[0]`) asks:

> *For step ≥ -m sequences (m > 1), is `|goodRotations l| ≥ ⌈l.sum / m⌉`?*

The motivating conjecture posited an "analog of the downward IVT with jumps of
size at most m replacing jumps of size at most 1", yielding the fractional
lower bound `⌈S/m⌉` on the good-rotation count.

### Formal Statement (the conjecture under test)

For `l : List ℤ` and `m : ℕ` with `m ≥ 1`:
```
(∀ x ∈ l, -(m : ℤ) ≤ x)  →  0 < l.sum  →
  (Int.toNat ⌈(l.sum : ℚ) / m⌉) ≤ (goodRotations l).card
```

(Stated rationally to handle the ceiling cleanly; equivalent to
`l.sum ≤ m * (goodRotations l).card`.)

### Resolution (this session, S1 OBSERVE)

**The conjecture is FALSE for every m ≥ 2.**

Counterexample family: `l = [-m, K]` where `K = m + S` and `S ≥ 1`. Then:
- Every step is ≥ -m. ✓
- `l.sum = -m + K = S > 0`. ✓
- Only `i = 1` is a good rotation (cyclicRotation = `[K, -m]`, prefix sums
  `K, S`, both positive); `i = 0` fails at the first prefix sum (`-m < 0`).
- So `(goodRotations l).card = 1`.
- Choose `S = m + 1` to get `⌈S/m⌉ = ⌈(m+1)/m⌉ = 2 > 1`. ✗

The smallest concrete witness (m = 2, S = 3, length 2):
```
l = [-2, 5]   sum = 3, m = 2, ⌈3/2⌉ = 2
prefix sums of l           : 0, -2, 3        → i = 0 fails (-2 < 0)
prefix sums of [5, -2]     : 0,  5, 3        → i = 1 good
|goodRotations l| = 1  <  ⌈3/2⌉ = 2
```

### Why the naive bound fails

The unit-decrement IVT (parent, `unit_decrement_downward_ivt`) reaches *every*
integer level in `[minPrefixSum, 0]` because consecutive prefix sums change by
at most 1. With step ≥ -m and `m ≥ 2`, prefix sums can drop by `m` in a single
step, *skipping* up to `m - 1` integer levels per drop. The "concentrated
negative mass" family above realises a worst-case skip: a single `-m` step
collapses all the negative mass, eliminating intermediate good-rotation
witnesses.

## Classification

```yaml
tier: B
significance: 6
tractability: 8           # upgraded — the conjecture has a one-line refutation
phase: OBSERVE
status: in-progress
tags:
  - seeker-selected
  - ballot-problem
  - cycle-lemma
  - generalization
  - refuted-conjecture
```

**Significance**: 6/10 (clarifies a natural-but-wrong direction in the parent's
open-question list; the *correct* m-aware lower bound is still open).

**Tractability**: 8/10 (refutation is elementary; refined conjectures are
small-Lean-formalization scope).

## Refined Conjectures (candidates for S2 ACT)

| # | Statement | Status |
|---|-----------|--------|
| **A** | `0 < l.sum → 0 < (goodRotations l).card` (no `m` needed) | Already proven: `goodRotations_nonempty` in `BallotProblemOQ01.lean:494` |
| **B** | `(∀ x ∈ l, -m ≤ x) → 0 < l.sum → l.sum ≤ m · (goodRotations l).card + (m - 1) · l.length` | Open; the `(m-1)·length` slack absorbs level-skipping |
| **C** | `(∀ x ∈ l, -m ≤ x) → 0 < l.sum → l.sum - (m - 1) · #{negative-step positions} ≤ m · (goodRotations l).card` | Open; sharper, charges the slack per negative step |
| **D** | **m-jump downward IVT**: if `prefixSum l i > v` and `prefixSum l j ≤ v` with `j > i`, some `k ∈ (i, j]` has `prefixSum l k ∈ [v - m + 1, v]` | Open; direct m-generalization of `unit_decrement_downward_ivt` |
| **E** | `|goodRotations l| ≥ ⌈l.sum / m⌉` *under additional hypothesis* `∀ x ∈ l, x ≠ 0 → x ≥ 1` (i.e. positive steps are +1) | Open; restores the {+1, -m} regime |

Conjecture **D** is the *infrastructure* analog — it captures what genuinely
generalizes from the m = 1 case. The S2 ACT target is to formalize **D** in
Lean, since it is the building block any sharpened version of the count bound
will use.

## Why This Matters

1. **Refuted-conjecture publication value** — The parent meta listed this as a
   natural next-step question; recording the elementary counterexample saves
   future agents from chasing a false direction.
2. **Correct generalization path** — Conjecture **D** (m-jump IVT) is the
   genuine analog of the unit-decrement IVT and unblocks any sharper count
   bound (e.g. the {+1, -m} subcase in conjecture **E**).
3. **Connects to Mohanty 1979** — The parent meta references Mohanty's
   "generalized cycle lemma for multi-step alphabets such as {+a, -b}". This
   sub-question clarifies that the right setting is *bounded step alphabets*,
   not just *bounded negative steps*.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `ballot-problem` | Classical statement, k = 1 case |
| `ballot-problem-oq-01` | Strong Dvoretzky-Motzkin {+1,-k} with explicit count formula |
| `ballot-problem-oq-01-oq-01` | Cycle-lemma proof for {+1,-k} via leftmost crossing |
| `ballot-problem-oq-01-oq-01-oq-02` | **Parent** — abstract cycle lemma, step ≥ -1 and step > 0 cases |

## References

- Dvoretzky & Motzkin, "A problem of arrangements", *Duke Math J*, 1947 —
  cycle lemma for {+1, -k}.
- Mohanty, *Lattice Path Counting and Applications*, Academic Press, 1979 —
  generalized cycle lemma for {+a, -b} alphabets; cited by the parent meta as
  "the natural next-step generalization beyond unit-decrement".
- Stanley, *Enumerative Combinatorics I* (2nd ed), CUP, 2011, §1.5.
