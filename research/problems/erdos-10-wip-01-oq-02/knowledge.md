# Knowledge Base: erdos-10-wip-01-oq-02

## Session 2026-07-02 (researcher-6) — SOLVED (ACT): shipped verified 0-axiom file

**Outcome**: COMPLETED. Formalized the pinned target as
`proofs/Proofs/Erdos10WIP01OQ02.lean` (203 LOC, 10 thm / 1 def, 0 sorry / 0 axiom,
self-contained on Mathlib), host-verified 0-axiom (`#print axioms` = propext /
Classical.choice / Quot.sound only). Also created the gallery entry
`src/data/proofs/erdos-10-wip-01-oq-02/`.

**Main result** `popcount_add_eq_iff`:
`popcount (a + b) = popcount a + popcount b ↔ a &&& b = 0`
— equality in the parent's subadditive bound holds exactly on disjoint binary supports
(no carries). Plus strict corollary `popcount_add_lt` (`a&&&b ≠ 0 ⇒ strict <`).

**Proof method** (matches the ORIENT plan, but *without* the exact xor/and identity —
a cleaner route): one binary parity strong induction on `a+b`. Building blocks all proved
in-file: popcount recursions `popcount(2n)=popcount n`, `popcount(2n+1)=popcount n+1`
(from Mathlib `bitIndices_two_mul(_add_one)`); the three `&&&` parity recursions
`(2a)&&&(2b)=2(a&&&b)`, `(2a+1)&&&(2b)=2(a&&&b)`, `(2a+1)&&&(2b+1)=2(a&&&b)+1` (via
`Nat.eq_of_testBit_eq`, applying `testBit_and` before `testBit_succ`); subadditivity
`popcount_add_le` re-derived by the same induction (so no dependency on the parent's
`RepWithAtMost` machinery — the file imports only Mathlib). The odd/odd case is the crux:
a carry is born, `a&&&b` becomes odd (=`2(a'&&&b')+1 ≠ 0`) and popcount strictly drops, so
both sides of the iff are false; the other three parity cases halve `a&&&b` and reduce to
the IH on the halved sum. The seeker's false lower-bound alternative (refuted at `(1,7)`)
is documented in the file docstring.

**Note**: the ORIENT plan's exact identity `popcount a + popcount b = popcount(a^^^b) +
2·popcount(a&&&b)` and the testBit↔bitIndices membership bridge were NOT needed — the
parity induction on `a+b` is a shorter, fully-elementary route. Aristotle not used
(host `lake env lean` worked in a narrow-import clean window despite concurrent-agent
cache corruption).


ORIENT-phase analysis (researcher-9, 2026-07-02).

Parent: `Erdos10WIP01.lean` proved **binary popcount is subadditive**

```
popcount (a + b) ≤ popcount a + popcount b        -- bitIndices_length_add_le
```

where `popcount n := (Nat.bitIndices n).length` is the number of binary 1-bits.
This open question asks for a *matching lower bound* or a *characterization of
equality* in that subadditive bound.

---

## Problem Understanding

The seeker note proposes two alternatives:

1. a matching lower bound `popcount(a+b) ≥ |popcount a − popcount b|`, **or**
2. characterize equality (no carries) in the subadditive bound.

### Alternative (1) is FALSE — do not attempt it.

`popcount(a+b) ≥ |popcount a − popcount b|` is refuted by an explicit
counterexample. Take `a = 1`, `b = 7`:

```
popcount 1 = 1,  popcount 7 = 3,  a + b = 8,  popcount 8 = 1
|popcount 1 − popcount 7| = 2  >  1 = popcount 8.
```

An exhaustive check over `0 ≤ a,b < 64` finds **142** counterexamples; the
lexicographically smallest is `(a,b) = (1,7)`. Adding a low bit to a
high-popcount number can *cascade carries* and collapse popcount to `1`
(`0b0111 + 1 = 0b1000`), so `popcount(a+b)` has **no** nontrivial general lower
bound in terms of `popcount a`, `popcount b`. The intuition "addition can only
lose bits by a bounded amount" is wrong: a single carry chain can annihilate an
arbitrarily long run of 1-bits.

**Conclusion:** the correct, well-posed target is alternative (2), the equality
characterization.

---

## The correct target (well-posed, verified true numerically)

> **Equality characterization.** For all `a b : ℕ`,
> ```
> popcount (a + b) = popcount a + popcount b   ↔   a &&& b = 0.
> ```

i.e. equality in the subadditive bound holds **exactly** when `a` and `b` have
disjoint binary supports (no position where both have a 1-bit), which is exactly
the "no carries" condition. Verified by brute force for all `a,b < 256`:
`(popcount(a+b) = popcount a + popcount b) ↔ (a &&& b = 0)` is `True` on the
whole square, and `a &&& b ≠ 0 ⇒ popcount(a+b) < popcount a + popcount b`
(strict) also holds throughout.

Note carries can still *propagate* through positions where only one operand has
a bit, but a carry can only be *born* at a position where both operands have a
1-bit; hence "no carries anywhere" ⟺ "no shared 1-bit" ⟺ `a &&& b = 0`.

---

## The clean engine: an exact popcount/carry identity

The sharpest supporting lemma (proves both directions at once and gives the
strict inequality for free) is the classical exact identity

> **`popcount a + popcount b = popcount (a ^^^ b) + 2 · popcount (a &&& b)`.**

Reason: split bit positions into three disjoint classes — *both* set
(contributes `2` to the left, `0` to `a^^^b`, `1` to `a&&&b`), *exactly one*
set (contributes `1` to the left, `1` to `a^^^b`, `0` to `a&&&b`), *neither*
(contributes `0` everywhere). `a^^^b` and `a&&&b` have disjoint supports, so
their popcounts are literal cardinalities of the "exactly-one" and "both" bit
sets.

Combined with the base recursion of binary addition
`a + b = (a ^^^ b) + 2 · (a &&& b)` (add without carry, then the carries shifted
up by one) and `popcount (2 * n) = popcount n`, this yields, by strong
induction on `a + b`,

> **`popcount a + popcount b − popcount (a + b) = (number of carries) ≥ 0`,**

and equality `popcount(a+b) = popcount a + popcount b` iff there are zero
carries iff `a &&& b = 0`. The strict corollary

> **`a &&& b ≠ 0 ⇒ popcount (a + b) < popcount a + popcount b`**

drops straight out.

---

## Proof plan for Lean (both directions)

### Forward direction (`a &&& b = 0 ⇒ equality`) — the easy half

Work through the existing representation machinery rather than raw carries:

1. `S n := (Nat.bitIndices n).toFinset`. Since `Nat.bitIndices_sorted`
   (`SortedLT`) gives `Nodup`, `popcount n = (S n).card`.
2. `Nat.twoPowSum_bitIndices : (n.bitIndices.map (2 ^ ·)).sum = n`, so
   `n = ∑ i ∈ S n, 2 ^ i`.
3. `a &&& b = 0 ↔ S a ∩ S b = ∅` (via `Nat.testBit_land` + a
   `i ∈ bitIndices n ↔ n.testBit i` membership lemma — **needs locating in
   Mathlib**, see gaps).
4. Disjoint ⇒ `a + b = ∑ i ∈ S a, 2^i + ∑ i ∈ S b, 2^i = ∑ i ∈ S a ∪ S b, 2^i`
   (`Finset.sum_union` on disjoint sets).
5. Binary-expansion uniqueness (`Nat.bitIndices_twoPowsum` for a `SortedLT`
   list, i.e. the sorted merge of `S a ∪ S b`) gives
   `S (a + b) = S a ∪ S b`, hence
   `popcount (a+b) = (S a ∪ S b).card = (S a).card + (S b).card`
   by `Finset.card_union_of_disjoint`.

### Reverse direction (`equality ⇒ a &&& b = 0`) — the hard half

Prove the contrapositive via the exact identity engine above. The load-bearing
lemma is `popcount a + popcount b = popcount (a ^^^ b) + 2 · popcount (a &&& b)`
plus `a + b = (a ^^^ b) + 2 * (a &&& b)` and strong induction on `a + b`
(the pair `(a ^^^ b, a &&& b)` recurses on a strictly smaller sum whenever
`a &&& b ≠ 0`, because `a + b = (a^^^b) + 2(a&&&b)` and re-adding those two is a
smaller instance). This is the delicate part (~50–100 lines of bit
bookkeeping); the exact identity is the right lemma to isolate and hand to
Aristotle once the build/prover environment is back.

---

## Mathlib inventory

Present and usable:
- `Nat.bitIndices`, `Nat.bitIndices_sorted` (`SortedLT`), `bitIndices_zero/one`,
  `bitIndices_two_pow`, `Nat.twoPowSum_bitIndices`, `Nat.bitIndices_twoPowsum`
  (uniqueness for sorted lists) — `Mathlib/Data/Nat/BitIndices.lean`.
- `Nat.testBit_land`, `Nat.testBit_lor`, `Nat.xor_eq_zero`,
  `Nat.zero_of_testBit_eq_false`, `Nat.lor_comm/land_comm` —
  `Mathlib/Data/Nat/Bitwise.lean`.
- Parent lemmas `bitIndices_length_add_le`, `repWithAtMost_add`,
  `popcount_le_iff` — `Erdos10WIP01.lean`.

Gaps to fill (none look deep, all routine):
- **`i ∈ Nat.bitIndices n ↔ n.testBit i`** — a membership↔testBit bridge. Not
  found by name in `BitIndices.lean`; may exist elsewhere or need a short proof
  from `Nat.twoPowSum_bitIndices` + `Nat.testBit_two_pow`.
- **`a &&& b = 0 → a + b = a ||| b`** (disjoint add = or) — no direct lemma
  found in `Nat/Bitwise.lean`; provable from `Nat.testBit_add`/carry lemmas.
- **`popcount a + popcount b = popcount (a^^^b) + 2·popcount(a&&&b)`** — not in
  Mathlib; this is the key new lemma to add (and the ideal Aristotle target).

---

## Dead Ends

- Alternative-(1) lower bound `popcount(a+b) ≥ |popcount a − popcount b|`:
  **false** (counterexample `(1,7)`; 142 counterexamples for `a,b<64`). Do not
  pursue.

## Environment blocker (this session)

- Local Docker/`lake` build impossible: host disk at 100% (≈0.5 GiB free) — any
  build attempt fails on `ENOSPC`.
- Aristotle MCP unavailable this session (`prove` returns `Resource not
  found`), so the reverse-direction lemma could not be offloaded server-side.
- Consequence: shipped as an ORIENT-phase analysis (correct target pinned, false
  direction refuted, full two-direction proof plan, Mathlib gaps enumerated)
  rather than a build-verified Lean file. A follow-up session with a working
  build should formalize the plan above; the forward direction is
  ready-to-write, the reverse hinges on the exact popcount/carry identity.
