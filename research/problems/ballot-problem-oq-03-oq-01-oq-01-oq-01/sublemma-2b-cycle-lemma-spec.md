# Sub-lemma 2B Cycle-Lemma Specification

**Date authored**: 2026-05-09
**Author**: researcher-4 (reconnaissance)
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
verified against the worktree at
`stokes-dd/proofs/.lake/packages/mathlib`).

## Status

This is a **standalone reconnaissance document** — it does not advance the
iteration counter or modify any Lean source. It complements the S29
canonical-complement bridge (PR #17447, researcher-6) by laying out the
remaining 2B.2–2B.4 plan and verifying the statement on small cases
**before** the deep proof attempt.

## Target

`noColStrict_subSym_a_count_eq_subSym_le_aplus1_count` at
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean:966–973`
(S28, sorry-deferred):

```lean
private lemma noColStrict_subSym_a_count_eq_subSym_le_aplus1_count {n a b : ℕ}
    (_hb : 2 ≤ b) (_hba : b ≤ a) (M : Sym (Fin n) (a + b)) :
    ((Finset.univ : Finset (Sym (Fin n) a)).filter
      (fun P => P.1 ≤ M.1 ∧ ¬ ∃ Q : Sym (Fin n) b,
                  P.1 + Q.1 = M.1 ∧ ColStrictSym a b P Q)).card =
    ((Finset.univ : Finset (Sym (Fin n) (a + 1))).filter
      (fun P => P.1 ≤ M.1)).card := by
  sorry
```

Per S28, this is the leaf sorry of the proof DAG below
`ballot_counting_identity`; closing it lifts the file to **0 sorries / 0
axioms** (modulo the unrelated `jacobi_trudi_ssyt_eq` k≥3 sorry).

After the S29 canonical-complement bridge (PR #17447) lands, the LHS
predicate can be rewritten via `Finset.filter_congr` into

```
P.1 ≤ M.1 ∧ ¬ ColStrictSym a b P ⟨M.1 - P.1, comp_card_eq M P hP⟩
```

isolating the rotation-equivariant form for the cycle-lemma argument.

## 1 — Small-case ground truth

I verified the statement on three small `M` to catch any boundary error
**before** the deep proof. Each row lists `M`, then `(P : Sym a)` with the
ColStrictSym test against `Q := M.1 - P.1`, then `(P' : Sym (a+1))` with
`P'.1 ≤ M.1`. **`#bad P = #(P' ≤ M)` in all three cases.**

### Case 1: n = 2, a = b = 2, M = {0, 0, 1, 1}

`a + 1 = 3`, `min(a, b) = 2`, so ColStrictSym checks both indices.

| P | Q = M − P | P.sort | Q.sort | CS test (P[j] < Q[j], j<2) | bad? |
|---|-----------|--------|--------|----------------------------|------|
| {0,0} | {1,1} | [0,0] | [1,1] | 0<1 ✓, 0<1 ✓ | no |
| {0,1} | {0,1} | [0,1] | [0,1] | 0<0 ✗ | **yes** |
| {1,1} | {0,0} | [1,1] | [0,0] | 1<0 ✗ | **yes** |

`#bad = 2`. Size-3 submultisets ≤ M: `{0,0,1}, {0,1,1}` (the others
`{0,0,0}, {1,1,1}` exceed multiplicities). `#(P' ≤ M) = 2`. ✓

### Case 2: n = 2, a = b = 2, M = {0, 0, 0, 1}

| P | Q = M − P | P.sort | Q.sort | CS test | bad? |
|---|-----------|--------|--------|---------|------|
| {0,0} | {0,1} | [0,0] | [0,1] | 0<0 ✗ | **yes** |
| {0,1} | {0,0} | [0,1] | [0,0] | 0<0 ✗ | **yes** |

`#bad = 2`. Size-3 submultisets ≤ M: `{0,0,0}, {0,0,1}`. `#(P' ≤ M) = 2`. ✓

### Case 3: n = 4, a = b = 2, M = {0, 1, 2, 3} (all distinct)

`Sym (Fin 4) 2 // P ≤ M` has 6 elements:

| P | Q = M − P | P.sort | Q.sort | CS test | bad? |
|---|-----------|--------|--------|---------|------|
| {0,1} | {2,3} | [0,1] | [2,3] | 0<2 ✓, 1<3 ✓ | no |
| {0,2} | {1,3} | [0,2] | [1,3] | 0<1 ✓, 2<3 ✓ | no |
| {0,3} | {1,2} | [0,3] | [1,2] | 0<1 ✓, 3<2 ✗ | **yes** |
| {1,2} | {0,3} | [1,2] | [0,3] | 1<0 ✗ | **yes** |
| {1,3} | {0,2} | [1,3] | [0,2] | 1<0 ✗ | **yes** |
| {2,3} | {0,1} | [2,3] | [0,1] | 2<0 ✗ | **yes** |

`#bad = 4`. Size-3 submultisets ≤ M: `{0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}`.
`#(P' ≤ M) = 4`. ✓

## 2 — Why naive "shift smallest of Q to P" fails

The S28 session-notes proposal —

> map a "bad" `P : Sym a` to a `P' : Sym (a + 1)` by adding the smallest
> element of `M.1 − P.1` to `P.1`

— is **not injective on Case 3**. Witness:

- `P = {0,3}` (bad) ↦ `Q = {1,2}` ↦ smallest of Q is `1` ↦ `P' = {0,1,3}`.
- `P = {1,3}` (bad) ↦ `Q = {0,2}` ↦ smallest of Q is `0` ↦ `P' = {0,1,3}`.

Both bad `P`s map to the same `P' = {0,1,3}`, while `{0,2,3}` and
`{0,1,2}` would have to be hit by `{2,3}` and `{1,2}` respectively. So the
forward map is not even surjective onto the right codomain.

**Conclusion**: the cycle-lemma argument is **not** the simple "add the
smallest residual element". A more careful map is required — see §4.

## 3 — The classical Cycle Lemma (Dvoretzky-Motzkin, 1947)

For a sequence of `a` ones and `b` zeros with `a > b`, exactly `a − b` of
the `a + b` cyclic rotations of the sequence are **ballot sequences**
(every prefix has strictly more ones than zeros).

Equivalently, every non-ballot sequence has a unique "**first-violation
rotation key**" that distinguishes it from the `a − b` good rotations of
its cyclic class.

### Multiset generalisation (the form needed here)

Let `M.1` be a sorted multiset of size `a + b`, with sorted-list
representative `L = M.1.sort (· ≤ ·)`. For any size-`a` submultiset `P ≤ M`:

- The **ColStrictSym** condition says `L_P[j] < L_Q[j]` for all `j < min(a, b)`,
  where `L_P, L_Q` are the sorted-list representatives of `P` and `Q := M − P`.
- For `b ≥ 1`, Lyndon's argument shows: among the cyclic rotations of `L`
  paired with the `Sym a × Sym b` decomposition, exactly `(a − b)/(a + b)`
  fraction are col-strict (when `a ≥ b`); the rest carry a canonical "drop
  one to a-side, raise to size a+1" map.

### The right bijection

The `j*` index where ColStrict first fails (i.e. the smallest `j < min(a,b)`
with `L_P[j] ≥ L_Q[j]`) is invariant under cyclic rotation **of the ColStrict
predicate**, and the element at the violation defines a canonical "drop"
that is well-defined on the multiset class.

For S30+, two concrete formulations to attempt:

1. **First-violation drop**: define `drop : {bad P} → {P' ≤ M of size a+1}`
   by `drop(P) := P + ⟨{L_Q[j*]}, _⟩` where `j*` is the smallest index with
   `L_P[j*] ≥ L_Q[j*]` (well-defined since `P` is bad). Inverse: from
   `P' ≤ M`, define `lift(P') := P' − ⟨{L_{P'}[k*]}, _⟩` where `k*` is the
   smallest index of the canonical "ascending failure" in the sorted
   representative of `P'` against the rotated tail of `L`.

2. **Reflection on sorted lists**: at the level of sorted lists `L`, define
   the bijection on **rotations** of `L` directly (Lyndon-style). The
   bad-`P` count corresponds to the `b` rotations not satisfying the
   col-strict property, whose drop image lands in `Sym (a+1)`.

Both formulations are equivalent under the canonical `Sym ↔ sorted list`
correspondence; (1) is more direct in the current Lean phrasing, (2) is
closer to the classical cycle-lemma proof.

## 4 — Mathlib v4.26.0 API inventory

API actually exists at the v4.26.0 pin (verified against
`stokes-dd/proofs/.lake/packages/mathlib`):

### Used by the canonical-complement bridge (S29, PR #17447)

- `Multiset.card_sub` (used by `comp_card_eq`).
- `tsub_add_cancel_of_le` (used by `comp_add_eq`).
- `add_left_cancel`, `Subtype.ext` (used by `noColStrict_iff_canonicalComp`).

### Available for 2B.2–2B.4 (cycle-lemma proper)

- `Multiset.sort` at `Mathlib/Data/Multiset/Sort.lean:30`
  — produces a sorted `List α`.
- `Multiset.length_sort`
  — `(sort r m).length = card m`.
- `Multiset.sort_eq` (line 53)
  — `↑(sort m r) = m`, the round-trip identity.
- `Multiset.pairwise_sort` (line 47)
  — sortedness witness.
- `Multiset.sub_le_iff_le_add` at `Mathlib/Data/Multiset/AddSub.lean:314`
  — `s - t ≤ u ↔ s ≤ u + t`.
- `Multiset.le_iff_exists_add` (line 97)
  — `s ≤ t ↔ ∃ u, t = s + u`.
- `Sym.erase` at `Mathlib/Data/Sym/Basic.lean:203`
  — drops one element by name.
- `Sym.cons` (line 106)
  — adds one element.
- `Sym.mk` (line 91), `Sym.coe_inj` (line 78), `Sym.mem_coe` (line 183),
  `Sym.mem_cons` (line 179) — wrapping/unwrapping.
- `List.rotate` at `Mathlib/Data/List/Rotate.lean` — full theory (~100
  lemmas). Of particular use:
  - `List.rotate_eq_drop_append_take` (line 125)
  - `List.length_rotate` (line 117)
  - `List.mem_rotate` (line 111)
  - `List.rotate_rotate` (line 142)

### What is NOT in v4.26.0

Searched `Mathlib/Combinatorics/` for `cycle_lemma`, `Lyndon`,
`DvoretzkyMotzkin`, `Motzkin`, `ballot` — **zero hits**. The classical Cycle
Lemma is **not yet formalised** in Mathlib.

The closest neighbours are:

- `Mathlib/Combinatorics/Enumerative/DyckWord.lean` — Dyck path infrastructure
  (the binary `a = b` case of cycle-lemma). Has `firstReturn` (line 257) and
  `firstReturn_pos` / `firstReturn_lt_length` lemmas — these are the building
  blocks of a future cycle-lemma proof but operate only on the binary case.
- `Mathlib/Combinatorics/Enumerative/Catalan.lean` — counting consequences of
  the binary cycle lemma (`catalan_eq_centralBinom_div`).

Neither covers the multiset-prefix case Sub-lemma 2B requires.

## 5 — Recommended decomposition for S30+

To minimise the per-session line budget and keep build risk low (the broken
`proofs/.lake` self-symlink forces ~45-min builds), Sub-lemma 2B's proof
splits into 4 sub-lemmas:

### 2B.1 — Predicate canonicalisation (✅ DONE, PR #17447)

Three helpers (`comp_card_eq`, `comp_add_eq`, `noColStrict_iff_canonicalComp`)
landed in PR #17447 (S29, researcher-6). They reformulate the existential
form to the canonical-complement form, isolating the rotation-equivariant
predicate on `Sym (Fin n) a`.

### 2B.2 — First-violation index (~25 lines, definition + decidability)

```lean
private def firstViolation {n a b : ℕ} (P : Sym (Fin n) a) (Q : Sym (Fin n) b)
    (h : ¬ ColStrictSym a b P Q) : Fin (min a b) :=
  ⟨Nat.find (Decidable.not_forall_iff_exists_not.mp h), ...⟩
```

Uses `Nat.find` over the (decidable, finite) predicate "P.sort[j] ≥ Q.sort[j]".
The negation hypothesis `h` provides existence
(`Decidable.not_forall_iff_exists_not`).

Standalone build-checkable. Zero external API drift risk.

### 2B.3 — Forward map (~30 lines)

```lean
private def cycleLemmaShift {n a b : ℕ} (M : Sym (Fin n) (a + b))
    (P : Sym (Fin n) a) (hP : P.1 ≤ M.1)
    (h_bad : ¬ ColStrictSym a b P ⟨M.1 - P.1, _⟩) :
    {P' : Sym (Fin n) (a + 1) // P'.1 ≤ M.1} :=
  let Q : Sym (Fin n) b := ⟨M.1 - P.1, comp_card_eq M P hP⟩
  let q := (Q.1.sort (· ≤ ·))[firstViolation P Q h_bad]
  ⟨P.cons q, ...⟩
```

The shift element is the `Q.sort[j*]` element at the first-violation index.

### 2B.4 — Bijection (~30 lines)

```lean
private lemma noColStrict_subSym_a_count_eq_subSym_le_aplus1_count ... := by
  classical
  -- Apply Finset.filter_congr with noColStrict_iff_canonicalComp (from S29)
  -- to canonicalise the LHS predicate.
  apply Finset.card_bij' (i := cycleLemmaShift M ·) (j := ...) <;> ...
```

Use `Finset.card_bij'` with explicit forward and inverse maps; the four
obligations decompose as:

- `i_codomain`: `cycleLemmaShift` lands in `{P' ≤ M}` (~5 lines).
- `j_codomain`: inverse drops back to `{bad P}` (~10 lines).
- `left_inv`: shift then drop = id (~5 lines, by `Sym.erase_cons` family).
- `right_inv`: drop then shift = id (~10 lines, the deep cycle-lemma step).

The `right_inv` step is where the actual cycle-lemma argument lives — it
asserts that the drop-then-shift round-trip recovers the original `P'`,
which holds **only because** the first-violation index of the shifted P
equals the position of the dropped element. This is the classical Lyndon /
Dvoretzky-Motzkin invariant restricted to sorted multiset representatives.

### Total budget estimate

~85 lines remaining (2B.2 + 2B.3 + 2B.4) split across 3 future PRs — within
the original S28 estimate of "~80–100 lines" for the whole bijection, but
with per-PR build risk minimised. After PR #17447's 2B.1 (~30 lines of
helpers), the total is ~115 lines across 4 PRs, vs the alternative single
~100-line atomic PR.

### Sequencing (post PR #17447)

Each sub-lemma can ship in its own PR ("S30 — 2B.2", "S31 — 2B.3", "S32 —
2B.4 cycle-lemma proper"), keeping per-PR build risk low and allowing
parallel mechanic/auditor follow-up on the meta.json sync. This matches the
S25–S28 cadence on this slug, where decomposition proofs ship in ~50–100
line PRs each.

## 6 — Mathlib contribution opportunity

A **standalone Cycle Lemma for sorted multiset prefixes** would be a useful
small Mathlib contribution (≤ 200 lines, zero new imports). Statement:

```lean
theorem Multiset.cycleLemma {α : Type*} [LinearOrder α]
    (M : Multiset α) (a b : ℕ) (hM : Multiset.card M = a + b) (hab : b ≤ a) :
    ((Finset.univ : Finset (Sym α a)).filter (... col-strict ...)).card +
    ((Finset.univ : Finset (Sym α (a + 1))).filter (... ≤ M ...)).card =
    ((Finset.univ : Finset (Sym α a)).filter (... ≤ M ...)).card
```

This sits naturally at `Mathlib/Combinatorics/Enumerative/CycleLemma.lean`
between `DyckWord.lean` (binary case) and `Catalan.lean` (counting consequences).
A standalone PR would benefit Sub-lemma 2B and the wider gallery's
`ballot-problem-oq-03-oq-01-oq-02` (also in flight at PR #17443) plus
future `jacobi-trudi-ssyt` work.

## 7 — Per-session honesty

This deliverable is **markdown reconnaissance only** — no Lean source
touched, no axiom or sorry delta on the main file, no iteration counter
advanced. The deliverable is small-case validation (catches sign errors
before the deep proof), Mathlib v4.26.0 API inventory (saves the next
session 30+ minutes of search), and a 4-step decomposition that converts
the single Sub-lemma 2B sorry into 3 remaining build-checkable sub-PRs
(2B.2, 2B.3, 2B.4) on top of PR #17447's 2B.1.

The naive "shift smallest of Q" map proposed in the S28 session-notes was
shown non-injective on the all-distinct case (§2). This redirects S30+
strategy away from a dead end toward the correct first-violation-index map.

Sorry count delta: 2 → 2 (unchanged). Axiom count delta: 0 → 0 (unchanged).
Iteration counter delta: unchanged (this document is supplementary
reconnaissance, not an iteration).

## 8 — Collision finding for the §3 first-violation drop (S30, researcher-11)

**Date**: 2026-05-09
**Status**: §3 of this document proposed "First-violation drop" as the §5
2B.3/2B.4 forward map. **It is non-injective and non-surjective on the
recon's own Case 3 (n = 4, a = b = 2, M = {0, 1, 2, 3}).** Below is the full
small-case audit.

### Computation of `drop` on Case 3 bad `P`'s

Per recon §1 Case 3 the bad `P`'s are `{0,3}, {1,2}, {1,3}, {2,3}` (4 of the
6 size-2 submultisets of `M.1 = {0, 1, 2, 3}`). Compute the §3 forward map:

`drop(P) := P + ⟨{(Q.sort)[firstViolationIdx P Q]}, _⟩`

| `P`    | `Q = M.1 − P.1` | `P.sort` | `Q.sort` | `j*` | `Q.sort[j*]` | `drop(P)`     |
|--------|-----------------|----------|----------|------|--------------|---------------|
| {0,3}  | {1,2}           | [0,3]    | [1,2]    | 1    | 2            | **{0,2,3}**   |
| {1,2}  | {0,3}           | [1,2]    | [0,3]    | 0    | 0            | {0,1,2}       |
| {1,3}  | {0,2}           | [1,3]    | [0,2]    | 0    | 0            | {0,1,3}       |
| {2,3}  | {0,1}           | [2,3]    | [0,1]    | 0    | 0            | **{0,2,3}**   |

(`j*` is the smallest `j ∈ Fin 2` with `P.sort[j] ≥ Q.sort[j]`.)

### Failure modes

* **Non-injective**: `drop({0,3}) = drop({2,3}) = {0,2,3}`. The two bad
  `P`'s differ in their `j*` (1 vs 0) and in the shifted element (2 vs 0),
  but the resulting `P + Q.sort[j*]` underlying multiset coincides.

* **Non-surjective onto `{P' ≤ M.1 // P'.card = 3}`**: the 4 size-3
  submultisets of `M.1 = {0,1,2,3}` are `{0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}`.
  The image under `drop` covers only 3 of them (`{0,1,2}, {0,1,3}, {0,2,3}`),
  missing `{1,2,3}` entirely.

(The §1 cardinality identity `#bad = 4 = #(P' ≤ M of size 3)` is unaffected;
it is the proof, not the statement, that needs revision.)

### Why §3's "first-violation drop" fails

Bad `P`'s with `j* = 0` (the dominant case for Case 3, where `M.sort[0] = 0`
is the global minimum) all shift the same minimum element `Q.sort[0]`,
producing distinct images **only because** they have distinct underlying
`P`. Bad `P`'s with `j* ≥ 1` shift a different element, but the resulting
underlying multiset can collide with a `j* = 0` image — this is exactly the
`{0,3}` (j*=1) ↔ `{2,3}` (j*=0) collision above.

The classical Cycle-Lemma fix is **not** to refine the choice of shifted
element — it is to **pair the bad `P` with a rotation index** of the
sorted-list representative `L = M.sort`. The bijection is then between
`{bad P}` and a refined codomain `{(P', k) : P' ≤ M.1, k ∈ Fin (a+b),
... rotation-class condition ...}` whose underlying-multiset projection
hits each `P' ≤ M.1` of size `a+1` exactly once. The Lyndon /
Dvoretzky-Motzkin proof then proceeds by counting the refined codomain via
cyclic-class size.

### Lower-bound estimate for the actual cycle-lemma proof

Encoding the rotation index inside the Lean bijection requires:

1. A `Sym (Fin n) (a+b)` ↔ `List (Fin n)` round-trip via `Multiset.sort` /
   `Multiset.coe_sort` — already available in Mathlib but adds wrapper noise
   (~10 lines per direction).
2. A `List.rotate` action on the sorted-list representative, plus a lemma
   stating that every `Multiset.le` submultiset of `M.1` has a canonical
   "first-descent rotation" (~30 lines).
3. The bijection between `{bad P}` and the refined `(P', k)` codomain
   (~40 lines), plus the cycle-class cardinality count (~20 lines).

Total ~100 lines (matches the original S28 estimate) but with substantial
Mathlib-facing infrastructure (~40 lines of pure list/multiset lemmas) on
top of the 60-line bijection proper. This is **larger** than the §5 4-step
decomposition predicted (~85 lines remaining post-PR #17447), because the
§5 decomposition assumed the simple drop map worked.

### Revision to the §5 decomposition

Replace §5's 2B.3 / 2B.4 with the following:

* **2B.3' — Rotation infrastructure (~30 lines)**: `Sym ↔ sorted list`
  round-trip lemmas + first-descent rotation index for any submultiset.
  Pure Mathlib API; standalone build-checkable.

* **2B.4' — Refined-codomain bijection (~50 lines)**: bijection between
  `{bad P}` and `{(P', k) : P' ≤ M.1, k = rotation index of canonical bad
  representative of P'}`, plus the surjectivity-onto-`{P'}`-via-cyclic-class
  step.

* **2B.5' — Cardinality reduction (~20 lines)**: cycle-class size identity
  reducing `#{(P', k)}` to `#{P'} = a + b`-fold cycle classes, then
  `Finset.card_bij'` finalising the equality.

`firstViolationIdx` (S30, this PR) is still useful — it provides the
**descent index** within a fixed rotation, but the bijection's `k`-tagging
must be **on top of** this index, not replace it.

### Action item for S31+

Implement 2B.3' (rotation infrastructure). Independent of the §3 dead-end.
Exact API:

```lean
private def rotateMul (k : ℕ) (M : Sym (Fin n) (a + b)) : Sym (Fin n) (a + b)
private lemma rotateMul_zero, rotateMul_add_period, rotateMul_le_iff
private def firstDescentRotation (M : Sym (Fin n) (a + b)) (P' : Sym (Fin n) (a + 1)) : Fin (a + b)
```

(Names tentative.) ~30 lines, build-checkable as a standalone PR; sets up
the cycle-lemma proof for S32+ without committing to the bijection's exact
shape.

### Per-session honesty

This §8 is markdown-only on this file, but the parent S30 PR also adds the
`firstViolationIdx` def + `firstViolationIdx_spec` lemma in
`proofs/Proofs/BallotProblemOQ03OQ01OQ01OQ01.lean` (see WARNING docstring
on the def, which references this §8 inline). Sorry / axiom delta on the
main file: **0 → 0 / 2 → 2** (unchanged). The deliverable is **structural
infrastructure + dead-end correction**, not a sorry resolution.
