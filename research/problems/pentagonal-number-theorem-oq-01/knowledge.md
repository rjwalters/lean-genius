# Knowledge Base: pentagonal-number-theorem-oq-01

## Problem Understanding

Gallery entry `pentagonal-number-theorem-oq-01` is **verified/original**, 0-axiom,
39 theorems (`proofs/Proofs/PentagonalNumberTheoremOQ01.lean`, imports Mathlib
only). It characterizes the generalized pentagonal numbers `g(k)=k(3k−1)/2` by the
square-discriminant test (`isGenPent_iff_isSquare`: `m` is generalized pentagonal
iff `24m+1` is a perfect square; explicit root `24·g(k)+1=(6k−1)²`), and machine-
checks both ends of Euler's identity through Mathlib's `Partition.genFun`.

It carries **three open questions**:
1. **Open core** — Franklin's sign-reversing involution
   `∑_{p∈distincts n}(−1)^{#parts} = pentSeriesCoeff(n)`. The genuinely hard
   combinatorial gap; still **OPEN**.
2. Derive Euler's partition recurrence for `p(n)` as a corollary.
3. Extend the square-discriminant viewpoint to higher figurate families.

## Progress

### 2026-06-23 (researcher-1) — answered OQ-03 with a new child entry

Created **`pentagonal-number-theorem-oq-01-oq-03`** (new verified/original entry,
`Proofs/PentagonalNumberTheoremOQ01OQ03.lean`, 18 theorems / 2 defs / 0 sorries /
0 axioms / no native_decide, host-lean verified against Mathlib 4.26.0):

- generalized **heptagonal** numbers `h(k)=k(5k−3)/2` with recognition criterion
  `isGenHept_iff_isSquare` (`m` heptagonal iff `40m+9` is a perfect square;
  converse via `ZMod 10`, mirroring the pentagonal `ZMod 6` argument), explicit
  roots `40·h(k)+9=(10k−3)²`, and the `±k` structural facts;
- the **general s-gonal discriminant identity** `disc_genPolygonal`:
  `8(s−2)·P+(s−4)² = ((2s−4)k−(s−4))²` (pentagonal s=5 and heptagonal s=7 as
  instances) — the unifying square-completion behind all figurate tests.

The **open core (OQ-01, Franklin involution) remains OPEN** — not touched.
Releasing the parent research claim; OQ-03 is shipped as the child entry.

### 2026-06-28 (researcher-2) — formalized Franklin's FIXED POINTS (Part 7)

Added **Part 7** to the parent file (`PentagonalNumberTheoremOQ01.lean`, now 705
lines / +7 theorems, all **0-axiom, 0-sorry**, host-`lean env`-verified vs Mathlib
4.26): the fixed-point side of the open core.

- `staircase_ico_eq_range` / `_neg`: reindex `Ico k (2k)` (and `Ico (k+1) (2k+1)`)
  as `range k` via `Finset.sum_Ico_eq_sum_range`.
- `staircase_sum_eq_genPent` / `_neg`: the consecutive integers `k,…,2k-1` sum to
  `g(k)` and `k+1,…,2k` sum to `g(-k)`. Proof: division-free Gauss sum
  (`gauss_int`, doubled form by induction + `linear_combination`) + the parent's
  `two_mul_genPent`, then cancel the factor 2 with `mul_left_cancel₀`.
- `franklin_fixed_point` / `_neg`: for `k≥1`, each staircase is exactly `k`
  **distinct positive parts** (`Nat.card_Ico`, `Finset.mem_Ico` + `omega`) summing
  to a generalized pentagonal number, with part-count parity
  `(-1)^k = pentSign (±k)` (`pentSign`, `Int.natAbs_natCast`, `Int.natAbs_neg`).

These are precisely the fixed points of Franklin's involution — the residual (RHS)
terms its cancellation leaves behind. **What remains genuinely OPEN** is only the
involution on the *non-fixed* distinct-part partitions (the cancellation of all
non-pentagonal terms); the full sign-reversing map is still absent from Mathlib and
is the deep multi-file development.

GOTCHA: `Int.natAbs_ofNat` is gone in 4.26 — use `Int.natAbs_natCast`. The assigned
`feature/researcher-2` worktree predates main; worked on a fresh branch off
`origin/main` (`research/pentagonal-staircase`) with `proofs/.lake` symlinked.
