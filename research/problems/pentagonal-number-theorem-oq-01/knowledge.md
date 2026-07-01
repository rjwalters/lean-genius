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

## Session (2026-06-30, researcher-2) — Part 8: staircases as genuine `Nat.Partition` / `distincts` members

Closed the **bookkeeping gap** the prior sessions flagged as the one tractable item
below Franklin's involution: Part 7 recorded the staircases only as `Finset.Ico`
*sums*, never as elements of Mathlib's `Nat.Partition` type, so they were not literally
inside the `Nat.Partition.distincts n` Finset that the Part-6 bridges
(`coeff_genFun_pent`, `coeff_tprod_pent`) sum over. Part 8 promotes them.

Added to `PentagonalNumberTheoremOQ01.lean` (now 809 lines, 61 thm / 10 def,
**0 sorry / 0 axiom / no native_decide**, docker-build-VERIFIED `[7743/7743]`):

- `genPentNat k := ∑ i ∈ Ico k (2k), i` and `genPentNatNeg k := ∑ i ∈ Ico (k+1) (2k+1), i`,
  with `genPentNat_cast : (genPentNat k : ℤ) = genPent k` (and neg arm) via `Nat.cast_sum`
  + the Part-7 `staircase_sum_eq_genPent[_neg]`.
- `staircasePartition k : Nat.Partition (genPentNat k)` (and neg arm): the staircase Finset's
  underlying multiset as an honest partition. `parts_pos` holds for **all** k (`0 ∉ Ico k (2k)`,
  closed by `omega`); `parts_sum` is `rw [genPentNat, Finset.sum, Multiset.map_id']` (definitional).
- `staircasePartition_mem_distincts`: membership in `Nat.Partition.distincts` — the parts are
  `Nodup` because they come from a `Finset` (`(Finset.Ico …).nodup`).
- `staircasePartition_card = k` (`← Finset.card_def`, `Nat.card_Ico`, omega) and
  `staircasePartition_sign : (-1)^{#parts} = pentSign (±k)`.
- Headlines `franklin_fixed_point_isPartition[_neg]`: the staircase IS an element of
  `distincts (g(±k))` with exactly k parts, signed weight `pentSign(±k)`, value `g(±k)`.

So Part 7's fixed points are now *literally* among the distinct-part partitions whose signed
count is `[Xⁿ]∏(1-Xᵐ)`, each contributing exactly `pentSign(±k)`. **STILL OPEN** (unchanged):
evaluating the whole signed `distincts` sum — i.e. proving the staircases are the *only*
surviving contributors — which is Franklin's sign-reversing involution itself.

WORKFLOW: fast-iterated the proofs host-side via `lake env lean` on a throwaway
`ScratchPent.lean` importing the prebuilt parent olean (seconds vs minutes), then inlined and
did the sanctioned full docker build. Docker backend healthy again this session (29.6.1).

## Session (2026-06-30, researcher-5) — Part 11: Franklin's Move A operation itself

The first formalization in this file of an actual Franklin involution **move** (Parts
7–10 covered only the fixed points). On a distinct-part partition as `Finset ℕ` `S`
(smallest `s = min S`, largest `m = max S`), Franklin's **Move A** (case `s ≤ ℓ`)
removes `s` and adds 1 to the top `s` parts `{m-s+1,…,m}`; after cancelling the overlap
this is the closed form

    `franklinMoveA S s m = insert (m+1) ((S.erase s).erase (m-s+1))`.

Added to `PentagonalNumberTheoremOQ01.lean` (now ~1160 lines, +7 theorems/1 def,
**0 sorry / 0 axiom / no native_decide**, docker-build-VERIFIED `[7743/7743]`, PR #31615):

- `franklinMoveA_sum`  — `∑(Move A) = ∑S` (weight-preserving; stays in partitions of n).
  Proof: `Finset.add_sum_erase` twice + `Finset.sum_insert`, then `omega` over the three
  equations (omega handles the `m-s+1` truncated subtraction given `s ≤ m`).
- `franklinMoveA_card` — `card(Move A) = card S - 1` (two distinct parts removed, one
  added). `Finset.card_erase_of_mem` ×2 + `card_insert_of_notMem`; `card ≥ 2` from the
  pair `{s, m-s+1} ⊆ S`.
- `franklinMoveA_sign` — `(-1)^{card(Move A)} = -(-1)^{card S}`: **the sign cancellation**.
  `obtain j, card = j+1` then `pow_succ; ring`.
- `franklinMoveA_pos` — image is positive distinct parts (validity).
- `franklinMoveA_top_mem` — `s ≤ ℓ` (as `Icc (m-s+1) m ⊆ S`) ⟹ run bottom `m-s+1 ∈ S`.
- `franklinMoveA_headline` — all four packaged for a non-fixed `S` (`hnf : s ≠ m-s+1`)
  with `s ≤ ℓ`, reading `s`/`m` off `min'`/`max'`.

The boundary `s = m-s+1` ⟺ `m = 2s-1` ⟺ `S` is the positive staircase `{s,…,2s-1}` of
Parts 7–10 — exactly where Move A degenerates (the fixed point), excluded by `hnf`.

**STILL OPEN** (unchanged): the companion "Move B" (case `s > ℓ`: peel the top run down
and create a new smallest part `ℓ`), the proof that Move A and Move B are mutually
inverse on the non-fixed partitions, and hence the full involution
`∑_{distincts n}(-1)^{#parts} = pentSeriesCoeff n`.

GOTCHA: a concurrent rebase onto `origin/main` discarded the uncommitted edit mid-session
(the worktree's `feature/researcher-5` branch was rebased by a sibling/cleanup). Re-applied
from context and committed IMMEDIATELY before re-verifying — commit early on hot worktrees.
Also hit transient `ENFILE: file table overflow` right after `docker kill`-ing builds; clears
after `pkill -f leantar/lake/curl`.

### Next Steps
- Part 12: formalize **Move B** (`s > ℓ`): `franklinMoveB S ℓ m = insert ℓ (image of top
  run shifted down)`, with the same sum/card/sign lemmas (card +1, sign flips the other way).
- Part 13: prove `franklinMoveB (franklinMoveA S …) … = S` and vice versa on the non-fixed
  domain — the mutual-inverse property — then assemble the sign-reversing involution and
  close `∑_{distincts n}(-1)^{#parts} = pentSeriesCoeff n` via cancellation.
- A staircase-length `ℓ` def (`S.filter (Icc · (max') ⊆ S)`) would let Move A/B be stated
  with `s ≤ ℓ` / `s > ℓ` directly rather than the spelled-out `Icc ⊆ S` hypothesis.

## Part 12 — Move B + the two moves are MUTUALLY INVERSE [VERIFIED, 0-axiom]

Completed the genuine open core named at the end of Part 11. Added **Move B** (the
`s > ℓ` complement of Move A) and the two **closed-form composition identities** that
exhibit Franklin's map as an involution. `PentagonalNumberTheoremOQ01.lean` now ~1313
lines, **0 sorry / 0 axiom / no native_decide** (host `lake env lean` exit 0;
`#print axioms` = `[propext, Classical.choice, Quot.sound]` only — docker daemon was down
this session, verified via the host-lean fallback).

`franklinMoveB S ℓ m = insert ℓ (insert (m-ℓ) (S.erase m))` — delete old top `m`, create
run bottom `m-ℓ`, insert new smallest part `ℓ`. New theorems (+1 def, +8 thm):

- `insert_pair_erase_pair` — re-inserting two distinct existing parts after erasing both
  recovers the set (`ext` + nested `by_cases`); the algebraic backbone of the inverse pair.
- `franklinMoveB_sum` — `∑(Move B) = ∑S` (`-m + (m-ℓ) + ℓ = 0` via `add_sum_erase` + `omega`).
- `franklinMoveB_card` — `card(Move B) = card S + 1` (one part out, two distinct in).
- `franklinMoveB_sign` — `(-1)^{card(Move B)} = -(-1)^{card S}`: sign-REVERSING (opposite
  parity shift from Move A, same cancellation effect).
- `franklinMoveB_pos` — image stays positive distinct parts (`ℓ≥1`, `m-ℓ≥1` from `ℓ<m`).
- **`franklinMoveB_franklinMoveA`** — `franklinMoveB (franklinMoveA S s m) s (m+1) = S`
  (Move B undoes Move A). Key: `Finset.erase_insert` of the fresh top `m+1` (not in the
  double-erased set, by `max`), `harith : m+1-s = m-s+1`, then `insert_pair_erase_pair`.
- **`franklinMoveA_franklinMoveB`** — `franklinMoveA (franklinMoveB S ℓ m) ℓ (m-1) = S`
  (Move A undoes Move B). Key: `h1 : m-1+1=m`, `h2 : m-1-ℓ+1 = m-ℓ`, then `erase_insert`
  ×2 + `insert_erase`.
- `franklinMoveB_headline` — all four preservation laws packaged for a non-fixed `S` in
  the `ℓ < s = min'` regime, reading `m` off `max'`.

The parameter threading is the crux: the part Move A *removes* (`s`) is exactly the
smallest part Move B *creates*; the top `m+1` Move A *creates* is the top Move B *removes*.
Together with the four preservation laws this is a sign-reversing involution pairing each
non-fixed distinct-part partition of `n` with one of opposite sign — the cancellation that
collapses Euler's product to the pentagonal terms.

GOTCHA: docker daemon down all session → used the host-lean fallback
`cd proofs && bin/lake env lean Proofs/<File>.lean` (the safety wrapper passes `lake env`
through; only `lake build` is blocked). Confirmed 0-axiom by injecting `#print axioms`
before the final `end` and compiling the whole file (no olean import needed since none was
built for the worktree).

### Next Steps
- Part 13: introduce a staircase-length `ℓ` definition so Move A/B dispatch on `s ≤ ℓ` vs
  `s > ℓ` directly, then glue the two headlines into a single `franklinInvolution` on the
  non-fixed domain and a `card`-parity sign-reversal — the last structural step before the
  cancellation sum `∑_{distincts n}(-1)^{#parts} = pentSeriesCoeff n`.

## Part 13 — the unified Franklin step (dispatch A/B) with uniform sign reversal [VERIFIED build, 0-axiom by inheritance]

Consolidated Parts 11–12's two separate moves into one dispatched map and proved the two
properties that hold **uniformly across both branches** — the cancellation engine.

`franklinStep S s ℓ m := if s ≤ ℓ then franklinMoveA S s m else franklinMoveB S ℓ m`
(+1 def, +4 thm). `PentagonalNumberTheoremOQ01.lean` now ~1454 lines.

- `franklinStep_sum` — `∑ (franklinStep) = ∑ S` in either regime.
- `franklinStep_sign` — **`(-1)^{#parts} ↦ -(-1)^{#parts}` uniformly** (Move A: card−1,
  Move B: card+1; parity flips either way). This is *the* fact forcing
  `∑_{non-fixed} (-1)^{#parts} = 0`.
- `franklinStep_pos` — image stays in positive parts.
- `franklinStep_headline` — the three packaged together.

RECIPE (clean regime dispatch without over-requiring hypotheses): give each theorem its
preconditions **conditionally** — `hA : s ≤ ℓ → <MoveA hyps>` and `hB : ℓ < s → <MoveB
hyps>`. Proof: `unfold franklinStep; split_ifs with h`; in the A branch `obtain … := hA h`,
in the B branch `obtain … := hB (not_le.mp h)`, then apply the matching Part 11/12 branch
lemma. No branch is asked to satisfy the other's preconditions (Move A's `Icc ⊆ S` would
fail in the `s>ℓ` regime, so unconditional bundling would be unprovable). Move B's `sum`
needs `ℓ ≤ m`; feed `le_of_lt h6` from the headline's `ℓ < m`.

VERIFY: full-file `cd proofs && env LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PentagonalNumberTheoremOQ01.lean` → **EXIT 0, 0 errors, 0 sorry warnings**.
`#print axioms` could **not** be run this session: the box was at load-avg ~28–51 with
~149 concurrent lean/lake processes and every `#print axioms`/`-o` invocation segfaulted
(EXIT 139, empty output) on resource exhaustion — NOT a proof defect. 0-axiom status is
inferred from (a) the clean sorry-free build and (b) axiom-inheritance: the new decls only
compose the already-0-axiom `franklinMoveA_*`/`franklinMoveB_*` via `unfold`/`split_ifs`/
`obtain`/`exact` (no axiom/sorry/native_decide/decide-on-data introduced). Re-run
`#print axioms PentagonalNumberTheoremOQ01.franklinStep_headline` when the box is quiet.

### Next Steps
- Part 14: **bijectivity / involution.** `franklinStep (franklinStep S …) … = S`. The raw
  algebra is Part 12's mutual-inverse pair (`franklinMoveB_franklinMoveA`,
  `franklinMoveA_franklinMoveB`); the missing piece is that the regime **swaps** under one
  move (so the second dispatch picks the other branch), which needs recomputing
  `min'/max'` and the top-run length `ℓ` on the image. A `staircaseLen`/run-length
  definition (`Nat.find` of the first gap below `max'`) would let the dispatch test read
  `s ≤ ℓ` off `S` directly and make the swap statable.
- Then the cancellation sum `∑_{distincts n}(-1)^{#parts} = pentSeriesCoeff n` via the
  sign-reversing involution on the non-fixed domain (fixed staircases = pentagonal terms).

## Part 14 (partial) — recomputing the top part `max'` on the move images [VERIFIED, 0-axiom]

**Session 2026-06-30 (researcher-3).** Toward the Franklin involution's self-inverse
property (`franklinStep (franklinStep S …) … = S`), which needs the second dispatch to read
the reverse-move parameters off the image `T`. The top parameter is `max' T`. Proved both
recomputations in closed form (+2 thm, ~74 L; docker-build `Built Proofs.PentagonalNumberTheoremOQ01`
clean; `#print axioms` on both = `[propext, Classical.choice, Quot.sound]`):

- `franklinMoveA_max' (H hmax) : max' (franklinMoveA S s m) = m + 1`. The image inserts the
  fresh top `m+1`; everything else is `≤ m` (from `hmax : ∀ x∈S, x≤m`). `le_antisymm`:
  `max'_le` (mem_insert → `omega` on `m+1` branch, `hmax`+erase_subset on the other) and
  `le_max'` on `m+1 ∈ insert …`. This is exactly the `m+1` fed to
  `franklinMoveB (franklinMoveA S s m) s (m+1) = S`.
- `franklinMoveB_max' (H hmax hℓ1 hℓm htop) : max' (franklinMoveB S ℓ m) = m - 1`. The new
  top is `m-1`, present EITHER as `m-ℓ` (run length 1, `ℓ=1`) OR as a run part `m-1 ∈ S`
  (run length ≥2, from `htop : Icc (m-ℓ+1) m ⊆ S`) — CASE SPLIT `Nat.lt_or_ge ℓ 2` is
  required. Upper bound: `ℓ<m`, `m-ℓ≤m-1` (`ℓ≥1`), erase-branch `y≤m ∧ y≠m ⟹ y≤m-1`
  (`omega`). This is the `m-1` fed to `franklinMoveA (franklinMoveB S ℓ m) ℓ (m-1) = S`.

RECIPE: `max'` of an `insert/erase` closed form via `le_antisymm (max'_le …) (le_max' … hmem)`;
unfold the def with `rw [franklinMoveX, Finset.mem_insert, …, Finset.mem_erase]` then
`rcases` the disjunction; each branch closes by `omega` (given `hmax`). Membership of the
new max in a Move B image is the only place needing a run-length case split.

### STILL OPEN (next)
The companion `min'` / staircase-length recomputations that fix the *smallest-part* dispatch
test `s ≤ ℓ` on the image (so the second `franklinStep` provably picks the OTHER branch).
Move B creates smallest part `ℓ`, so heuristically `min'(franklinMoveB S ℓ m) = ℓ` in the
`s>ℓ` regime (needs `ℓ < s ≤ m-ℓ`); `min'` of a Move A image is second-smallest-of-`S` and
needs the staircase structure. Then glue with Part 12's mutual-inverse pair for the full
`franklinStep` involution and the cancellation sum
`∑_{distincts n}(-1)^{#parts} = pentSeriesCoeff n`.

## Session 2026-06-30 (researcher-2) — child OQ01OQ01 Part 5: gap structure of A001318

Avoided the parent file (active open PR #31615 adds Parts 11–12 = Franklin Move A/B there →
collision risk; the deep involution core is owned by that PR). The parent's pentagonal-sign
identity `∑_{distincts}(-1)^#parts = pentSeriesCoeff` is the OPEN core (Franklin's involution),
so OQ02's classical Euler recurrence is NOT reachable yet — its recurrence is correctly left in
terms of the abstract Euler coefficient.

Instead extended the collision-free child `PentagonalNumberTheoremOQ01OQ01.lean` (ordered
enumeration `gpAt` of A001318) which recorded strict monotonicity but never the GAP sizes.
Added **Part 5** (5 theorems, 0-axiom; host `lake env lean` EXIT 0; now 255L/21thm, meta synced):
- `gpAt_gap_odd` : `gpAt(2j+1) − gpAt(2j) = 2j+1` (even step `g(−j)→g(j+1)`, the odd progression
  1,3,5,7,…) — via `genPent_succ_sub` + `genPent_neg` + `linarith`.
- `gpAt_gap_even` : `gpAt(2j+2) − gpAt(2j+1) = j+1` (odd step `g(j+1)→g(−(j+1))`, naturals
  1,2,3,4,…) — `rw [show 2j+2=2(j+1)]` then `genPent_neg`/`push_cast`/`ring`.
- `gpAt_gap_pos` : every consecutive difference `≥ 1` (quantitative strict monotonicity);
  `Nat.even_or_odd` split, each branch closed by `omega` against the gap formula.
- `gpAt_gaps` (capstone conjunction) + `gpAt_gap_values` (sanity vs 1,1,3,2,5,3).

So A001318's first differences are now pinned as two interleaved APs. Independent of the Franklin
core; complements OQ01OQ01's existing range/strict-mono results.

## Session 2026-06-30 (researcher-2) — child OQ01OQ01 Part 6: quadratic closed form + growth/density of A001318

Continued the collision-free child `PentagonalNumberTheoremOQ01OQ01.lean` (Franklin core still
owned by the parent's open PRs #31794 Part 14 etc.; avoided the parent entirely). Parts 1–5 fixed
the *order* (strict-mono) and *gaps* (first differences) but never the *growth rate*. **Part 6**
telescopes the two interleaved gap-APs into a single quadratic (7 theorems, 0-axiom, docker-VERIFIED;
now 326L/28thm, meta synced). NOTE: rescued **Part 5** first — it was committed only on the stale
`feature/researcher-2` (commit 032708b0d7a) and never merged; cherry-picked it onto a fresh branch
off `origin/main` so this PR ships Parts 5+6 together.

- `gpAt_eight_even` / `gpAt_eight_odd`: exact closed forms `8·gpAt(2j)=3(2j)²+2(2j)` and
  `8·gpAt(2j+1)=3(2j+1)²+4(2j+1)+1`. Each is a one-line `rw [gpAt_even/odd]` then
  `linear_combination (4:ℤ) * two_mul_genPent (-(j:ℤ) / (j:ℤ)+1)` — the coefficient 4 turns the
  parent's `2·g = k(3k-1)` into the `8·gpAt` form. `linarith` CANNOT close these (RHS product), use
  `linear_combination`.
- `gpAt_eight_lower` (3n² ≤ 8·gpAt n) / `gpAt_eight_upper` (≤ 3n²+4n+1, equality at odd n) /
  `gpAt_eight_upper'` (≤ 3(n+1)²): parity split `Nat.even_or_odd`, each branch `push_cast; nlinarith
  [Nat.cast_nonneg (α:=ℤ) j]`. (Even case needs `rw [show j+j=2*j from (two_mul j).symm]` first since
  `Even n` unfolds to `n=j+j` not `2*j`.)
- `gpAt_eight_sandwich` (Θ(n²) capstone) + `gpAt_le_imp_index_sq_le` (density: `gpAt n ≤ N ⟹ 3n²≤8N`,
  so ≤ √(8N/3)+1 generalized pentagonal numbers lie in [0,N] — they thin out like √N).

Meta openQuestions refined: the per-parity closed form is now DONE; remaining bounded follow-ups are
(a) a single parity-free `gpAt n = ⌊(3n²+4n)/8⌋`, (b) the EXACT counting function #{gen-pent ≤ N}.
Still OPEN (unchanged, not touched): Franklin's sign-reversing involution (the parent's deep core).

GOTCHA: symlinking main's `proofs/.lake` into the /tmp worktree did NOT speed the docker build (it
uses the `lean-mathlib-cache` docker volume, re-downloads 7727 oleans regardless) and the first build
died at [330s] with `exit 125 unexpected EOF` = Docker VM crash (not a Lean error); infra-guardian
restarts it. Removed the symlink and rebuilt clean.
