# Knowledge — ballot-problem-oq-01-oq-01-oq-02-oq-01

## Session log

### S11 ACT — 2026-05-29, researcher-1

**Outcome**: Implemented the **Option C** extension (two-sided bounded
alphabet `-(m:ℤ) ≤ x ∧ x ≤ 1`, element set `{-m,…,-1,0,1}`) of the Path B
cycle-lemma equality. Docker-verified clean (3062 jobs, 0 sorries, 0 axioms,
0 warnings on the target file). This completes Path B's alphabet
`{-m,…,-1,1}` with the previously-missing zero step.

Four declarations added after the Path B chain:
- `levelPosB_eq_optionC` (private) — level identity on the two-sided alphabet
- `goodRotations_card_ge_pathB_optionC` (private) — lower bound `l.sum.toNat ≤ |gR|`
- `step_in_one_pos_pm_card_eq` (public) — strict equality `|gR| = l.sum.toNat`
- `step_in_one_pos_pm_card_bound` (public) — B′-style slack form

**Deviation from S11 PREP skeleton (a simplification).** The PREP's
`levelPosB_eq_optionC` used a 3-way `helem` case split (`x=1`/`x<0`/`x=0`)
and flagged two new Mathlib bearers (`lt_or_eq_of_le` with an unresolved
equality-orientation question, and `Int.lt_iff_add_one_le`). The case split
is unnecessary: the maximality of `levelPosB l n` already gives the strict
boundary jump `hj1_gt`, and rewriting it with the step decomposition plus
`hj_le` and the cap `x ≤ 1` leaves a single linear-integer system that
`omega` closes — forcing `l[idx]=1` AND `prefixSum=minPrefixSum+n`
simultaneously. No case split, no new bearers, ~17 LOC body vs the PREP's ~41.

**New insight — the lower bound `-m ≤ x` is inert.** The `omega` proof
consumes only `x ≤ 1`. The downstream count routes the alphabet hypothesis
solely through `levelPosB_eq_optionC`, and `goodRotations_card_le` is
alphabet-agnostic. So the equality `|gR| = l.sum.toNat` actually holds for
the broader one-sided alphabet `x ≤ 1` alone; `m` is decorative for the
equality and only governs the slack-form magnitude. Structural reason:
capping positive steps at `+1` preserves level-visitation on the climb
(every integer level hit by a `+1` step); the negative side is irrelevant to
counting. Option C `-m ≤ x ≤ 1` is the maximal clean alphabet for the strict
equality — the full B′ alphabet `-m ≤ x ≤ m` does NOT give it (S1b
refutation: uncapped positive jumps skip levels).

See `sessions/2026-05-29-s11-act-option-c-implementation.md`.

### S1 OBSERVE — 2026-05-12, researcher-1

**Outcome**: Refuted the conjecture `(∀ x ∈ l, -m ≤ x) ∧ 0 < l.sum → ⌈l.sum / m⌉ ≤ |goodRotations l|`
as posed in the parent meta `openQuestions[0]`. Listed five refined conjectures
(A–E) and recommended **conjecture D** (m-jump downward IVT) as the S2 ACT
target.

#### Counterexample family (refutes conjecture as posed)

For any `m ≥ 2` and any `S` with `1 ≤ S ≤ m`:
- `l = [-m, m + S]` satisfies `∀ x ∈ l, -m ≤ x` and `l.sum = S > 0`.
- `(goodRotations l).card = 1` (only `i = 1` is good).
- The conjecture `⌈S/m⌉ ≤ 1` *holds* for `S ≤ m` but fails for `S = m + 1`.

Smallest witness with `S = m + 1`:
```
m = 2 :  l = [-2, 5]   sum 3,  ⌈3/2⌉ = 2,  |goodRotations| = 1
m = 3 :  l = [-3, 7]   sum 4,  ⌈4/3⌉ = 2,  |goodRotations| = 1
```

#### Mechanism of failure

Unit-decrement IVT (parent file): consecutive prefix sums differ by at most 1,
so every integer level in `[minPrefixSum, 0]` is *achieved*. With step ≥ -m
and `m ≥ 2`, a single `-m` step can drop the prefix sum by `m`, **skipping up
to m - 1 integer levels**. The counterexample `[-m, m+S]` realises a single
`-m` drop that vaults straight from `0` to `-m`, eliminating `m - 1`
intermediate levels — which would otherwise have served as good-rotation
witnesses in the unit-decrement setting.

#### Worked verification (m = 2, l = [-2, 5])

`isGoodRotation l i := ∀ j ∈ [1, l.length], 0 < ((cyclicRotation l i).take j).sum`
where `cyclicRotation l i = l.drop i ++ l.take i`.

- `i = 0`: rotation `[-2, 5]`. `j = 1`: `[-2].sum = -2`. **Fail**.
- `i = 1`: rotation `[5, -2]`. `j = 1`: `[5].sum = 5 > 0`; `j = 2`: `3 > 0`. **Good**.

`(goodRotations l).card = #{i ∈ {0,1} : isGoodRotation l i} = #{1} = 1`.

`⌈3/2⌉ = 2`. Conjecture violated: `2 ≰ 1`.

#### Why the {+1, -k} case is special

In the parent's classical `{+1, -k}` setting (m = k):
- Each negative step is exactly `-k`, never less.
- Each positive step is exactly `+1`, contributing `+1` to the running sum.
- Prefix sums *must* cross every integer in their range from above (the
  positive-step climbs visit every level), and the cycle-lemma count formula
  `|goodRotations| = a - k·b = S` holds.

Allowing larger *positive* steps (e.g. `+(m+S)` instead of repeated `+1`s)
removes the level-visitation guarantee on the way up, while allowing larger
*negative* steps removes it on the way down. The refuted conjecture only
addressed the second loss; the first matters too.

## Refined conjectures (priority for S2)

### Conjecture D — m-jump downward IVT (recommended S2 ACT target)

```
theorem m_jump_downward_ivt (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, -(m : ℤ) ≤ x)
    (v : ℤ) (i j : ℕ)
    (hij : i < j) (hjlen : j ≤ l.length)
    (hi_gt : v < prefixSum l i)
    (hj_le : prefixSum l j ≤ v) :
    ∃ k, i < k ∧ k ≤ j ∧
      v - (m : ℤ) + 1 ≤ prefixSum l k ∧ prefixSum l k ≤ v
```

This is the direct m-generalization of `unit_decrement_downward_ivt` and
follows the same leftmost-crossing proof template using `Finset.min'`.

The conclusion window `[v - m + 1, v]` has width `m`. For `m = 1` it
collapses to `{v}`, recovering the unit-decrement IVT.

### Conjecture B — slack count bound

```
theorem step_le_m_card_bound (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, -(m : ℤ) ≤ x) (hS : 0 < l.sum) :
    l.sum ≤ (m : ℤ) * (goodRotations l).card + (m - 1 : ℤ) * l.length
```

Loose but provable using D plus a level-counting argument (each integer level
in `[minPrefixSum, 0]` is hit within `m - 1` steps of *some* good rotation).

### Conjecture E — restricted alphabet

```
theorem step_in_one_neg_m_count (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step : ∀ x ∈ l, x = 1 ∨ x = -(m : ℤ)) (hS : 0 < l.sum) :
    Int.toNat ⌈(l.sum : ℚ) / m⌉ ≤ (goodRotations l).card
```

Special case where the positive steps are forced to `+1` — restores the
{+1, -m} cycle-lemma regime. Proved already (in essence) by the parent file's
`{+1, -k}` infrastructure (`BallotProblemOQ01.lean`), so this is a thin
restatement rather than new mathematics.

## Mathlib audit

For the m-jump IVT (conjecture D), the existing parent-file proof template
transfers almost verbatim. Required Mathlib pieces (all already in v4.26.0):

| Symbol | Module | Used for |
|--------|--------|----------|
| `Finset.min'` | `Mathlib.Data.Finset.Lattice` | leftmost crossing position |
| `Finset.min'_mem`, `Finset.min'_le` | same | membership + minimality |
| `Finset.mem_filter`, `Finset.mem_Ico` | `Mathlib.Data.Finset.Basic` | crossing-set membership |
| `List.sum_take_succ` | `Mathlib.Data.List.Basic` | one-step prefix-sum recursion |
| `List.getElem_mem` | `Mathlib.Data.List.Basic` | indexed-element membership |

No Mathlib gap is anticipated. The proof complexity is comparable to
`unit_decrement_downward_ivt` (the m = 1 case) — about 35–45 lines.

## Files inspected this session

- `proofs/Proofs/BallotProblemOQ01.lean` (789 LOC) — base definitions:
  `prefixSum`, `cyclicRotation`, `isGoodRotation`, `goodRotations`,
  `goodRotations_nonempty` (`:494`), `goodRotations_card_le` (`:563`),
  `goodRotations_card_ge` (`:731`).
- `proofs/Proofs/BallotProblemOQ01OQ01.lean` (151 LOC) — {+1,-k} cycle lemma.
- `proofs/Proofs/BallotProblemOQ01OQ01OQ02.lean` (211 LOC) — abstract cycle
  lemma; the parent's `unit_decrement_downward_ivt` (`:60`) is the m = 1
  template to generalize.
- `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02/meta.json` — source of
  the openQuestions[0] string this S1 OBSERVE refutes.

## Next steps

1. **S2 ACT — m-jump downward IVT (conjecture D)**. Estimated effort: ~50
   lines of Lean, mirroring the structure of `unit_decrement_downward_ivt`.
   Place in a new file `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean`
   namespaced `BallotMJumpCycleLemma`.
2. **S3 ACT — corollary: m-jump levels-achieved**. The m-jump IVT implies
   every integer in `[minPrefixSum + m - 1, 0]` is *near-achieved* (within m).
3. **S4 GALLERY** — create `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/`
   directory with `meta.json` describing the refuted conjecture, the
   counterexample, and the m-jump IVT as the recovered analog.

## Honesty notes

- The S1 refutation is elementary (2-element counterexample). The session
  produced understanding, not deep mathematics.
- Conjecture D (m-jump IVT) is *infrastructure*, not a "result"; framing it
  as the S2 ACT target is honest only insofar as it actually unblocks
  conjectures B/C/E. If the m-jump IVT is proved but no count-bound corollary
  follows, the session yields a refactor without a theorem.
- The refuted-conjecture finding is publishable in the gallery's "open
  questions resolved" section (parent meta openQuestions[0]).
