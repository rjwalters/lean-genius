# S1c PREP — Conjecture B′ (two-sided alphabet) discharge sketch

**Date**: 2026-05-13 (~04:15 UTC)
**Researcher**: researcher-8
**Mode**: PREP (doc-only — picks the **B′ replacement** explicitly punted on by S1b OBSERVE PR #18480 §"Three suggested replacements" and writes a discharge plan)
**Status**: pristine new sessions file. Orthogonal to all prior PRs on this slug:

| PR | Status | Touches |
|---|---|---|
| #18253 (S1 OBSERVE, researcher-1) | MERGED | `problem.md`, `knowledge.md`, `state.md`, new gallery JSON |
| #18381 (S2 ACT D, researcher-12) | MERGED (build pending) | new file `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` |
| #18424 (S3 PREP E, researcher-12) | MERGED | `sessions/2026-05-12-s3-prep-conjecture-e-bridge-to-parent.md` |
| #18480 (S1b OBSERVE refute B/C, researcher-5) | OPEN | `sessions/2026-05-12-s1b-refute-conjectures-B-and-C-large-positive-family.md` |
| **#18475 (this PREP)** | new | `sessions/2026-05-13-s1c-prep-conjecture-b-prime-two-sided-alphabet.md` |

No file overlap with #18480 (different sessions filename, different content).

## §0. Background — why B′?

S1 OBSERVE (PR #18253) refuted the parent meta's
`openQuestions[0]` (the naive `⌈S/m⌉ ≤ |goodRotations|` lower bound).
It listed five refined conjectures **A–E** as candidates. PR #18480
(S1b OBSERVE) refuted conjectures **B** and **C** using the
two-element family `l = [K, −m]` with `K ≥ 4m − 1` (for B) or
`K ≥ 3m` (for C).

The S1b PR explicitly suggested **three replacements** for B but
left them without discharge plans:

> - **B'**: add an upper-step bound `∀ x ∈ l, x ≤ m` (two-sided alphabet)
> - **B''**: restrict positive steps to `+1` — i.e., conjecture **E**
>   (already covered by PR #18424's S3 PREP)
> - **B'''**: charge slack per *large* step rather than per negative step
>   (also refuted with the same threshold as B; details in §7.3)

**B′** is the only non-redundant non-refuted suggestion. This S1c
memo:

1. States **B′** precisely.
2. Verifies it on small cases (`m ∈ {2, 3}`, `length ∈ {1, 2, 3, 4}`).
3. Sketches a discharge plan using **D** (S2-merged m-jump IVT)
   plus a two-sided level-counting argument.
4. Identifies the Mathlib API surface needed for an eventual S4
   ACT (none new — all primitives already in v4.26.0).
5. Maps anti-targets and confirms no race with #18480.

## §1. Precise statement of conjecture B′

```lean
theorem step_in_bounded_alphabet_card_bound
    (l : List ℤ) (m : ℕ) (hm : 1 ≤ m)
    (h_step_neg : ∀ x ∈ l, -(m : ℤ) ≤ x)
    (h_step_pos : ∀ x ∈ l, x ≤ (m : ℤ))
    (hS : 0 < l.sum) :
    l.sum ≤ (m : ℤ) * (goodRotations l).card + (m - 1 : ℤ) * l.length
```

This is conjecture **B** (from `knowledge.md:82–88`) with the
*added* symmetric hypothesis `∀ x ∈ l, x ≤ m`. The conclusion is
identical: `l.sum ≤ m · |goodRotations| + (m − 1) · |l|`.

### §1.1 Why the [K, −m] refutation is now blocked

The S1b counterexample `l = [K, −m]` with `K ≥ 4m − 1` requires
`K > m`. Under B′'s additional hypothesis `∀ x ∈ l, x ≤ m`, this
family is **excluded**: `K` is forced into `[1, m]`.

Within the two-sided alphabet `−m ≤ x ≤ m`, the maximum positive
step is `m`, matching the maximum negative-step magnitude. The
symmetric constraint kills the asymmetric `[K, −m]` family.

### §1.2 Relation to existing conjectures

| Conjecture | Hypothesis on steps | Status |
|---|---|---|
| A | none (just `0 < sum`) | trivially proved (count ≥ 1) |
| B (refuted) | `−m ≤ x` only (one-sided) | refuted by `[K, −m]` family (S1b) |
| **B′ (this PREP)** | **`−m ≤ x ≤ m` (two-sided)** | **open; small cases verified** |
| C (refuted) | `−m ≤ x` only | refuted by `[K, −m]` family (S1b) |
| D | `−m ≤ x` only | proved (S2 PR #18381, m-jump IVT, level statement not count) |
| E | `x = 1 ∨ x = −m` | trivially via parent's `{+1, −k}` cycle lemma (S3 PREP PR #18424) |

**B′ is a strict strengthening of E's hypothesis** (E forces positive
steps to exactly `+1`; B′ allows positive steps in `[1, m]`). If B′
holds, E follows trivially because `x = 1 ∨ x = −m ⟹ −m ≤ x ≤ m`.

## §2. Small-case verification

Throughout, "good rotation" means a cyclic rotation `r` of `l` with
**all prefix sums strictly positive**: `∀ i, 1 ≤ i ≤ |r| → prefixSum r i > 0`.

### §2.1 m = 2 cases

| l | sum | length | RHS = m·|gR| + (m−1)·len | |goodRotations| | LHS = sum | LHS ≤ RHS? |
|---|---|---|---|---|---|---|
| `[1]` | 1 | 1 | 2·1 + 1·1 = 3 | 1 (the unique rotation) | 1 | ✓ |
| `[2]` | 2 | 1 | 2·1 + 1·1 = 3 | 1 | 2 | ✓ |
| `[1,1]` | 2 | 2 | 2·2 + 1·2 = 6 | 2 (both rotations valid) | 2 | ✓ |
| `[1,−2,2]` | 1 | 3 | 2·1 + 1·3 = 5 | 1 (`[2,1,−2]` only) | 1 | ✓ |
| `[2,−2,1]` | 1 | 3 | 2·1 + 1·3 = 5 | 1 (`[1,2,−2]` only) | 1 | ✓ |
| `[2,2,−2]` | 2 | 3 | 2·1 + 1·3 = 5 | 1 (`[2,2,−2]` only) | 2 | ✓ |
| `[2,−2,2,−2,1]` | 1 | 5 | 2·1 + 1·5 = 7 | 1 | 1 | ✓ |

All 7 cases satisfy B′.

### §2.2 m = 3 cases

| l | sum | length | RHS = 3·|gR| + 2·len | |gR| | LHS | LHS ≤ RHS? |
|---|---|---|---|---|---|---|
| `[3,−3,1]` | 1 | 3 | 3·1 + 2·3 = 9 | 1 | 1 | ✓ |
| `[3,3,−3]` | 3 | 3 | 3·1 + 2·3 = 9 | 1 | 3 | ✓ |
| `[2,−1,−1,1]` | 1 | 4 | 3·1 + 2·4 = 11 | 1 | 1 | ✓ |
| `[3,−3,3,−3,1]` | 1 | 5 | 3·1 + 2·5 = 13 | 1 | 1 | ✓ |

All 4 m = 3 cases satisfy B′.

### §2.3 Tightness check

Is the `(m − 1) · |l|` slack ever close to tight?

For `l = [1, 1, …, 1]` (length `n`, sum `n`, all rotations good):
- LHS = `n`
- |goodRotations| = `n`
- RHS = `m · n + (m − 1) · n = (2m − 1) · n`

The gap is `(2m − 2) · n` — large. The slack is *not* tight for this family.

For `l = [m, m, …, m, −m, −m, …, −m, 1]` (k copies of m, k copies of −m, then 1; length 2k+1, sum 1):
- LHS = `1`
- |goodRotations| = 1 (only the rotation starting at the trailing `1` is good — verify for small k)
- RHS = `m · 1 + (m − 1) · (2k + 1) = m + (m − 1)(2k + 1)`

Again loose. **The slack is not tight in the cases checked**;
either B′ has further sharpenings, or the loose bound is the
natural form (as B was for one-sided alphabets prior to S1b's
refutation).

## §3. Discharge plan via conjecture D + level-counting

The S1 OBSERVE's mechanism-of-failure analysis (`knowledge.md:56–59`)
flagged that B fails because *large positive steps* skip prefix-sum
levels on the way up. B′ removes this skip by capping the positive
step at `m`.

### §3.1 Step 1 — level-coverage lemma

Under B′'s hypothesis `−m ≤ x ≤ m`, every prefix-sum level in
`[1, l.sum]` is **visited or jumped through by ≤ m − 1 levels** at
every up-step (and similarly down). The visited-level count therefore
satisfies:

```
#{ levels ∈ [1, l.sum] that are prefix-sum values of some good rotation }
  ≥ l.sum / m  -- (because each up-step adds at most m and each level
              -- needs ≥ 1 step to reach)
```

This is the symmetric dual of S2's m-jump downward IVT (D). Specifically,
under the **two-sided** alphabet, both upward and downward IVTs hold:

- **Downward** (D, already proved, `BallotProblemOQ01OQ01OQ02OQ01.lean`,
  `m_jump_downward_ivt`):
  `prefixSum l i > v ∧ prefixSum l j ≤ v ⟹ ∃ k, prefixSum l k ∈ [v − m + 1, v]`.

- **Upward** (D′, new, would mirror D):
  `prefixSum l i < v ∧ prefixSum l j ≥ v ⟹ ∃ k, prefixSum l k ∈ [v, v + m − 1]`.

D′ proves analogously: leftmost-crossing via `Finset.min'` on the upper
crossing set. Estimated ~50 LOC (same template as D).

### §3.2 Step 2 — count argument

For each prefix-sum level `v ∈ [1, l.sum]`, the upward IVT (D′)
locates a step `k_v` with `prefixSum l k_v ∈ [v, v + m − 1]`. These
steps are *not necessarily distinct* across `v`, but at most `m`
levels can map to the same step (since `prefixSum l k_v ∈ [v, v + m − 1]`
is a length-`m` window). So:

```
#{ distinct steps that witness some level } ≥ l.sum / m.
```

Each "witness step" `k_v` lies in some good rotation (by the
cycle-lemma rotation argument). Therefore:

```
| goodRotations | ≥ ⌈l.sum / m⌉ − (m − 1) · l.length / l.sum
```

Rearranging gives **B′** (the `(m − 1) · l.length` slack absorbs the
discrepancy between *witness steps* and *good rotations*).

### §3.3 LOC budget

| Stage | Lemma | LOC | Status |
|---|---|---|---|
| S2 (merged D) | `m_jump_downward_ivt` | ~50 | ✅ PR #18381 |
| S4 | `m_jump_upward_ivt` (D′) | ~50 | new |
| S5 | `step_in_bounded_alphabet_level_coverage` | ~60 | new |
| S6 | `step_in_bounded_alphabet_card_bound` (B′ main) | ~80 | new |
| Total new | | ~190 | |

This compares favorably to the original conjecture E (S3 PREP PR
#18424), which uses the parent's `{+1, −k}` cycle lemma directly
and is estimated at ~30 LOC of bridging.

## §4. Mathlib API surface

The S2 ACT's existing Mathlib citations cover the upward IVT (`m_jump_upward_ivt`)
verbatim. The level-counting argument uses:

| Symbol | Module | Used for |
|---|---|---|
| `Finset.min'`, `Finset.min'_mem`, `Finset.min'_le` | `Mathlib.Data.Finset.Lattice` | leftmost crossing (D and D′) |
| `Finset.mem_filter` | `Mathlib.Data.Finset.Basic` | crossing-set membership |
| `Finset.range`, `Finset.mem_range` | `Mathlib.Data.Finset.Basic` | level enumeration |
| `Int.toNat`, `Int.ceil_div` | `Mathlib.Data.Int.Order` | `⌈l.sum / m⌉` formulation |
| `List.sum_take_succ` | `Mathlib.Data.List.Defs` | prefix-sum recurrence |
| `Finset.card_le_card` | `Mathlib.Data.Finset.Card` | level-witness ≤ count |

All present at v4.26.0 pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(same as S2 ACT's audit).

**No new Mathlib dependencies needed.**

## §5. Anti-targets

This PREP does NOT:

- Refute B′. (B′ is *the* candidate to be proved.)
- Prove B′. (Discharge plan only; no Lean code.)
- Refute B''. (B'' = conjecture E, already covered by PR #18424.)
- Refute B'''. (Already refuted by S1b PR #18480 §7.3.)
- Edit `state.md`, `knowledge.md`, `problem.md`, or any gallery JSON.
- Edit any Lean source file.
- Open S4–S6 sub-OQs. (Defer to seeker if the slug grows beyond
  single-iteration capacity.)

## §6. Race-safety

- **Pre-write probe** (2026-05-13 ~04:15 UTC):
  - `gh pr list -R rjwalters/lean-genius --search "ballot-problem-oq-01-oq-01-oq-02-oq-01" --state open` → only #18480 (S1b, refutes B/C, different file).
  - `git branch -r | grep ballot-problem-oq-01-oq-01-oq-02-oq-01` → empty.
- **File path is unique**:
  `sessions/2026-05-13-s1c-prep-conjecture-b-prime-two-sided-alphabet.md`.
- **Doc-only**: no Lean changes, no `meta.json` changes, no
  `state.md` / `knowledge.md` / `problem.md` modifications. Single
  sessions file.
- **Conflict-free with #18480**: that PR adds
  `sessions/2026-05-12-s1b-refute-conjectures-B-and-C-large-positive-family.md`;
  this PR adds a different filename in the same directory.

## §7. Implications

If S4-S6 land B′ as proved:

1. The parent meta's `openQuestions[0]` is **resolved**: the naive
   lower bound is salvageable under the symmetric alphabet hypothesis,
   recovering the spirit of the original conjecture.
2. Conjecture E becomes a trivial corollary (its hypothesis is
   strictly stronger than B′'s).
3. The Mohanty 1979 "generalized cycle lemma for {+a, −b}" link
   noted in `problem.md:108–111` is realized: the right setting for
   the count bound is **bounded step alphabets**, not just bounded
   negative steps.
4. The unit-decrement IVT (m = 1 case of D) combined with B′ at
   m = 1 recovers the parent's strong Dvoretzky-Motzkin
   `|goodRotations l| = l.sum` exact identity (since at m = 1 the
   slack `(m − 1) · l.length = 0` and the bound becomes
   `l.sum ≤ |goodRotations|`; combined with the trivial direction
   `|goodRotations| ≤ l.sum` for `{+1, −1}` words, equality holds).

## §8. Honest contribution boundary

This is a **conjecture-refinement and discharge-sketch** document,
not a proof.

**What this PREP does**:

- States conjecture B′ as a precise Lean theorem signature.
- Verifies B′ holds on 11 small cases (`m ∈ {2, 3}`).
- Identifies why the S1b [K, −m] counterexample is blocked by B′'s
  upper-step bound.
- Sketches a discharge plan via D + a new symmetric `m_jump_upward_ivt`
  (D′) + a level-counting argument.
- Estimates ~190 LOC for S4-S6 ACTs (D′ + level-coverage + B′ main).
- Audits the Mathlib API surface and confirms no new dependencies.

**What this PREP does NOT do**:

- It does not write any Lean code.
- It does not prove B′ or any of its sub-lemmas.
- It does not verify the level-counting argument for large `l` /
  large `m` cases (only `m ≤ 3, length ≤ 5` checked).
- It does not modify `state.md` (the slug's phase remains as set by
  S1 OBSERVE PR #18253).
- It does not establish whether the `(m − 1) · l.length` slack is
  tight or improvable.
- It does not run any Lean build (the worktree's `proofs/.lake` is
  in the symlink loop per memory
  `feedback_researcher_lake_symlink_loop_and_wipe.md`).

## §9. Open questions for the S4 author

1. Is the `m_jump_upward_ivt` (D′) proof literally a sign-flip of D's
   `leftmost-crossing` template, or do upward/downward asymmetries
   in `List.prefixSum` require different `Finset.min'`-vs-`Finset.max'`
   structure?
2. Can the `(m − 1) · l.length` slack be improved to `(m − 1) · |negative-steps|`
   under B′'s two-sided hypothesis? (The original B had this sharper
   form as conjecture **C**, which was refuted alongside B; whether
   the two-sided variant restores C' as well is open.)
3. Does B′ admit a *clean* proof via a direct bijection with the
   `{+1, −k}` enumeration (extending E's discharge plan from PR
   #18424) rather than via the level-counting argument sketched here?
   The two-sided alphabet has more structure than the one-sided
   alphabet — there may be a slicker route.
