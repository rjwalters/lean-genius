# Research State: roth-theorem-k3-oq-01-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-09T00:00:00Z (S5 ACT VERIFY-DISCOVERY this PR)
**Iteration**: 5

## Current Focus

**S5 ACT VERIFY-DISCOVERY (researcher-4, 2026-06-09)** — Attempted
to Docker-verify the S4 four-fix surgical repair on a remediated
host disk (105 GiB free vs S4's 158 Mi). The verification failed
on multiple grounds and S5 ships this as a discovery memo (doc-only
PR, no Lean file changes) so S6+ does not repeat the trip-up.

### Key finding — S4 diagnosis was incomplete

The four S4 fixes are individually correct but **collectively
insufficient** to restore the file to a fresh-Docker-build-green
state on Mathlib v4.26.0:

- **Fix #1** (`div_lt_iff` → `div_lt_iff₀`) — necessary and correct.
- **Fix #2** (remove math-false `max_iterations_bound`) — necessary
  and correct. The math finding (`max_iterations_bound` is False
  for `δ > 1`, counterexample `δ=2, k=0`) is real and valuable.
- **Fix #3** (`set_option maxHeartbeats 400000 in` before
  `rothNumber_three`) — **diagnosis wrong**. The actual fresh-build
  failure of `fin_cases ... simp_all` is **unclosed subgoals**, not
  a heartbeat panic. `simp_all` returns successfully with three
  residual subcases of ZMod 3 arithmetic that it no longer reduces
  (a `Decidable` discharger moved in v4.26.0). Bumping
  `maxHeartbeats` does nothing.
- **Fix #4** (`set S : Finset (Finset (ZMod N))` type annotation +
  `hS_def ▸` rewrite chain in `rothNumber_achieved`) — **necessary
  but insufficient**. The actual failure is
  `failed to synthesize DecidablePred APFree` at three sites inside
  `rothNumber_achieved` (and same failure in `rothNumber_pos` and
  `card_le_rothNumber`). The type annotation fixes the membership
  goal but not the underlying instance-synthesis failure.

See `sessions/2026-06-09-s5-act-verify.md` for the full
verification log (≥10 Docker build attempts, escalating tactic
replacements, cache clearing, classical-tactic experiment).

### Tentative diagnostic — `DecidablePred APFree`

The `noncomputable def rothNumber` uses
`Finset.univ.powerset.filter (fun A => APFree A)`, which requires
`DecidablePred APFree`. On the older Mathlib snapshot this was
implicitly synthesizable; on v4.26.0 the synthesis fails and the
classical fallback isn't applied automatically.

S5's experimental fix attempt was to add `classical` to each
affected theorem (`rothNumber_pos`, `card_le_rothNumber`,
`rothNumber_achieved`). This shifted the error but didn't
eliminate it — the `classical`-introduced local `Decidable`
instance differs from the global `Classical.dec` used by the
`noncomputable def`, so the `Finset.filter` expressions no longer
unify (`{A ∈ univ.powerset | APFree A}.sup card ≤ sorry.sup card`).

The correct fix likely requires one of:
- A file-scoped `noncomputable instance : DecidablePred (@APFree N)`;
- Explicit `Classical.decPred` annotations at every `Finset.filter`
  site;
- Relocating `rothNumber_three` (the `decide`-cascade trigger) to a
  separate file.

All three are deeper than the surgical-repair scope S4 envisaged.

## Diff this PR ships

```
proofs/Proofs/RothTheoremQuantitative.lean — UNCHANGED
research/problems/.../sessions/2026-06-02-s4-act-repair.md — IMPORTED from S4 (never merged)
research/problems/.../sessions/2026-06-09-s5-act-verify.md — NEW (this S5 report)
research/problems/.../state.md — UPDATED (this file)
src/data/research/problems/roth-theorem-k3-oq-01-incomplete-01.json — UPDATED
```

Zero Lean changes. Counts unchanged: 286 LOC, 9 theorems,
4 sorries, 0 axioms, 1 def.

## Status of S4 PR #22075

S4 PR #22075 (DRAFT) is **not promotable as-is**. The four edits
are necessary contributors but not sufficient. S5 leaves the PR
open for the team to decide whether to:
- Close as superseded (S6 starts fresh);
- Rebase + extend with the additional `DecidablePred APFree` /
  `simp_all`-residue fixes;
- Cherry-pick fixes #1, #2 only (they're independent and useful
  even without the full repair).

## Prior Focus (S4 ACT REPAIR DRAFT, 2026-06-02, PR #22075)

S4 (researcher-1, 2026-06-02) drafted four surgical fixes for the
issues S3 (2026-06-01) discovered. PR opened DRAFT because host
disk was at 99 % (158 Mi free) and the Docker build could not
run. S5's host has 105 GiB free, so verification finally
proceeded — and discovered that the S4 fix design was
incomplete. See `sessions/2026-06-02-s4-act-repair.md`.

## Prior Focus (S3 ACT REPAIR-DISCOVERY, 2026-06-01, PR #22001)

S3 began as a small-N enumeration ACT but pivoted to a
fresh-build audit when Docker surfaced 6 distinct compile
failures in the file *as it sits on `main`*. Identified four
root causes (which S4 attempted to address surgically; S5
proves at least two of the four diagnoses were incomplete).

## Prior Focus (S2 contribution merged 2026-05-31, PR #21520)

S2 shipped `rothNumber_div_tendsto_zero` to the file (lines
156–207 of that revision). Proof reduces to
`Szemeredi.Roth.roth_density_bound` via the corners-theorem
chain. CI passed via Lake's incremental cache; rebuilding the
file from a clean state on Mathlib v4.26.0 surfaced the issues
S3 → S4 → S5 are still working through.

## Prior Focus (S1 OBSERVE, 2026-04-03)

Initial problem understanding from problem.md. The Lean file
`RothTheoremQuantitative.lean` has 4 landmark sorries remaining
(Roth 1953, Behrend 1946, Bloom–Sisask 2020, Kelley–Meka 2023),
each requiring ≥ 1000 LOC of formalization.

## Active Approach

S6 ACT OBSERVE/REPAIR-DESIGN — design the actual repair given
S5's findings. Not a simple surgical edit; needs investigation
into `Finset.filter` over noncomputably-decidable predicates and
how to keep `DecidablePred APFree` synthesizable across the
file.

## Attempt Count
- Total attempts: 5 (S1 OBSERVE, S2 ACT qualitative, S3 ACT
  REPAIR-DISCOVERY, S4 ACT REPAIR DRAFT, S5 ACT
  VERIFY-DISCOVERY this PR)
- Current approach attempts: 1
- Approaches tried: 4 (OBSERVE, qualitative ACT,
  REPAIR-DISCOVERY, REPAIR DRAFT → VERIFY-DISCOVERY)

## Blockers

`RothTheoremQuantitative.lean` fails fresh Docker build on
Mathlib v4.26.0. Root causes (S5-revised diagnosis):

1. `div_lt_iff` API rename (drop-in fix, S4 had this right).
2. Math-false `max_iterations_bound` (S4 had this right;
   remove and document).
3. `rothNumber_three`: `simp_all` leaves three residual ZMod 3
   arithmetic subcases on v4.26.0. Needs tactic redesign,
   not heartbeat bump.
4. `DecidablePred APFree` synthesis failure across the
   noncomputable filter chain in `rothNumber`,
   `rothNumber_pos`, `card_le_rothNumber`,
   `rothNumber_achieved`. Needs instance-handling redesign,
   not just `set` type annotations.

## Next Action

**S6 ACT REPAIR-DESIGN** — investigate `Finset.filter` over
`DecidablePred` for noncomputable-by-default predicates. Three
candidate approaches sketched in
`sessions/2026-06-09-s5-act-verify.md` (file-scoped instance,
explicit Classical.decPred, separate-file isolation).

Once S6 lands a green-on-fresh-build file, the original S3
small-N enumeration plan can resume:

```lean
theorem apFree_zero_one_zmod_four : APFree ({0, 1} : Finset (ZMod 4)) := by ...
theorem two_le_rothNumber_four : 2 ≤ rothNumber 4 := ...
theorem rothNumber_four_le_three : rothNumber 4 ≤ 3 := ...
```

≤ 30 LOC total.

The four landmark sorries (`roth_quantitative_upper_bound`,
`behrend_lower_bound`, `bloom_sisask_bound`,
`kelley_meka_upper_bound`) remain multi-PR research efforts.
