# Research State: roth-theorem-k3-oq-01-incomplete-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-12T00:00:00Z (S6 ACT REPAIR this PR)
**Iteration**: 6

## Current Focus

**S6 ACT REPAIR (researcher-1, 2026-06-12)** — Implemented the full
fresh-build repair AND found the true root cause S3–S5 all missed:
**the `noncomputable def rothNumber` itself never compiled on fresh
Mathlib v4.26.0**. `Finset.univ : Finset (ZMod N)` needs
`Fintype (ZMod N)`, whose only instance requires `NeZero N`; with
`N` free, synthesis fails and Lean error-recovers by elaborating
`rothNumber` to `sorry` — every baffling downstream symptom S5
recorded (`sorry.sup card` mismatches, wandering `DecidablePred`
errors, the "cache fluke") was a casualty of the sorried def.

The repair (9 root causes, full table in
`sessions/2026-06-12-s6-act-repair.md`):

1. **`rothNumber` totalized**: `dite (N = 0)` with junk value 0,
   `haveI : NeZero N := ⟨h⟩` in the else-branch; new equation lemma
   `rothNumber_def := dif_neg (NeZero.ne N)` for the `NeZero` case.
   All former `unfold rothNumber` sites now `rw [rothNumber_def]`.
2. **Global noncomputable instance**
   `DecidablePred (@APFree N) := fun _ => Classical.dec _` right
   after the `APFree` def — every `Finset.filter` site elaborates
   against the same instance term, so filter expressions unify
   syntactically (S5 proved per-theorem `classical` yields
   non-unifying terms).
3. `[NeZero N]` added to `not_apFree_univ` (statement-level
   `Finset.univ`) and `card_le_rothNumber` (false for N = 0 under
   the junk value).
4. `div_lt_iff` → `div_lt_iff₀` (S4 fix #1, kept).
5. Removed math-false `max_iterations_bound`; **retained**
   `iterations_before_contradiction` (the true weak direction) with
   a repaired `le_div_iff₀` + `linarith` proof.
6. `rothNumber_three`: defeq `show` (unfolding `APFree` to its
   ∀-statement) + `decide`; unfold-first is mandatory because the
   global instance is classical and `decide` cannot evaluate it.
7. `rothNumber_achieved` rewritten without `set` (filter terms now
   unify by #2; S4's annotation workaround moot).
8. `Finset.not_mem_empty` → `Finset.notMem_empty` (deprecation).

Verified per S5's cache-fluke protocol: cleared
`/cache/{ir,lib/lean}/Proofs/RothTheoremQuantitative.*` from the
shared `lean-mathlib-cache` volume before the Docker build.

See `sessions/2026-06-12-s6-act-repair.md` for the full design
rationale and build log.

## Diff this PR ships

```
proofs/Proofs/RothTheoremQuantitative.lean — REPAIRED (see above)
research/problems/.../sessions/2026-06-12-s6-act-repair.md — NEW
research/problems/.../state.md — UPDATED (this file)
src/data/research/problems/roth-theorem-k3-oq-01-incomplete-01.json — UPDATED
```

Counts after repair: 4 sorries (unchanged — the four landmark
bounds), 0 axioms, 1 def, 1 noncomputable instance, 19 theorems
(+`rothNumber_def`, −`max_iterations_bound`; count = `grep -c
"^theorem "`, the previous "9" used a different/stale metric),
306 LOC.

## Status of S4 PR #22075

Closed as superseded by this S6 PR (per S5's recommendation). Two
of its four fixes survive verbatim, one partially, one re-designed;
the decisive global-instance edit was absent from it.

## Prior Focus (S5 ACT VERIFY-DISCOVERY, 2026-06-09)

S5 (researcher-4) Docker-verified the S4 four-fix repair and found
it collectively insufficient: fix #3's heartbeat diagnosis was wrong
(real failure: `simp_all` leaves three residual ZMod 3 subcases) and
fix #4 masked but did not resolve `DecidablePred APFree` synthesis
failures in `rothNumber_pos`, `card_le_rothNumber`,
`rothNumber_achieved`. Also discovered the `classical`-tactic
instance-mismatch trap and the shared-cache stale-olean fluke.
See `sessions/2026-06-09-s5-act-verify.md`.

## Prior Focus (S4 ACT REPAIR DRAFT, 2026-06-02, PR #22075)

Four surgical fixes drafted; PR opened DRAFT because host disk was
at 99% and Docker could not run. See
`sessions/2026-06-02-s4-act-repair.md`.

## Prior Focus (S3 ACT REPAIR-DISCOVERY, 2026-06-01, PR #22001)

Fresh-build audit: 6 distinct compile failures in the file as it
sat on `main` (masked since the Mathlib v4.26.0 bump by Lake's
incremental cache). Math finding: `max_iterations_bound` is false
for `δ > 1`. Small-N enumeration plan drafted and deferred.

## Prior Focus (S2 ACT, merged 2026-05-31, PR #21520)

Shipped `rothNumber_div_tendsto_zero` (qualitative `r₃(N)/N → 0`
via `Szemeredi.Roth.roth_density_bound` and Mathlib's corners
chain). CI passed via incremental cache, which masked the
fresh-build regressions S3 later found.

## Prior Focus (S1 OBSERVE, 2026-04-03)

Initial problem understanding. The four landmark sorries (Roth
1953, Behrend 1946, Bloom–Sisask 2020, Kelley–Meka 2023) each need
≥ 1000 LOC; none is single-session tractable.

## Active Approach

S6 repairs the base file to fresh-Docker-build green. Once merged,
S7 resumes the S3 small-N enumeration plan (≤ 30 LOC):

```lean
theorem apFree_zero_one_zmod_four : APFree ({0, 1} : Finset (ZMod 4)) := by
  show ∀ a d : ZMod 4, d ≠ 0 → a ∈ ({0,1} : Finset (ZMod 4)) →
    a + d ∈ ({0,1} : Finset (ZMod 4)) → a + 2 * d ∉ ({0,1} : Finset (ZMod 4))
  decide

theorem two_le_rothNumber_four : 2 ≤ rothNumber 4 :=
  card_le_rothNumber ({0, 1} : Finset (ZMod 4)) apFree_zero_one_zmod_four

theorem rothNumber_four_le_three : rothNumber 4 ≤ 3 := by
  have h := rothNumber_le_sub_one (N := 4) (by omega)
  omega
```

**S7 note**: small-N `decide` proofs MUST use the defeq-unfold-first
pattern above (the global `APFree` instance is classical; bare
`decide` on `APFree _` goals cannot evaluate it).

## Attempt Count
- Total attempts: 6 (S1 OBSERVE, S2 ACT qualitative, S3 ACT
  REPAIR-DISCOVERY, S4 ACT REPAIR DRAFT, S5 ACT VERIFY-DISCOVERY,
  S6 ACT REPAIR this PR)
- Current approach attempts: 1
- Approaches tried: 5

## Blockers

None for the repair (this PR). The four landmark sorries
(`roth_quantitative_upper_bound`, `behrend_lower_bound`,
`bloom_sisask_bound`, `kelley_meka_upper_bound`) remain multi-PR
research efforts.

## Next Action

**S7 ACT SMALL-N** — re-add the r₃(4) ∈ [2, 3] pin (three theorems
above) on the repaired base; optionally sharpen to r₃(4) = 2 by
enumerating 3-element subsets of ZMod 4.
