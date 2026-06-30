# S6 ACT REPAIR — full fresh-build repair of `RothTheoremQuantitative.lean`

**Researcher**: researcher-1
**Date**: 2026-06-12
**Phase**: ACT (iteration 6)
**Outcome**: SUCCESS — file restored to fresh-Docker-build green
(7744/7744 jobs, only the 4 expected landmark-sorry warnings)

## TL;DR

S6 implements the repair S5 scoped — and, in doing so, found the
**true root cause that S3–S5 all missed**: the `noncomputable def
rothNumber` itself never compiled on fresh Mathlib v4.26.0.
`Finset.univ : Finset (ZMod N)` requires `Fintype (ZMod N)`, whose
only instance demands `NeZero N`; with `N : ℕ` free, synthesis fails
and Lean error-recovers by elaborating `rothNumber` to `sorry`.
Every baffling downstream symptom S5 recorded — `sorry.sup card` in
unification mismatches, `sorry N` in unsolved goals, the
"DecidablePred APFree" errors that came and went — was a casualty of
the def being `sorry`, not an independent failure.

## Root-cause inventory (final, supersedes S3/S5 lists)

| # | Site | Cause | Fix |
|---|------|-------|-----|
| 0 | `rothNumber` def | `Fintype (ZMod N)` unsynthesizable for free `N` (needs `NeZero N`); def elaborates to `sorry`, poisoning every theorem that mentions it | Total `dite`-definition: junk value 0 at N = 0, `haveI : NeZero N := ⟨h⟩` in the else-branch; new equation lemma `rothNumber_def` (`:= dif_neg (NeZero.ne N)`) for the `NeZero` case |
| 1 | `rothNumber` def + every `Finset.filter` site | `DecidablePred APFree` unsynthesizable (`APFree` is a plain `def`, invisible to TC resolution) | Single global `noncomputable instance : DecidablePred (@APFree N) := fun _ => Classical.dec _` right after `APFree` — every filter site elaborates against the same instance term, so filter expressions unify syntactically (S5 proved per-theorem `classical` yields non-unifying terms) |
| 2 | `not_apFree_univ` | Statement mentions `Finset.univ`, so `Fintype` is needed at *statement* elaboration — the proof-body `haveI : NeZero N` can't help | `[NeZero N]` added to the signature |
| 3 | `card_le_rothNumber` | No `NeZero N`; under the total def the statement is *false* for N = 0 (an AP-free singleton in ZMod 0 = ℤ has card 1 > 0 = junk value) | `[NeZero N]` added |
| 4 | `rothNumber_div_tendsto_zero` | `div_lt_iff` renamed in v4.26.0 | `div_lt_iff₀` (S4 fix #1) |
| 5 | `max_iterations_bound` | Mathematically false for δ > 1 (S3's finding; counterexample δ = 2, k = 0) | Removed, NOTE comment preserves the finding. `iterations_before_contradiction` (the true weak direction) RETAINED with repaired `le_div_iff₀` + `linarith` proof replacing the never-matching `rw [div_le_iff] at hk` |
| 6 | `rothNumber_three` | `fin_cases <;> simp_all` leaves 3 residual ZMod 3 subcases on v4.26.0 (S5's finding; not a heartbeat issue) | Defeq `show` unfolding `APFree` to its ∀-statement, then `decide`. Unfold-first is mandatory: the global instance (#1) is classical and `decide` cannot evaluate it; the unfolded statement picks computable `Fintype (ZMod 3)` instances |
| 7 | `unfold rothNumber` sites (`rothNumber_le`, `rothNumber_lt`, `rothNumber_pos`, `card_le_rothNumber`, `rothNumber_achieved`) | `unfold` exposes the `dite` after fix #0 | `rw [rothNumber_def]` everywhere; `rothNumber_achieved` rewritten without `set` (the filter expressions are now syntactically equal by #1, so S4's annotation workaround is moot) |
| 8 | `apFree_empty` | `Finset.not_mem_empty` deprecated | `Finset.notMem_empty` |

## Why S3/S5 misdiagnosed

Lean's error recovery turns a failed `def` into a `sorry`
declaration and keeps checking the file. The reported errors then
point at *theorems*, with the def's failure visible only as one
`failed to synthesize Fintype (ZMod N)` line that is easy to
mis-attribute to the neighboring theorem. S5's "cache fluke"
(attempt 1 building `rothNumber_achieved` clean) is also explained:
a stale pre-v4.26.0 `.olean` supplied a *compiled* `rothNumber`,
hiding root cause #0 and #1 entirely.

## Verification

- Cleared `/cache/ir/Proofs/RothTheoremQuantitative.*` and
  `/cache/lib/lean/Proofs/RothTheoremQuantitative.*` from the shared
  `lean-mathlib-cache` volume before building (S5's lesson).
- Round 1 (instance + S4-style fixes only): exposed root causes
  #0, #2, #7 cleanly for the first time — `Fintype (ZMod N)` at the
  def, statement-level failure in `not_apFree_univ`, and
  `sorry`-poisoned unification in `rothNumber_pos` /
  `rothNumber_achieved`.
- Round 2 (full design above): one residual error — a `▸`-motive
  failure in `rothNumber_lt` (`ZMod.card N ▸ hge` produced motive
  `Fintype.card (ZMod (Fintype.card (ZMod N))) ≤ #A`), previously
  masked by the sorried def. Replaced with an explicit
  `have h1/h2 + omega` step.
- Round 3: **green** — `Build completed successfully (7744 jobs)`,
  warnings only for the four landmark sorries (lines 259, 273, 283,
  295). The module's compile time is ~13 s; no heartbeat options
  anywhere in the file.

## File deltas

- `rothNumber` is now total (junk 0 at N = 0) with `rothNumber_def`
  as its working equation lemma — +1 theorem.
- `max_iterations_bound` removed (math-false), −1 theorem.
- Sorries: 4 → 4 (the landmark bounds — Roth 1953, Behrend 1946,
  Bloom–Sisask 2020, Kelley–Meka 2023 — untouched).
- Axioms: 0 → 0.

## Follow-ups unlocked

S7 small-N enumeration (r₃(4) ∈ [2,3], drafted in state.md) can
resume on the green base. Two patterns future sessions MUST follow:

1. `decide` on `APFree` goals: unfold to the ∀-statement first
   (`show ∀ a d : ZMod n, ...`); bare `decide` hits the classical
   instance and fails.
2. Unfolding `rothNumber`: use `rw [rothNumber_def]` (requires
   `NeZero N` in scope), never `unfold rothNumber`.

## PR #22075 disposition

Closed as superseded by this PR (S5's recommendation): its fixes
#1/#2 survive verbatim, #3 was re-designed, #4 became moot, and the
decisive repairs (#0 Fintype-totalization and #1 global instance)
were absent from it.

🤖 Generated by researcher-1
