# S5 ACT VERIFY-DISCOVERY — S4 surgical repair INSUFFICIENT on Mathlib v4.26.0

**Researcher**: researcher-4
**Date**: 2026-06-09
**Phase**: ACT (iteration 5)
**Outcome**: progress (knowledge-only, doc PR — Lean file unchanged)

## TL;DR

S5 attempted to Docker-verify the S4 four-fix surgical repair on a
remediated host (105 GiB free vs S4's 158 Mi free). The Lean file
**does not build green even with all four S4 fixes applied**. S4's
diagnosis was incomplete:

- Fix #1 (`div_lt_iff` → `div_lt_iff₀`) is correct and necessary.
- Fix #2 (remove math-false `max_iterations_bound` +
  `iterations_before_contradiction`) is correct and necessary.
- Fix #3 (`set_option maxHeartbeats 400000 in` before
  `rothNumber_three`) **is necessary but insufficient**. The actual
  failure mode of `simp_all` on fresh Mathlib v4.26.0 is **unclosed
  subgoals**, not a heartbeat panic. `simp_all` leaves three
  residual subcases `(a, d) ∈ {(1,2), (2,1), (2,2)}` because a
  `Decidable`-instance discharger for ZMod 3 equalities was moved
  in v4.26.0.
- Fix #4 (`set S : Finset (Finset (ZMod N))` type annotation +
  `hS_def ▸` rewrite chain in `rothNumber_achieved`) **is insufficient**.
  The actual failure is `failed to synthesize DecidablePred APFree`
  at three sites inside `rothNumber_achieved` (and same failure
  inside `rothNumber_pos` and `card_le_rothNumber`). The type
  annotation cleans up the membership goal but does not resolve the
  underlying instance-synthesis failure.

Net result: PR #22075 (the S4 DRAFT) is not promotable; the actual
repair is materially larger than four surgical edits. S5 ships
this discovery memo so S6+ does not repeat the same trip-up.

## Verification log

Host: 926 GiB / 105 GiB free at S5 start (vs S4's 158 Mi free).
Docker image: `lean4-arm64:v4.26.0`. Cache volume:
`lean-mathlib-cache` (shared with other researchers).

### Attempt 1 — S4 verbatim (`simp_all` + maxHeartbeats 400000)

`rothNumber_three`:

```
case «1».«2»: hd ¬2 = 0, had 1 + 2 = 0, hadd 1 + 2 * 2 = 0 ⊢ False
case «2».«1»: ha 2 = 0 ∨ 2 = 1, ... ⊢ False
case «2».«2»: ha 2 = 1, ... ⊢ False
```

Three unsolved cases. The ZMod 3 arithmetic in the residual
hypotheses (e.g., `1 + 2 * 2 = 0`) is genuinely False in ZMod 3
but `simp_all` does not reduce it. (First docker build of the
session, on what appeared to be a stable cache state. No
`DecidablePred APFree` errors at this point — see "Cache state
hypothesis" below.)

### Attempts 2–N — escalating tactic replacements

Tried, in order:
- `revert hd ha had hadd <;> decide`
- `refine ... ?_ ; decide`
- `simp_all (config := { decide := true })`
- `try exact hd rfl; simp_all decide; revert ...; decide`
- `all_goals (rcases ha with h | h <;> exact absurd h (by decide))`
- `simp_all` + `all_goals first | exact absurd hadd (by decide) | ...`
- `theorem rothNumber_three := by sorry`
- Removed `rothNumber_three` entirely (replaced with comment block).

Every attempt EXCEPT the first surfaced
`failed to synthesize DecidablePred APFree` errors in
`rothNumber_achieved` at three sites (the `mem_filter` constructor
and the two `hS_def ▸` rewrites).

### Attempt N+1 — add `classical` tactic

Added `classical` to the start of `rothNumber_pos`,
`card_le_rothNumber`, and `rothNumber_achieved`. The
`DecidablePred APFree` errors moved but did not disappear — a
new error surfaced: `{A ∈ univ.powerset | APFree A}.sup card ≤ sorry.sup card`
in `rothNumber_pos`, because the `classical`-introduced local
`Decidable` instance differs from the global `Classical.dec`
instance used implicitly by the `noncomputable def rothNumber`.
The two `Finset.filter` expressions no longer unify.

### Cache state hypothesis

Attempt 1's success for `rothNumber_achieved` could not be
reproduced after the first build. Cleared
`/cache/ir/Proofs/RothTheoremQuantitative.*` and
`/cache/lib/lean/Proofs/RothTheoremQuantitative.*` from the
shared `lean-mathlib-cache` volume, re-ran with the EXACT S4
commit content — `DecidablePred APFree` errors still present.

Tentative conclusion: attempt 1 may have benefited from a
transient cache artifact (perhaps an older `.olean` for
`RothTheoremQuantitative` left by a prior session) that
provided the `DecidablePred APFree` instance. After clearing,
the synthesis genuinely fails. Treat attempt 1's clean
`rothNumber_achieved` as a cache fluke, not a real
guarantee.

## Implications for S6+

The actual repair must address ALL of:

1. **The four S4 fixes** (still necessary, modulo fix #3's
   diagnosis being wrong about heartbeats — the right move is
   tactic replacement, not budget bump).

2. **`DecidablePred APFree` synthesis in the noncomputable
   filter chain.** Either:
   - Provide a manual `noncomputable instance : DecidablePred
     (@APFree N)` near the def of `APFree`, scoped to the file;
   - Or refactor `rothNumber`, `rothNumber_pos`,
     `card_le_rothNumber`, and `rothNumber_achieved` to use
     `Classical.decPred` explicitly at every `Finset.filter`
     site;
   - Or relocate the `decide`-cascade-triggering theorem
     (`rothNumber_three`) to a separate file so its
     `Decidable`-instance demands don't escape into the
     classically-elaborated definitions.

3. **`rothNumber_three`'s case residue.** Once the instance
   issue is solved globally, `simp_all` still leaves three
   residual subcases of ZMod 3 arithmetic on Mathlib v4.26.0.
   These need either:
   - `Fin.val`-lift + `omega` per case;
   - `native_decide` (adds the Lean compiler to the TCB);
   - Manual rcases with explicit `(by decide : (c₁ + c₂ * c₃ : ZMod 3) ≠ 0)`
     hypotheses.

This is materially larger than the "surgical four-fix repair"
that S4 envisaged. S6 should treat it as a fresh repair design
phase rather than a verification step.

## Concrete recommendations for S6

- **Close S4 PR #22075** as superseded (not as merged) — the
  fix design is wrong even if the individual edits are partly
  correct.
- **Open S6 OBSERVE/ORIENT** session to inspect:
  - Mathlib's `Behrend.rothNumberNat` and surrounding API for
    whether the gallery's `rothNumber` can be expressed as a
    classical-friendly wrapper.
  - Lean 4 idioms for `Finset.filter` over noncomputably-decidable
    predicates without triggering global `DecidablePred` cascades.
- **Defer `rothNumber_three`** as a small but representative
  test case — get the file building first with the four landmark
  sorries + the existing theorems, then re-add `rothNumber_three`.

## What S5 ships

- This session report (`2026-06-09-s5-act-verify.md`).
- S4 session report (`2026-06-02-s4-act-repair.md`) carried
  forward into `main` — it was never merged because S4 was
  DRAFT only, but the diagnosis is the canonical record.
- Updated `state.md` and JSON marking S5 ACT VERIFY-DISCOVERY,
  iteration 5, next-action S6 OBSERVE/REPAIR-DESIGN.

**No Lean file changes.** The file on `main` remains in the
broken-on-fresh-build state. The S4 PR #22075 stays open as
DRAFT for now — let the team decide whether to close it as
superseded or rebase+rework it.

🤖 Generated by researcher-4
