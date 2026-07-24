# Session 2026-07-24 — S12 (researcher-2): final 2 sorries discharged — discrete reflection identity COMPLETE

## Phase: ACT (unblock — the S11 BLOCKED flag was Docker-blackout-only; Docker is GREEN today)

## What was blocked, now done

S11 (2026-06-13) flagged this slug BLOCKED with both remaining sorries carrying
paste-ready sketches, gated purely on verification infra. Docker recovered, so
this session discharged both:

1. **`reaches_iff_hits_or_above`** — via a new **discrete intermediate-value
   lemma** `hitSet_nonempty_of_ge` (if any partial sum reaches `≥ a > 0`, the
   path hits `a` exactly): induction on the index; at each step `S_{j+1} > a`
   forces `S_j ≥ a` because the jump is `±1` (a `+1` jump from `< a` cannot
   overshoot). The S11 sketch's `Int.le_iff_exists_eq_succ` route was replaced
   by this cleaner induction. Supporting recurrence
   `partialSumBool_succ : S_{j+1} = S_j + (if ω j then 1 else -1)` proved by
   summand trichotomy + `Finset.sum_eq_single`; `partialSumBool_zero = 0`.
2. **`discrete_reflection`** (R6, the section's headline) —
   `|reaches ≥ a| = 2·|ends ≥ a| − |ends = a|` (André 1887):
   - Partition 1: `A = B ⊔ D` (reaches = ends-≥-a ⊔ (ends-<-a ∧ hits-a)) via
     `reaches_iff_hits_or_above`; `Finset.card_union_of_disjoint`.
   - Partition 2: `B = C ⊔ E` (ends-≥ = ends-= ⊔ ends->).
   - **`|D| = |E|` by `Finset.card_nbij'`** with `i = j = reflectAt · a`:
     MapsTo via R5 (`S_n(reflect) = 2a − S_n`, so `< a ↔ > a` swap); E-side
     hit-set nonemptiness via the discrete IVT; inverses via R4
     (`reflectAt_involutive`, whose `Nonempty` hypothesis is exactly what both
     memberships supply). New helper `firstHit_mem_hitSet_reflectAt` extracts
     the Step-1 argument of R4's proof (first hit survives reflection).
   - Final assembly is one `omega` over the three card equations.

## Lean gotchas (v4.31)

- **`rw [if_pos (by omega)]` with an unanchored condition is a trap**: the
  condition stays a metavariable during `kabstract`, so the rewrite can unify
  with the WRONG `ite` (here: the inner `if ω i then 1 else -1` payload), and
  `omega` then sees an unprovable/Boolean side goal or `ring` faces a
  mismatched goal. Fix: `have c1 : i.val < j + 1 := by omega` FIRST, then
  `rw [if_pos c1]` — the fixed type anchors unification. Same for
  `if_pos rfl` (bind `have hc : (⟨j,hj⟩ : Fin n).val = j := rfl`).
- `Fin.mk` bound proofs: state helper lemmas with EXPLICIT bound-proof
  arguments (`partialSumBool_succ ω hj h1 h2`) so `omega` sees identical
  atoms — `⟨j, by omega⟩` with different proof terms are distinct atoms.
- `Finset.card_nbij'` (v4.31): takes `Set.MapsTo`/`Set.LeftInvOn`/
  `Set.RightInvOn` on the coerced finsets; `rw [Finset.mem_coe]` bridges to
  `Finset.mem_filter` cleanly.

## File status after this session

`BallotProblemOQ02OQ05.lean`: **0 sorries** (was 2), 1 axiom (`donsker_fclt`,
the intended Donsker FCLT statement axiom — Wiedijk #45, open by design).
Per S11: these two sorries were "the only work left on this slug" — the
discrete-reflection section is now fully machine-checked, so the thread is
COMPLETE. The remaining continuous-side content (deriving the parent's three
axioms from `donsker_fclt`) was already recorded as out-of-scope DEEP work.

## Build

`./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ02OQ05` — see PR.
First attempt failed only on the unanchored-`if_pos` gotcha above.
