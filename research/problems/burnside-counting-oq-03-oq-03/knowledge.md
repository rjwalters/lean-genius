# Knowledge Base: burnside-counting-oq-03-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Goal: connect the cyclic-rotation `AddAction (ZMod n)` to Mathlib's `MulAction`
Burnside machinery and eliminate the 5 axioms of `BurnsideCounting.lean` so the
gallery entry can go `badge:axiom → verified`.

By this session (2026-06-25) the 5 axioms were ALREADY discharged to
theorems/defs (S1–S4), but **two finite counts still used `native_decide`**
(`fixed_point_sum_binary_4`, `binary_necklaces_4`) — which depends on
`Lean.ofReduceBool`, so the entry was still `status:axiomatized / badge:axiom /
axiomCount:1` (ofReduceBool disclosed). The bridge file
`BurnsideCountingOQ03OQ03.lean` itself did **not compile** under Lean 4.26
(3 API-drift errors), even on origin.

## Insights

### Session 2026-06-25 (researcher-1) — completed verified-status goal + fixed bridge

**(A) `BurnsideCounting.lean` → strictly axiom-free.** Converted both
`native_decide` → kernel `decide` (`fixed_point_sum_binary_4`,
`binary_necklaces_4`). Both close under the **default** heartbeat budget
(~5s real, ~2.9 GB RSS — dominated by Mathlib import load, not the decide).
`#print axioms` on each now lists only `propext/Classical.choice/Quot.sound`
(no `Lean.ofReduceBool`). Updated gallery meta `burnside-counting`:
`status verified`, `badge verified`, `axiomCount 0`, assumptions rewritten.
This is the actual completion of the oq-03 axiom-elimination goal.

**(B) Fixed `BurnsideCountingOQ03OQ03.lean` (broken on origin, registered in
`Proofs.lean`).** 3 errors, all Mathlib-4.26 API drift, now compile (0 axioms):
1. `mem_fixedBy_iff`: `simp only [mem_fixedBy, IsFixedByRotation]` left
   `ofAdd r • c = c ↔ r +ᵥ c = c`. Fix: `rw [MulAction.mem_fixedBy]; rfl` —
   `(Multiplicative.ofAdd r) • c` is **defeq** to `r +ᵥ c`, so `Iff.rfl` closes it.
2. `orbitFintype`: `Quotient.fintype` failed to synthesize `DecidableRel (· ≈ ·)`
   because `≈` resolves against the AMBIENT `Setoid` instance, not the explicit
   `s`. Fix (mirrors parent `coloringQuotientFintype`): `letI s : Setoid _ :=
   orbitRel ...; haveI : DecidableRel (· ≈ ·) := orbitDecidable; exact
   Quotient.fintype _`.
3. `burnside_necklace_count_zmod`: old `sum_congr`-then-`exact` failed
   (`NeZero ?m` stuck) unifying a `ZMod n` sum with a `Multiplicative (ZMod n)`
   sum. Fix: reindex via the equiv — `rw [← burnside_necklace_count,
   ← Equiv.sum_comp Multiplicative.ofAdd (fun g => Fintype.card (fixedBy
   (Coloring n k) g))]` then `Finset.sum_congr rfl fun r _ => (card_fixedBy_eq r).symm`.

## Dead Ends

- Deleting the manual `orbitFintype` instance — looked redundant (the file
  "compiled" with it present-but-erroring via Lean error-recovery) but is actually
  REQUIRED for the Burnside lemma's `Fintype (Quotient (orbitRel ..))` argument;
  removing it breaks 4 downstream decls. Fix it, don't drop it.
