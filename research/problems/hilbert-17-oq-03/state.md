# Current State

**Phase**: MATURE (substance delivered via child entries)
**Since**: 2026-07-08
**Iteration**: 2

## Current Focus

None. This slug ("Complexity of Deciding PSD Polynomial Sum-of-Squares") is a
**complexity meta-question**, not a clean Lean theorem target. Its mathematical
substance — the PSD ⊋ SOS separation and the PSD=SOS classification cases — has
been fully delivered as verified, 0-axiom **child** gallery entries and wired into
the parent `hilbert-17` (see knowledge.md for the multi-session log). No
incremental Lean work remains on this node itself.

## What was delivered (children of oq-03, all verified / 0-axiom)

- `hilbert-17-oq-03-oq-02` — Motzkin polynomial is **not** SOS (`Hilbert17MotzkinNotSOS.lean`).
- `hilbert-17-oq-03-oq-03` — Robinson polynomial is **not** SOS (`Hilbert17RobinsonNotSOS.lean`,
  zero-set / 10-point det-128 linear-algebra route).
- `hilbert-17-oq-03-oq-04` — univariate PSD ⇒ SOS (`Hilbert17UnivariatePSDSOS.lean`).
- Quadratic PSD ⇒ SOS via the Gram/√M engine (`Hilbert17QuadraticGram.lean`).

All four are imported into `Proofs/Hilbert17SumOfSquares.lean`, which drove the
parent from **10 → 1 axioms**.

## Blockers

The parent `hilbert-17` has exactly **one** axiom left: `pfister_bound_aux`
(Pfister's 2ⁿ-square bound over formally real fields). This is genuinely deep with
no short Mathlib path (confirmed across sessions) and is correctly left axiomatized.
The complexity classification itself (SOS membership ≈ SDP feasibility) is a
meta/complexity statement with no clear meaningful Lean formalization.

## Next Action

None for this slug. Future claimants should release without fabricating value.
The only remaining hard target is `pfister_bound_aux` (multi-session, Pfister
forms), tracked under the parent `hilbert-17`.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
