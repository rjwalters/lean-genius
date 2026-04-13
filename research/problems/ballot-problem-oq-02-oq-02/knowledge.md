# Knowledge Base: ballot-problem-oq-02-oq-02

First Passage Time Characterization via csInf Theory

---

## Problem Understanding

The parent `BallotProblemOQ02.lean` uses an axiom:
```
axiom firstPassageTime_eq_maxEvent :
  {ω | firstPassageTime bm a ω ≤ T} = maxEvent bm a T
```
OQ-02 asks whether this can be proved from `path_continuous` and csInf theory.

---

## Session 2026-04-02 (Session 1) — COMPLETED

**Mode**: FRESH
**Outcome**: completed — full proof with 0 sorries, builds successfully

### Key Finding: sInf ∅ = 0 in Lean ℝ

In `ConditionallyCompleteLinearOrder ℝ`, `Real.sInf_empty : sInf ∅ = 0` (NOT +∞).
This makes the parent axiom technically false without a nonemptiness hypothesis:
- If a path never reaches level `a`, hitting set is ∅, so `firstPassageTime = sInf ∅ = 0 ≤ T`
- But `ω ∉ maxEvent` since the path never hits `a`

### Proof Architecture

1. **Hitting set is closed** (from path continuity): preimage of `[a,∞)` under continuous `W(·,ω)`
   - Used `IsClosed.preimage hcont` (not `Continuous.isClosed_preimage` — that name doesn't exist)
2. **Easy direction**: `maxEvent → firstPassageTime ≤ T` via `csInf_le`
3. **Hard direction**: Under nonemptiness, `firstPassageTime ≤ T → maxEvent` via `IsClosed.csInf_mem`
4. **IVT**: `isPreconnected_Icc.intermediate_value₂` with `f = W(·,ω)` and `g = const a`
5. **Nonemptiness from IVT**: When `W(0,ω) < a ≤ W(T,ω)`, IVT gives a crossing point

### Techniques

- `IsClosed.csInf_mem hne hbdd` — closed bounded-below nonempty sets contain their infimum
- `isPreconnected_Icc.intermediate_value₂` — two-function IVT for crossing point
- `isClosed_Ici.preimage hcont` — correct name for preimage closure

### Main Results (0 sorries)

- `fpt_le_iff_maxEvent`: Under nonemptiness, `firstPassageTime bm a ω ≤ T ↔ ω ∈ maxEvent bm a T`
- `fpt_le_set_eq_maxEvent`: Set-level equality when nonemptiness holds for all ω
- `ivt_first_crossing`: IVT gives explicit crossing time `s ∈ (0,T]` with `W(s,ω) = a`

### Files Modified

- `proofs/Proofs/BallotProblemOQ02OQ02.lean` (new, ~190 lines)

---

## Dead Ends

- `Continuous.isClosed_preimage` — lemma name doesn't exist; use `IsClosed.preimage` instead
- `IsPreconnected.intermediate_value₂` with a single-function form — it's a two-function crossing theorem; apply with `g = const a`
