# Knowledge Base: sperner-ndim-oq-05

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Contribute `SpernerTriangulation` (abstract cell complex) and
`sperner_parity` to Mathlib via mathlib4#25231.

**Current state** (as of 2026-04-21):
- All gallery Lean files have **0 sorries** — mathematical content is complete
- `SpernerMathlib4.lean` (731 lines) is the main Mathlib contribution file
- `SpernerSimplicialInstance.lean` (1019 lines) provides the bridge from
  abstract simplicial data to the `CellComplex` typeclass
- Mathlib fork branch `rjwalters/mathlib4:sperner-abstract-parity` needs update
- Blocked on external feedback from Dillies/SproutSeeds on mathlib4#25231
- **HEARTBEAT BLOCKER RESOLVED**: `set_option maxHeartbeats` removed entirely.
  File now compiles within Lean's default 200,000 heartbeat limit.

---

## Session 2026-04-21 (Session 2) - Heartbeat Optimization ACHIEVED

**Mode**: FRESH (continuing from Session 1 optimization plan)
**Outcome**: MAJOR PROGRESS — heartbeat blocker eliminated

### What I Did

1. Applied `Finset.sum_involution` optimization to `even_card_of_fpf_invol`
2. Replaced 53-line `strongInduction` proof (lines 57–109) with 18-line
   `ZMod 2` proof using `Finset.sum_involution`
3. Fixed deprecation: replaced `ZMod.natCast_zmod_eq_zero_iff_dvd` →
   `ZMod.natCast_eq_zero_iff`
4. Tested heartbeat reduction: 1,600,000 → **no limit needed** (< 200,000)
5. Removed `set_option maxHeartbeats 1600000` entirely from the file

### Key Findings

- `Finset.sum_involution` exists in Mathlib v4.26.0 and is used in
  this codebase (BallotProblemOQ03OQ02.lean)
- The optimized proof compiles in Docker build (85s → 38s wall time)
- Heartbeat budget tested: 1600000 ✓, 800000 ✓, 400000 ✓, 200000 ✓, none ✓
- `ZMod.natCast_zmod_eq_zero_iff_dvd` is deprecated; the replacement
  `ZMod.natCast_eq_zero_iff` works in Mathlib v4.26.0
- File reduced from 768 lines to 731 lines (removed `set_option` + 37 proof lines)

### Proof Strategy for `even_card_of_fpf_invol` (Working)

```lean
have hsum : ∑ _ ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => f a)
      (fun _ _ => by decide)      -- (1 : ZMod 2) + 1 = 0
      (fun a ha _ => hNe a ha)    -- f a ≠ a since 1 ≠ 0
      hMem                         -- f a ∈ S for a ∈ S
      hInv                         -- f (f a) = a for a ∈ S
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [Nat.even_iff, ← Nat.dvd_iff_mod_eq_zero]
  exact (ZMod.natCast_eq_zero_iff _ 2).mp hsum
```

**Key insight**: The 53-line `strongInduction` proof was expensive to
elaborate in Lean because it constructs an explicit recursion scheme over
Finsets. `Finset.sum_involution` delegates to a pre-compiled Mathlib lemma,
avoiding elaboration overhead entirely.

### Files Modified

- `proofs/Proofs/SpernerMathlib4.lean` (lines 51–109 replaced)
  - Removed: `set_option maxHeartbeats 1600000`
  - Replaced: 53-line strongInduction proof → 18-line sum_involution proof
  - Fixed: `ZMod.natCast_zmod_eq_zero_iff_dvd` → `ZMod.natCast_eq_zero_iff`

### Next Steps

1. **Update Mathlib fork branch**: Push optimized `SpernerMathlib4.lean` to
   `rjwalters/mathlib4:sperner-abstract-parity`
2. **Comment on mathlib4#25231**: Report heartbeat resolution, ping reviewer
3. **Granular imports** (optional, further cleanup): Replace `import Mathlib`
   with specific imports if Mathlib style guide requires it
4. **Ping deadline**: If no Dillies/SproutSeeds response by 2026-05-01,
   escalate or find new reviewer

---

## Session 2026-04-21 (Session 1) - Heartbeat Optimization Research

**Mode**: FRESH (first research on this problem)
**Outcome**: optimization plan found; awaiting external PR feedback

### What I Did

1. Read all Sperner-related Lean files to understand current state
2. Confirmed: `SpernerMathlib4.lean` has 0 sorries, `maxHeartbeats 1600000`
3. Searched Mathlib for alternatives to `Finset.even_card_of_fpf_invol`
4. Found: `Finset.sum_involution` in `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
5. Designed optimized 12-line proof to replace 53-line strongInduction proof

### Key Findings

- `Finset.even_card_of_fpf_invol` (lines 57-109 of SpernerMathlib4.lean) uses
  `Finset.strongInduction`, which is expensive to elaborate in Lean.
- **Optimization**: Apply `Finset.sum_involution` from Mathlib with
  `f = const (1 : ZMod 2)` to get `∑ _ ∈ S, 1 = 0`, then conclude
  `(S.card : ZMod 2) = 0`, i.e., `Even S.card`.
- Mathlib PR #25231 is the target; Dillies/SproutSeeds is the reviewer.

---

## Dead Ends

- `FixedPointFree.lean` (GroupTheory) — about group automorphisms, not Finsets
- `SimpleGraph.IsMatching.even_card` — about graph matching, too much overhead
- No direct `Finset.even_card_of_involutive` exists in Mathlib
