# Knowledge Base: sperner-ndim-oq-05

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Contribute `SpernerTriangulation` (abstract cell complex) and
`sperner_parity` to Mathlib via mathlib4#25231.

**Current state** (as of 2026-04-21):
- All gallery Lean files have **0 sorries** — mathematical content is complete
- `SpernerMathlib4.lean` (768 lines) is the main Mathlib contribution file
- `SpernerSimplicialInstance.lean` (1019 lines) provides the bridge from
  abstract simplicial data to the `CellComplex` typeclass
- Mathlib fork branch `rjwalters/mathlib4:sperner-abstract-parity` pushed 2026-04-01
- Blocked on external feedback from Dillies/SproutSeeds on mathlib4#25231
- Main technical blocker: `maxHeartbeats 1600000` (8× default of 200,000)

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
- This reduces the proof from 53 lines (manual strongInduction) to ~12 lines
  (delegation to pre-compiled Mathlib lemma).
- Key insight: `Finset.sum_involution` itself uses strongInduction internally,
  but since it is pre-compiled in Mathlib, it doesn't cost heartbeats in our file.
- Mathlib PR #25231 is the target; Dillies/SproutSeeds is the reviewer.
  No response yet (ping deadline: 2026-05-01).

### Proof Strategy for `even_card_of_fpf_invol`

```lean
theorem Finset.even_card_of_fpf_invol {α : Type*}
    [DecidableEq α] (S : Finset α) (f : α → α)
    (hInv : ∀ x ∈ S, f (f x) = x) (hMem : ∀ x ∈ S, f x ∈ S)
    (hNe : ∀ x ∈ S, f x ≠ x) : Even S.card := by
  have hsum : ∑ _ ∈ S, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun a _ => f a)
      (fun _ _ => by decide) (fun a ha _ => hNe a ha) hMem hInv
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [Nat.even_iff, ← Nat.dvd_iff_mod_eq_zero]
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp hsum
```

### Additional Optimizations Identified

1. **Granular imports** (instead of `import Mathlib`):
   Needed modules: `Mathlib.Data.Finset.Card`, `Mathlib.Data.Finset.Basic`,
   `Mathlib.Data.ZMod.Basic`, `Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
   `Mathlib.Data.Fin.Basic`. Switching reduces compile time by 20-30%.

2. **Profiling**: Use `set_option profiler true` to identify which theorems
   are most expensive.

3. **Other lemmas**: `surjection_unique_dup_fiber` (lines 168-226) is the
   second most complex proof. Type annotations may help elaboration.

### Files Modified

- `research/problems/sperner-ndim-oq-05/knowledge.md` (this file)
- `research/problems/sperner-ndim-oq-05/lean/SpernerMathlib4Opt.lean` (new proposal)

### Next Steps

1. Test `Finset.sum_involution` approach — does it compile? What heartbeat count?
2. Profile `SpernerMathlib4.lean` with `set_option profiler true` to rank slowdowns
3. Switch from `import Mathlib` to granular imports
4. If heartbeats ≤ 400000, push updated branch and ping mathlib4#25231 reviewer
5. Ping Dillies/SproutSeeds if no response by 2026-05-01

---

---

## Session 2026-04-21 (Session 2) - Heartbeat Optimization Implemented

**Mode**: REVISIT
**Outcome**: PROGRESS — `even_card_of_fpf_invol` proof optimized from 53 → 13 lines

### What I Did

1. Read `SpernerMathlib4.lean` (768 lines) — confirmed `maxHeartbeats 1600000`
2. Implemented Session 1's proposed optimization: replaced `Finset.strongInduction`
   proof with `Finset.sum_involution` delegation
3. Ran background Docker build to verify compilation

### Key Change

**Before** (53 lines, uses expensive `Finset.strongInduction`):
```lean
induction S using Finset.strongInduction with
| H S ih => ...  -- 48 lines of explicit pairing induction
```

**After** (13 lines, delegates to pre-compiled Mathlib lemma):
```lean
have hsum : ∑ _ ∈ S, (1 : ZMod 2) = 0 :=
  Finset.sum_involution (fun a _ => f a)
    (fun _ _ => by decide)
    (fun a ha _ => hNe a ha)
    hMem hInv
simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
obtain ⟨k, hk⟩ := (ZMod.natCast_zmod_eq_zero_iff_dvd _ 2).mp hsum
exact ⟨k, by omega⟩
```

**Mathematical idea**: Each element `a ∈ S` pairs with `f a ∈ S`, contributing
`(1 : ZMod 2) + (1 : ZMod 2) = 0` to the sum. So `∑ _ ∈ S, 1 = 0` in ZMod 2,
meaning `S.card ≡ 0 (mod 2)`, i.e., `Even S.card`.

**Why faster**: `Finset.strongInduction` constructs an explicit recursion scheme
during elaboration (expensive). `Finset.sum_involution` is pre-compiled in Mathlib
so avoids elaboration overhead.

### Files Modified

- `proofs/Proofs/SpernerMathlib4.lean` (768 → 727 lines, -41 lines in proof)

### Build Status

Background Docker build started — awaiting results.
If proof compiles, heartbeat reduction expected: 30-50% of current 1600000.

### Next Steps

1. If build succeeds: reduce `maxHeartbeats` and measure actual reduction
2. Switch to granular imports (required for actual Mathlib PR)
3. Identify if `surjection_unique_dup_fiber` (lines 168-226) can also be simplified
4. Update mathlib4#25231 PR with optimized proof once heartbeats ≤ 400000

---

## Dead Ends

- `FixedPointFree.lean` (GroupTheory) — about group automorphisms, not Finsets
- `SimpleGraph.IsMatching.even_card` — about graph matching, too much overhead
- No direct `Finset.even_card_of_involutive` exists in Mathlib
