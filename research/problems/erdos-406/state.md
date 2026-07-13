# Current State

**Phase**: ACT
**Since**: 2026-06-09T22:00:00.000Z
**Iteration**: 2

## Current Focus

Maintenance + extension iteration on Erdős #406 (powers of 2 with only digits 0,1 in base 3).

## Active Approach

Two-track contribution:
1. **Maintenance / repair**: Restore `Erdos406Problem.lean` to building state at Mathlib v4.26.0 after upstream API/path changes broke six unique error sites in the existing file (was last verified building under an older Mathlib).
2. **Mathematical extension**: Add `digits01_double_eq_map` — the pointwise digit-doubling *equality* strengthening the previously-proved `digits01_double_digits02` bound. This is the precise per-column no-carry statement Kummer's theorem consumes.

## What landed (iter-2)

### Mathlib v4.26.0 compatibility
- Import path: `Mathlib.Data.Nat.Digits` → `Mathlib.Data.Nat.Digits.Defs`
- `List.mem_cons_self a l` → `List.mem_cons_self` (arg-free signature)
- `List.not_mem_nil d` → drop arg; use `simp at hd` for the empty-digits case
- `Finset.not_mem_empty` → `Finset.notMem_empty` (deprecation rename)
- `Nat.pred` injectivity via `Nat.succ_pred_eq_of_pos` (omega now sees the witness)
- Moved `instance Decidable (HasOnlyDigits01Base3 n)` and `..12..` above the `native_decide`-using theorems (instance scoping in v4.26.0)
- Dropped unused `simp only [Function.comp, …]` argument
- Symm-fixed an IH application in `sum_of_distinct_powers_digits01` (Mathlib v4.26.0 flipped the equality direction surfaced by `hT`)

### Math bug fix
- `dense_complete_to_15` originally claimed the n≤15 set for `HasOnlyDigits12Base3 (2^n)` was `{1, 3, 5, 7, 15}`. This is **mathematically incorrect**: 2^0=[1], 2^2=[1,1], 2^4=[1,2,1] all consist of digits in {1,2}, while 2^5=[2,1,0,1], 2^7=[2,0,2,1,1] both contain a 0 and so are NOT in the set. The corrected statement is `{0, 1, 2, 3, 4, 15}` (verified by `native_decide` on the 16 cases). The theorem now succeeds under v4.26.0 with the correct disjunction.

### Mathematical extension
- `digits01_double_eq_map (n : ℕ) (h : HasOnlyDigits01Base3 n) : Nat.digits 3 (2 * n) = (Nat.digits 3 n).map (· * 2)` — proves the digit list of `2n` is literally the pointwise double of the digit list of `n` when `n` is ternary-sparse. Strengthens the previous bound `digits01_double_digits02` (∀ d ∈ digits 3 (2n), d ∈ {0,2}) to an exact list-level identity. This is the lockstep no-carry equation Kummer's theorem applies to `n + n` to conclude `v₃(Nat.choose (2n) n) = 0`.

## Blockers

None at HEAD; build is clean (Docker 3058 jobs).

## Next Action

A reasonable next iteration would attempt the converse: define `HasOnlyDigits02Base3` and prove the biconditional `HasOnlyDigits02Base3 m ↔ ∃ k, m = 2 * k ∧ HasOnlyDigits01Base3 k`. The forward direction follows from `digits01_double_eq_map`; the reverse goes through `Nat.digits` strong-induction structurally mirroring `digits01_sum_of_powers`. This would close out a clean digit-set transfer characterization useful for any future Kummer/lifting-the-exponent extension.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib upgrade + digit-doubling equality refinement)
