# Current State

**Phase**: AUDIT
**Since**: 2026-04-27
**Iteration**: 2
**Last Updated**: 2026-04-27

## Current Focus

Metadata sync + axiom-elimination refactor planning. Lean file
`proofs/Proofs/Erdos827Problem.lean` has 4 axioms, 14 theorems, 0 sorries —
significantly more proved than the original metadata claimed (state.md and
src/data JSON were stuck at iteration 1 / NEW phase despite multiple
axiom-elimination PRs).

## Axiom Inventory (4)

1. `minimalNk : ℕ → ℕ` — opaque function (the threshold itself)
2. `minimalNk_valid` — universal property of the threshold
3. `minimalNk_sharp` — minimality property
4. `martinez_roldan_pensado` — published bound: ∃ C > 0, ∀ k ≥ 3, minimalNk k ≤ C·k⁹

## Theorem Inventory (14)

Structural:
- `parabolaPoint_injective`, `parabolaSet_card`, `parabolaSet_gp`
- `distSq_comm`, `distSq_self`, `distSq_nonneg`, `distSq_eq_zero_iff`
- `generalPosition_subset`, `allDistinctCircumradii_subset`

Existence & combinatorial:
- `nk_ge_k`: k ≤ minimalNk k via parabola GP construction
- `allDistinctCircumradii_of_card_three`: vacuous case for |T|=3
- `nk_three`: minimalNk 3 = 3
- `nk_monotone`: k₁ ≤ k₂ → minimalNk k₁ ≤ minimalNk k₂
- `nkExists_of_axioms`: NkExists k for k ≥ 3

## Active Approach

**Refactor opportunity** (not yet attempted; requires Docker to verify):

The triple {minimalNk, minimalNk_valid, minimalNk_sharp} can be collapsed
to **one** axiom plus a noncomputable definition:

```lean
def NkProperty (k n : ℕ) : Prop :=
  ∀ S : Finset Point, GeneralPosition S → n ≤ S.card →
    ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

axiom nk_property_witness (k : ℕ) (hk : 3 ≤ k) : ∃ n, NkProperty k n

noncomputable def minimalNk (k : ℕ) : ℕ :=
  if h : ∃ n, NkProperty k n then Nat.find h else 0
```

Then `minimalNk_valid` follows from `Nat.find_spec`, and `minimalNk_sharp`
follows from `Nat.find_min`. This reduces 4 → 2 axioms.

Further: properly stating Martinez-Roldán-Pensado as a free-standing
existence theorem with explicit polynomial witness *implies*
`nk_property_witness`, so in principle the axiom count could drop to 1
(the published MRP theorem itself).

## Blockers

- **Disk pressure**: 89% capacity, 1.6GB free. Cannot run Docker build to
  verify a refactor PR (per memory, disk-full sessions corrupt containerd).
- **Refactor scope**: switching to `Nat.find` requires updating proofs of
  `nk_ge_k`, `nk_three`, `nk_monotone` (each consumes
  `minimalNk_valid`/`_sharp`). Mechanical but needs build verification in
  one PR.

## Next Action

1. Wait for disk pressure to clear (other agents complete or cleanup runs).
2. Prototype Nat.find refactor in fresh worktree; verify with Docker.
3. Submit refactor as separate PR (axiom count 4 → 2).

For now: this audit + insight documentation lands the structural
understanding so the next session can proceed directly to implementation.

## Attempt Counts

- Total attempts: 2 (initial axiom-elimination wave + this audit)
- Current approach attempts: 1 (audit/refactor planning)
- Approaches tried: parabola GP construction (success), audit (in progress)
