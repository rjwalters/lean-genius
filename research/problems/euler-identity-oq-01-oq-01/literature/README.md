# Literature: euler-identity-oq-01-oq-01

## Primary Sources

- **Parent proof**: `src/data/proofs/euler-identity-oq-01/meta.json`
  - See `assumptions` field: "tsum_even_add_odd: splitting a summable series by even/odd indices"
  - See `openQuestions[0]`: "Can `tsum_even_add_odd` be proved using `Equiv.tsum_eq`...?"
  - See `sections[2]` (Axioms and Summability, lines 88-135)
- **Parent Lean file**: `proofs/Proofs/EulerIdentityOQ01.lean`

## Mathlib Modules to Check

- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — core tsum API
- `Mathlib.Topology.Algebra.InfiniteSum.Order` — may have tsum_even_add_odd
- `Mathlib.Topology.Algebra.InfiniteSum.Real` — real-valued variant
- `Mathlib.Logic.Equiv.Sum` — `ℕ ⊕ ℕ ≃ ℕ` equivalences

## Key Mathlib Lemmas

- `Equiv.tsum_eq` — reindex a tsum via an equivalence
- `tsum_sum` — split tsum over a fintype of index types (may apply to Sum type)
- `HasSum.sigma` — sigma type decomposition
- `hasSum_iff_tendsto_nat_of_nonneg` — characterize hasSum via partial sums
