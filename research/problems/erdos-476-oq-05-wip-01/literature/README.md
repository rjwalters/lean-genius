# Literature for erdos-476-oq-05-wip-01

## Lean Files in This Repo

| File | Description |
|------|-------------|
| `proofs/Proofs/Erdos476OQ05Problem.lean` | Main WIP proof (2 sorries, 407 lines) |
| `proofs/Proofs/Erdos476OQ05Aristotle.lean` | Aristotle companion exposing provable sorries |

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-476` | Parent: Cauchy-Davenport theorem (already verified) |
| `erdos-476-oq-05` | Direct parent: Vosper theorem WIP proof |
| `erdos-476-oq-05-incomplete-01` | Related incomplete formalization attempt |

## Key Papers

### Primary

- **Vosper (1956)**: "The critical pairs of subsets of a group of prime order".
  *J. London Math. Soc.* 31, 200–205.
  _The original theorem. Proof structure is the template for filling the two sorries._

- **Lev (2000)**: "Restricted set addition in groups". Covers equality conditions for
  additive combinatorics results in ℤ/pℤ.

### Lean/Mathlib Context

- `Mathlib.Combinatorics.Additive.CauchyDavenport` — the parent theorem
- `Mathlib.Data.ZMod.Basic` — ℤ/pℤ arithmetic, coercion lemmas
- `Mathlib.Data.Finset.Card` — `Finset.card_sdiff`, `card_image_of_injective`

## Notes

The equality case of Cauchy-Davenport (Vosper) is a standard result but delicate
to formalize due to Finset cardinality arithmetic and the need to track the exact
common difference d across inductive steps.
