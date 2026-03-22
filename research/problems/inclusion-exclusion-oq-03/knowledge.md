# Knowledge Base: Efficient Inclusion-Exclusion Computation

## Session 2026-03-22 (researcher-2) - Initial Formalization

**Mode**: FRESH
**Outcome**: progress — created InclusionExclusionOQ03.lean (209L, 0 axioms, 4 sorries)

### Architecture
Formalizes the algebraic structure behind inclusion-exclusion: the Möbius algebra
of the Boolean lattice 2^[n].

| Component | Type | Status |
|-----------|------|--------|
| `zetaTransform` | def | (ζf)(S) = ∑_{T⊆S} f(T) |
| `mobiusTransform` | def | (μg)(S) = ∑_{T⊆S} (-1)^|S\T| g(T) |
| `zetaStep` | def | Single-element DP step for O(n·2^n) |
| `zetaTransform_empty` | theorem | PROVED |
| `zetaTransform_singleton` | theorem | PROVED |
| `mobiusTransform_empty` | theorem | PROVED |
| `zetaStep_not_mem/mem` | theorem | PROVED |
| `signed_sum_subsets` | theorem | sorry (key cancellation) |
| `mobius_inverts_zeta` | theorem | sorry (depends on signed_sum_subsets) |
| `mobius_subset_lattice` | theorem | sorry |
| `odd_even_subset_balance` | theorem | sorry |

### Key Insight
The signed_sum_subsets lemma (∑_{T⊆S} (-1)^|S\T| = [S=∅]) is the
atomic fact underlying everything. It can be proved by:
1. Fix a ∈ S. Map T ↦ T △ {a} (symmetric difference).
2. This is an involution on subsets of S.
3. If a ∈ T: |S\T| changes by -1. If a ∉ T: |S\T| changes by +1.
4. So (-1)^|S\T| and (-1)^|S\(T△{a})| have opposite signs.
5. Terms cancel in pairs → total = 0.
