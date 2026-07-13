# Problem: Simplex Ehrhart Polynomial — Axiom-Free Proof via Multiset Bijection

**Slug**: ehrhart-cube-proven-oq-01
**Created**: 2026-05-06T16:07:08+03:00
**Updated**: 2026-05-06
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
L(\Delta^d, n) = \left|\{(a_1,\ldots,a_d) \in \mathbb{Z}_{\geq 0}^d : a_1 + \cdots + a_d \leq n\}\right| = \binom{n+d}{d}
$$

In Lean 4, the target theorem is:

```lean
theorem simplex_lattice_count (d n : ℕ) :
    Fintype.card (Sym (Fin (d + 1)) n) = Nat.choose (n + d) d
```

or equivalently, as a direct cardinality count:

```lean
theorem simplex_lattice_count' (d n : ℕ) :
    Fintype.card {f : Fin d →₀ ℕ // f.sum (fun _ k => k) ≤ n} = Nat.choose (n + d) d
```

### Plain Language

The standard $d$-dimensional simplex $\Delta^d$ is the convex hull of the $d+1$ standard basis vectors — the "simplest" polytope in each dimension. When dilated by $n$, its lattice points are all non-negative integer tuples $(a_1, \ldots, a_d)$ with $a_1 + \cdots + a_d \leq n$.

**Question**: Can we prove axiom-free (no `sorry`, no `axiom`) that this count equals $\binom{n+d}{d}$ using a type-theoretic bijection, mirroring how `EhrhartCubeProven.lean` proved the cube formula $(n+1)^d$ via `Fintype.card_fun`?

### Why This Matters

The cube proof (`EhrhartCubeProven.lean`) used the bijection `Fin d → Fin (n+1)` + `Fintype.card_fun`. The simplex case is the natural companion:

- **Mathematical symmetry**: Together, cube and simplex cover the two most fundamental polytopes. The cube uses function types; the simplex uses multiset types.
- **Demonstrates a principle**: When a polytope has an explicit, elementary formula, the general Ehrhart existence theorem is unnecessary. Proving this for the simplex reinforces the principle.
- **Proof technique exposure**: The bijection `(lattice points of n·Δᵈ) ↔ Sym (Fin (d+1)) n` illustrates the power of Lean's symmetric group types.
- **Gallery extension**: Completes the Ehrhart collection (cube + simplex = the two canonical families of lattice polytopes).

## Known Results

### What's Already Proven

- `cube_lattice_count`: $|n \cdot [0,1]^d \cap \mathbb{Z}^d| = (n+1)^d$ — proved axiom-free via `Fintype.card_fun` in `EhrhartCubeProven.lean` (proofs/Proofs/EhrhartCubeProven.lean)
- `Sym.card` (Mathlib): `Fintype.card (Sym α n) = Nat.choose (Fintype.card α + n - 1) n`
- `Fintype.card_fin`: `Fintype.card (Fin n) = n`
- Stars-and-bars: Non-negative integer solutions to $a_1 + \cdots + a_k = n$ is $\binom{n+k-1}{k-1}$

### What's Still Open

- No axiom-free Lean proof that `Fintype.card (Sym (Fin (d+1)) n) = Nat.choose (n+d) d`
- No verified bijection between "lattice points of n·Δᵈ" (as a Lean type) and `Sym (Fin (d+1)) n`
- The arithmetic identity `Nat.choose (d+1+n-1) n = Nat.choose (n+d) d` needs to be massaged into the right form

### Our Goal

Prove `Fintype.card (Sym (Fin (d + 1)) n) = Nat.choose (n + d) d` without any `sorry` or `axiom`, using:
1. Mathlib's `Sym.card` or `Fintype.card_sym`
2. `Fintype.card_fin` for `Fintype.card (Fin (d+1)) = d+1`
3. Arithmetic simplification: `Nat.choose (d+1+n-1) n = Nat.choose (n+d) n = Nat.choose (n+d) d`

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `ehrhart-cube-proven` | Direct parent; cube case uses same philosophy | `Fintype.card_fun`, function types |
| `ehrhart-polynomial-oq-03` | Axiomatizes general Ehrhart theory we're avoiding | `axiom ehrhartPoly` |
| `picks-theorem-oq-03` | Pick's theorem; simplex proof implies Pick for triangles | Ehrhart specialization |

## Initial Thoughts

### Potential Approaches

1. **Direct `Sym.card` approach** (most promising):
   - Use `Fintype.card (Sym (Fin (d+1)) n)` as the primary type
   - Apply `Sym.card`: gives `Nat.choose (d+1+n-1) n = Nat.choose (n+d) n`
   - Use `Nat.choose_symm_diff` or `Nat.choose_comm` to convert `Nat.choose (n+d) n` to `Nat.choose (n+d) d`
   - Risk: arithmetic API in Lean for choose may be messy; `d+1+n-1 = n+d` may need `omega`

2. **Stars-and-bars via `Finset.Nat.antidiagonalSubset`**:
   - Use `Finset.Nat.antidiagonalSubset` or `Finset.Nat.weakCompositions`
   - More explicit but requires more plumbing
   - Risk: API may not be complete in Mathlib 4.26

3. **Finsupp approach** (most direct mathematically):
   - Type: `{f : Fin d →₀ ℕ // f.sum (fun _ k => k) ≤ n}`
   - Show bijection with `Sym (Fin (d+1)) n`
   - Risk: Finsupp bijection is non-trivial to formalize

### Key Difficulties

- **Arithmetic off-by-one**: `Sym.card` gives `Nat.choose (Fintype.card α + n - 1) n` — with `α = Fin (d+1)`, this is `Nat.choose (d+1+n-1) n = Nat.choose (n+d) n`. Need to show `Nat.choose (n+d) n = Nat.choose (n+d) d`.
- **Natural number subtraction**: `d+1+n-1` may expand to `d+n` via omega when types are ℕ, avoiding truncation issues.
- **Which type is the "right" Lean formalization**: `Sym (Fin (d+1)) n` vs `{f : Fin d →₀ ℕ // ...}` — the former has better Mathlib support.

### What Would a Proof Need?

- `Sym.card` or `Fintype.card_sym` (already in Mathlib)
- `Fintype.card_fin` (already in Mathlib)
- Arithmetic: `d + 1 + n - 1 = n + d` (omega)
- `Nat.choose_symm` or `Nat.choose_comm`: `Nat.choose n k = Nat.choose n (n-k)`

## Tractability Assessment

**Difficulty**: Low (tractability 7/10)

**Justification**:
- `Sym.card` is already in Mathlib; the proof reduces to applying it correctly
- The main challenge is arithmetic normalization of choose indices (solvable with omega/norm_num)
- Similar to `cube_lattice_count` which was proved in one line via `simp [Fintype.card_fun]`
- `simplex_lattice_count` may be a 3-5 line proof

**Estimated Effort**:
- Exploration: 1-2 hours (find the right Mathlib API)
- If tractable: 1-2 days (write and verify the proof file)
- Concrete deliverable: A new file `proofs/Proofs/EhrhartSimplexProven.lean`

## References

### Papers
- Beck, M. and Robins, S. (2007). *Computing the Continuous Discretely*. Springer. — Chapter 3 covers simplex Ehrhart polynomial and bijection with multisets.
- Ehrhart, E. (1962). *Sur les polyèdres rationnels homothétiques à n dimensions*. C.R. Acad. Sci. Paris.

### Mathlib
- `Mathlib.Data.Sym.Card` — `Sym.card` theorem
- `Mathlib.Data.Fintype.Card` — `Fintype.card_fin`
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose_symm`, `Nat.choose_comm`
- `Mathlib.Data.Finsupp.Basic` — Finsupp type for weighted compositions

### Key Lean Lemmas to Find
```lean
-- From Mathlib:
Sym.card : Fintype.card (Sym α n) = Nat.choose (Fintype.card α + n - 1) n
Fintype.card_fin : Fintype.card (Fin n) = n
Nat.choose_symm_diff : Nat.choose n k = Nat.choose n (n - k)  -- or similar
```

## Metadata

```yaml
tags:
  - combinatorics
  - ehrhart-theory
  - polytopes
  - lattice-points
  - simplex
  - multisets
  - axiom-elimination
related_proofs:
  - ehrhart-cube-proven
  - ehrhart-polynomial-oq-03
  - picks-theorem-oq-03
difficulty: low
source: proof-suggestion
created: 2026-05-06T16:07:08+03:00
```

**Significance**: 6/10
**Tractability**: 7/10
