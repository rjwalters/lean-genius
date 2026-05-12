# Problem: Exact count of square roots of unity in (ℤ/nℤ)ˣ

## Statement

### Plain Language

The parent proof `gauss-wilson-non-cyclic`
(`Proofs/GaussWilsonNonCyclic.lean`, 323 lines, 0 axioms) establishes
the **lower-bound direction**: for `n ≥ 3` with `(ℤ/nℤ)ˣ` not cyclic,
the equation `x² = 1` in `ℤ/nℤ` has at least three solutions
(`card_sq_eq_one_ge_three`).

This OQ asks for the strictly stronger **exact-count** result via
the CRT construction:

> Can the CRT construction be generalized to give a formula for the
> number of square roots of unity in `(ℤ/nℤ)ˣ` for any `n`?

The answer is yes, and the formula is classical:

$$
\#\{x \in \mathbb{Z}/n\mathbb{Z} : x^2 = 1\} \;=\; 2^{\omega^{*}(n)},
$$

where `ω*(n)` counts the "independent ℤ/2 factors" in the 2-torsion
of `(ℤ/nℤ)ˣ`:

$$
\omega^{*}(n) \;=\; \omega_{\text{odd}}(n) \;+\; \varepsilon_2(n),
$$

with `ω_odd(n)` = number of distinct **odd** prime factors of `n` and

$$
\varepsilon_2(n) \;=\;
\begin{cases}
0 & \text{if } 2 \nmid n \text{ or } 2 \,\|\, n \\
1 & \text{if } 4 \,\|\, n \\
2 & \text{if } 8 \mid n
\end{cases}
$$

In particular:

| `n` | factorization | `ω_odd` | `ε₂` | predicted count | check |
|----:|:--------------|--------:|-----:|----------------:|:------|
| 1   | (unit)        | 0       | 0    | 1               | {1} |
| 2   | 2             | 0       | 0    | 1               | {1} |
| 3   | 3             | 1       | 0    | 2               | {1, 2} |
| 4   | 2²            | 0       | 1    | 2               | {1, 3} |
| 8   | 2³            | 0       | 2    | 4               | {1, 3, 5, 7} |
| 15  | 3·5           | 2       | 0    | 4               | {1, 4, 11, 14} |
| 16  | 2⁴            | 0       | 2    | 4               | {1, 7, 9, 15} |
| 24  | 2³·3          | 1       | 2    | 8               | {1, 5, 7, 11, 13, 17, 19, 23} |
| 105 | 3·5·7         | 3       | 0    | 8               | (8 sqrts) |

### Formal Statement

Two natural Lean 4 targets:

**Counted form** (existence of formula):

```lean
-- The number of square roots of 1 modulo n
noncomputable def numSqrtsOne (n : ℕ) : ℕ :=
  2 ^ (n.factorization.support.filter (· ≠ 2)).card *
    (if n % 4 = 0 then if n % 8 = 0 then 4 else 2 else 1)

theorem card_sqrts_one (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun x : ZMod n => x ^ 2 = 1)).card = numSqrtsOne n := by sorry
```

**Structural form** (2-torsion of `(ℤ/nℤ)ˣ`):

```lean
-- Equivalent statement via the unit group structure
theorem two_torsion_card (n : ℕ) [NeZero n] :
    Nat.card {u : (ZMod n)ˣ // u ^ 2 = 1} = numSqrtsOne n := by sorry
```

Both formulations should be provable; the second is more conceptual
and connects directly to Mathlib's unit-group infrastructure.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - number-theory
  - group-theory
  - cyclic-groups
  - zmod
  - wilson-gauss
  - mathlib-coverage
```

**Significance**: 6/10 — The exact-count formula is classical
(folklore at least since Gauss's *Disquisitiones*, 1801) and provides
a tight quantitative complement to the parent file's `≥ 3` lower
bound. It's a natural target for completion of the Gauss-Wilson
generalization in the gallery.

**Tractability**: 6/10 — All ingredients are in Mathlib at the
pinned revision: `ZMod.chineseRemainder`, the cyclic structure of
`(ZMod p^k)ˣ` for odd `p` (`ZMod.unitsCyclic`), and the explicit
description of `(ZMod 2^k)ˣ` for `k ≤ 3` and the well-known
`ZMod 2 × ZMod 2^{k-2}` decomposition for `k ≥ 3`. The proof
strategy is a straightforward induction on the number of prime
factors using CRT.

## Why This Matters

1. **Gauss-Wilson completion**: The parent's `card_sq_eq_one_ge_three`
   gives a *qualitative* lower bound (3) for the non-cyclic case.
   OQ-03 upgrades to the *quantitative* exact count for every `n`,
   making the gallery's coverage of the Gauss-Wilson generalization
   complete.

2. **CRT pedagogical example**: The proof is a textbook application
   of the Chinese Remainder Theorem, with one subtle complication
   (the power-of-2 case `(ZMod 2^k)ˣ` is non-cyclic for `k ≥ 3`).
   It would be the cleanest CRT specialization in the gallery.

3. **Connects to character theory**: `numSqrtsOne n` is exactly the
   number of real Dirichlet characters mod `n`, since real characters
   correspond to homomorphisms `(ℤ/nℤ)ˣ → {±1}`, i.e., to elements
   of `Hom((ℤ/nℤ)ˣ, ℤ/2ℤ) ≅` (the 2-torsion of `(ℤ/nℤ)ˣ`)*.
   This is the same count by Pontryagin duality.

4. **Quadratic-residue companion**: `numSqrtsOne` × (the count of
   quadratic residues) = `φ(n)`. Combined with Mathlib's
   `ZMod.card_zpowers` family, OQ-03 closes a small but visible
   gap in the Mathlib coverage of `(ℤ/nℤ)ˣ`.

## Theoretical Path

### CRT decomposition

For `n = p_1^{a_1} · p_2^{a_2} · ... · p_k^{a_k}` (prime factorization),
the CRT gives a ring isomorphism

$$
\mathbb{Z}/n\mathbb{Z} \;\cong\; \prod_{i=1}^{k} \mathbb{Z}/p_i^{a_i}\mathbb{Z}
$$

The square roots of `1` in a product are coordinate-wise square roots
of `1` in each factor. So

$$
\#\sqrt{1}_n \;=\; \prod_{i=1}^{k} \#\sqrt{1}_{p_i^{a_i}}
$$

### Prime-power counts

For odd prime `p`, `(ℤ/p^k ℤ)ˣ` is cyclic of order
`p^{k-1}(p-1)`. A cyclic group of even order has exactly **2**
square roots of `1` (namely `1` and the generator-squared-half).

For `p = 2`:

- `k = 0`: `(ℤ/1ℤ)ˣ` trivial → 1 root.
- `k = 1`: `(ℤ/2ℤ)ˣ` trivial → 1 root.
- `k = 2`: `(ℤ/4ℤ)ˣ ≅ ℤ/2ℤ` → 2 roots (1, 3).
- `k ≥ 3`: `(ℤ/2^k ℤ)ˣ ≅ ℤ/2 × ℤ/2^{k-2}` → 4 roots
  (namely `1, -1, 2^{k-1} + 1, 2^{k-1} - 1`).

### Assembling the formula

Combining: if `n = 2^a · m` with `m` odd having `ω_odd(n)` distinct
odd prime factors, then

$$
\#\sqrt{1}_n \;=\; \#\sqrt{1}_{2^a} \cdot \prod_{p \mid m \text{ odd}} 2 \;=\; \#\sqrt{1}_{2^a} \cdot 2^{\omega_{\text{odd}}(n)}.
$$

With `#√1_{2^a} ∈ {1, 1, 2, 4, 4, ...}` for `a = 0, 1, 2, 3, 4, ...`,
this gives the closed formula in the Plain Language section.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `gauss-wilson-non-cyclic` (parent) | Lower bound `≥ 3` for non-cyclic `(ℤ/nℤ)ˣ`; OQ-03 upgrades to exact count |
| `gauss-wilson-non-cyclic-oq-01` (sibling) | A different OQ on the same parent |
| `wilson-theorem` | Classical case `n = p` (prime): `(p-1)! ≡ -1 (mod p)` |
| `chinese-remainder-theorem` | The CRT proof that underlies the construction |
| `fermat-little-theorem` | `(ℤ/pℤ)ˣ` cyclic of order `p-1`, the base case for the prime-power analysis |

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4) | Module |
|------|----------------------|--------|
| Chinese Remainder Theorem (rings) | `ZMod.chineseRemainder` | `Mathlib.Data.ZMod.Basic` |
| `(ℤ/p^k ℤ)ˣ` cyclic for odd `p` | `ZMod.isCyclic_units_of_prime_pow` (and friends) | `Mathlib.RingTheory.ZMod.UnitsCyclic` |
| `(ℤ/2^k ℤ)ˣ` structure for `k ≥ 3` | `ZMod.unitsTwoPow_iso_zmodTwo_prod` (or its current name) | `Mathlib.RingTheory.ZMod.UnitsCyclic` |
| Number of solutions to `x^2 = 1` in cyclic groups | `Nat.card` calculations via `IsCyclic.card_zpowers` | `Mathlib.GroupTheory.SpecificGroups.Cyclic` |
| `Nat.factorization` | `Nat.factorization`, `Nat.factorization.support` | `Mathlib.NumberTheory.Padics.PadicVal` |
| `(ZMod n)ˣ` is finite | `Fintype.ofFinite`, `ZMod.fintype` | `Mathlib.Data.ZMod.Basic` |

**Caveat**: The parent file already exhibits CRT (`exists_third_sqrt_coprime`)
and the `(ZMod 2^k)ˣ` construction (`exists_third_sqrt_pow2`) at the
*existence* level; the OQ-03 work is to upgrade these from "at least
one extra solution" to "exact count of solutions".

## Suggested Next-Action Decomposition

This is **OBSERVE** phase. No Lean changes yet — only a survey and a
concrete decomposition into S2..S5 sessions.

1. **S2: Define `numSqrtsOne n` and prove small-cases.** Create
   `proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` with the definition
   (using `Nat.factorization` + power-of-2 case split) and prove
   the table values for `n ∈ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 15, 16, 24}`
   via `decide` / `rfl` against `Finset.card`. ~80 lines.

2. **S3: Prime-power case.** Prove `card_sqrts_one_prime_pow` for
   odd primes (using `ZMod.unitsCyclic` + the 2-torsion of cyclic
   groups of even order) and `card_sqrts_one_two_pow` for the four
   `(ZMod 2^k)ˣ` regimes. ~100 lines.

3. **S4: CRT multiplicativity.** Prove
   `card_sqrts_one_coprime_mul : Coprime a b → card_sqrts_one (a*b)
   = card_sqrts_one a * card_sqrts_one b` via `ZMod.chineseRemainder`.
   ~50 lines.

4. **S5: Full formula assembly.** Combine S3 + S4 into the
   main theorem `card_sqrts_one : ∀ n ≥ 1, ... = numSqrtsOne n`
   by induction on `n.factorization.support`. ~40 lines.

## Risk Notes

- **Power-of-2 case is the only subtlety.** All other primes contribute
  a factor of 2 (cyclic-group, even-order argument). The `2^k` case
  bifurcates at `k ∈ {0, 1, 2, ≥3}` and the parent file already
  handles `k ≥ 3` constructively for the existence direction; OQ-03
  needs to prove "exactly 4, no more".

- **Mathlib `Nat.factorization` quirks**: `n.factorization 2` may need
  `[NeZero n]` to be well-behaved; the parent file uses
  `Nat.ordProj_mul_ordCompl_eq_self` which is a related but distinct
  API. Pick one and stay consistent.

- **No axioms expected**: all infrastructure is `verified` in
  Mathlib; OQ-03 stays in the `verified` track.

- **Docker build cost**: a fresh build with full Mathlib imports
  (`Mathlib.Data.ZMod.Basic` + `Mathlib.NumberTheory.Padics.PadicVal`)
  is ~45 min in this worktree per the broken `.lake` symlink. Plan
  accordingly; the SCAFFOLD itself is text-only and incurs no build.
