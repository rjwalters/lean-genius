# Problem: Negative Pell x^2 - D y^2 = -1 Is Unsolvable When a Prime p = 3 (mod 4) Divides D

**Slug**: pell-equation-oq-08
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: pell-equation

## Problem Statement

### Formal Statement

$$
\text{If a prime } p \equiv 3 \pmod 4 \text{ divides } D, \text{ then } x^2 - D\,y^2 = -1 \text{ has no integer solution.}
$$

Equivalently, a solution of the negative Pell equation forces $-1$ to be a quadratic
residue modulo every divisor of $D$, but $-1$ is a nonresidue modulo any prime
$p \equiv 3 \pmod 4$.

### Plain Language

The classical Pell equation $x^2 - D y^2 = 1$ is always solvable (parent entry), but the
**negative** Pell equation $x^2 - D y^2 = -1$ is not always solvable. This child proves a
clean local obstruction: if $D$ has any prime factor $p \equiv 3 \pmod 4$, then no integer
solution exists. This immediately gives the elementary corollary $D \equiv 3 \pmod 4
\Rightarrow$ unsolvable, and it also catches cases the mod-4 test alone misses — e.g.
$D = 21 \equiv 1 \pmod 4$ is still unsolvable because $3 \mid 21$ — contrasted with the
solvable $D = 2$ (1,1) and $D = 5$ (2,1).

### Why This Matters

The parent gallery entry and its subtree treat solutions that **exist** (regulator, size
bounds, norm forms, recurrences, the $D=2$ negative case). None addresses *when the
negative Pell equation is unsolvable for general D* — a thread flagged by sibling oq-02.
Mathlib's `Pell` library only handles the norm-$+1$ equation, so no named result covers
this. The proof is a short reduction to `ZMod` quadratic-residue facts.

## Known Results

### What's Already Proven

- Parent `pell-equation` is verified (0-axiom).
- Mathlib has `ZMod.exists_sq_eq_neg_one_iff` and `ZMod.isSquare_neg_one_of_dvd`.

### What's Still Open

- The target theorems below (currently `sorry`).

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**specialization / obstruction**.

## Target Lean Sketch

```lean
open scoped Classical

/-- A negative-Pell solution makes `-1` a square mod `D`. -/
theorem negPell_isSquare_neg_one {D : ℕ}
    (h : ∃ x y : ℤ, x ^ 2 - (D : ℤ) * y ^ 2 = -1) :
    IsSquare (-1 : ZMod D) := by
  sorry -- push through Int.cast : ℤ → ZMod D; (D : ZMod D) = 0 via ZMod.natCast_self

/-- A prime factor `p ≡ 3 (mod 4)` obstructs solvability. -/
theorem negPell_no_sol_of_prime_factor {D p : ℕ}
    (hp : p.Prime) (hp3 : p % 4 = 3) (hpD : p ∣ D) :
    ¬ ∃ x y : ℤ, x ^ 2 - (D : ℤ) * y ^ 2 = -1 := by
  sorry -- descend IsSquare(-1) mod D to mod p, contradict exists_sq_eq_neg_one_iff
```

Plus the corollary `negPell_no_sol_of_three_mod_four (hD : D % 4 = 3)`, and worked
`example`s: solvable $D = 2, 5$; unsolvable $D = 3, 7, 21$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `pell-equation` | Parent: Pell's equation | continued fractions, fundamental solution |
| `pell-equation-oq-02` | Sibling: solvability questions | number theory |
| `fermat-two-squares` | Uses `-1` quadratic residue mod primes | quadratic residues |

## Tractability Assessment

**Difficulty**: Low-Medium

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: Three short lemmas — a cast/reduction (`push_cast` + `ZMod.natCast_self`),
one library descent lemma, and one library iff. No induction or `Solution₁` machinery. Main
risk is minor `Int.cast` bookkeeping.

### Suggested First Steps

1. Prove `negPell_isSquare_neg_one` by casting the equation into `ZMod D` (`push_cast`,
   `ZMod.natCast_self`) so `x^2 = -1`.
2. Descend to `ZMod p` via `ZMod.isSquare_neg_one_of_dvd hpD`, then contradict with
   `ZMod.exists_sq_eq_neg_one_iff.mp` given `p % 4 = 3` (needs `Fact p.Prime`).
3. Derive the `D ≡ 3 (mod 4)` corollary and add `norm_num` / `decide` worked examples.

## References

### Mathlib

- `ZMod.exists_sq_eq_neg_one_iff` — NumberTheory/LegendreSymbol/Basic.lean (`IsSquare (-1) ↔ p % 4 ≠ 3`)
- `ZMod.isSquare_neg_one_of_dvd` — NumberTheory/SumTwoSquares.lean (divisor descent)
- `ZMod.natCast_self`, `ZMod.intCast_zmod_eq_zero_iff_dvd` — Data/ZMod/Basic.lean
- `ZMod.isSquare_neg_one_iff'` — NumberTheory/SumTwoSquares.lean (squarefree full criterion, optional)

### Literature

- Continued fractions and the negative Pell equation; solvability criteria (e.g. via
  the class group / genus theory). The $p \equiv 3 \pmod 4$ obstruction is classical.

## Metadata

```yaml
tags:
  - number-theory
  - pell-equation
  - quadratic-residues
  - diophantine-equations
related_proofs:
  - pell-equation
  - pell-equation-oq-02
  - fermat-two-squares
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
