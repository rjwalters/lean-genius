# Problem: Finite Factorial Telescoping Sum

**Slug**: factorial-telescoping-sum-oq-02
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Prove the finite closed form

$$
\sum_{k=1}^{n} \frac{k}{(k+1)!} \;=\; 1 - \frac{1}{(n+1)!} \qquad (n \ge 0),
$$

where the $n = 0$ case is the empty sum $0 = 1 - 1/1! = 0$. Establish it axiom-free by
induction on $n$, using the exact telescoping identity

$$
\frac{k}{(k+1)!} \;=\; \frac{1}{k!} - \frac{1}{(k+1)!}.
$$

### Plain Language

Add up $\tfrac{1}{2!} + \tfrac{2}{3!} + \tfrac{3}{4!} + \dots + \tfrac{n}{(n+1)!}$. Each
term is exactly the gap between two consecutive reciprocal factorials, $\tfrac{1}{k!} -
\tfrac{1}{(k+1)!}$, so the whole sum telescopes and collapses to $1 - \tfrac{1}{(n+1)!}$.
As $n \to \infty$ the leftover $1/(n+1)!$ vanishes, which is exactly why the infinite
series equals $1$.

### Why This Matters

This is the *finite* partial-sum identity that underlies the sibling entry
`factorial-telescoping-sum-oq-01-oq-01`, which proves the convergent series
$\sum_{k\ge 1} k/(k+1)! = 1$. That convergence result is cleanest when it rests on an
explicit finite closed form plus a vanishing tail; formalizing the finite identity here
turns the limit argument into a one-line `1/(n+1)! → 0` step and makes the telescoping
lemma reusable. It complements the parent `factorial-telescoping-sum-oq-01`
($\sum k\cdot k! = (n+1)! - 1$), giving the "reciprocal" companion of that integer identity.

## Known Results

### What's Already Proven

- $\sum_{k=1}^n k\cdot k! = (n+1)! - 1$ — parent `factorial-telescoping-sum-oq-01`.
- $\sum_{k\ge 1} k/(k+1)! = 1$ (infinite series) — sibling
  `factorial-telescoping-sum-oq-01-oq-01`.

### What's Still Open (for this entry)

- The explicit finite partial sum $\sum_{k=1}^n k/(k+1)! = 1 - 1/(n+1)!$ as a standalone,
  reusable identity over $\mathbb{Q}$.

### Our Goal

Formalize the finite identity over $\mathbb{Q}$ by induction. Base $n = 0$: empty sum
$= 0 = 1 - 1/1!$. Step: with `Finset.sum_range_succ`, reduce to
$\bigl(1 - \tfrac{1}{(n+1)!}\bigr) + \tfrac{n+1}{(n+2)!} = 1 - \tfrac{1}{(n+2)!}$, i.e.
$\tfrac{n+1}{(n+2)!} = \tfrac{1}{(n+1)!} - \tfrac{1}{(n+2)!}$, closed by
`Nat.factorial_succ` + `field_simp` + `ring`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| factorial-telescoping-sum-oq-01 | parent: $\sum k\cdot k! = (n+1)!-1$ | induction, telescoping |
| factorial-telescoping-sum-oq-01-oq-01 | sibling: infinite series $=1$ | tsum, tail bound |
| geometric-series / arithmetic-series | ambient finite-sum machinery | `Finset.sum`, induction |

## Initial Thoughts

### Potential Approaches

1. **Termwise telescoping then `Finset.sum_range_succ_comm`**: rewrite each term as
   $\tfrac{1}{k!} - \tfrac{1}{(k+1)!}$ and apply the telescoping-sum lemma
   (`Finset.sum_range_sub'` or manual induction).
   - Why it might work: the summand is *exactly* a difference of consecutive terms — the
     textbook telescoping shape.
   - Risk: index bookkeeping (`range n` vs `Icc 1 n`); factorial-of-succ rewriting.

2. **Direct induction with `field_simp`**: induct on `n`, peel the top term with
   `Finset.sum_range_succ`, and discharge the rational step with
   `simp [Nat.factorial_succ]; field_simp; ring`.
   - Why it might work: mirrors how the sibling finite identities are formalized.

### Key Difficulties

- Casting `Nat.factorial` into `ℚ` and keeping `(k+1)! = (k+1)·k!` available as a rewrite.
- Nonzero-denominator side goals for `field_simp` (all factorials are positive — discharge
  with `Nat.factorial_pos` / `Nat.cast_ne_zero`).

### What Would a Proof Need?

- `Finset.sum_range_succ`, `Nat.factorial_succ`, `Nat.factorial_pos`.
- `field_simp` + `ring` for the per-step rational identity.
- (Optional, for the telescoping route) `Finset.sum_range_sub'`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Pure telescoping; the summand is a literal difference of consecutive reciprocal
  factorials, so `ring` closes each step.
- Sibling infinite-series entry already builds all needed factorial-cast machinery.

**Estimated Effort**:
- Exploration: minutes–hours
- If tractable: <1 day

## References

### Mathlib
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_range_succ`, `Finset.sum_range_sub'`.
- `Mathlib.Data.Nat.Factorial.Basic` — `Nat.factorial_succ`, `Nat.factorial_pos`.
- `Mathlib.Tactic.FieldSimp` / `Mathlib.Tactic.Ring`.

### Online Resources
- Telescoping series (standard references) — reciprocal-factorial example.
- Series for $e$: $\sum 1/k! = e$, of which this is a telescoping cousin.

## Metadata

```yaml
tags:
  - number-theory
  - factorials
  - telescoping
  - finite-sums
  - induction
related_proofs:
  - factorial-telescoping-sum-oq-01
  - factorial-telescoping-sum-oq-01-oq-01
difficulty: low
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 8/10
