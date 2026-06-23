# Problem: Telescoping Partial Alternating Binomial Sums

**Slug**: combinations-formula-oq-05-oq-01
**Created**: 2026-06-23
**Status**: Active
**Source**: gallery-gap <!-- open question of verified parent combinations-formula-oq-05 (full alternating-row cancellation) -->

## Problem Statement

### Formal Statement

$$
\sum_{k=0}^{j} (-1)^k \binom{n}{k} \;=\; (-1)^j \binom{n-1}{j}, \qquad 0 \le j \le n .
$$

The parent entry establishes the *full-row* cancellation $\sum_{k=0}^{n} (-1)^k \binom{n}{k} = 0$ (for $n \ge 1$). This open question refines that vanishing into the **partial-sum** identity above: the alternating sum truncated at index $j$ collapses to a single signed binomial coefficient $(-1)^j\binom{n-1}{j}$. Setting $j = n$ recovers the parent (since $\binom{n-1}{n}=0$).

### Plain Language

If you walk along a row of Pascal's triangle and add the entries with alternating signs ($+,-,+,-,\dots$), the *whole* row cancels to zero. But what does the running total look like before you reach the end? The answer is surprisingly clean: after $j$ steps the partial total is exactly $\pm$ one entry of the row *above* — namely $(-1)^j\binom{n-1}{j}$. This problem asks to formalize that exact running-total formula in Lean, turning the "everything cancels" fact into a precise telescoping statement.

### Why This Matters

The partial-sum form is strictly more informative than the parent's full cancellation: it gives the exact value at every truncation point, exposes the identity as a telescoping consequence of Pascal's rule $\binom{n}{k} = \binom{n-1}{k} + \binom{n-1}{k-1}$, and is the discrete analogue of an antiderivative. It is a standard ingredient in inclusion–exclusion remainder bounds and in proofs of binomial transform inversion. Formalizing it exercises `Finset.sum_range_succ`, induction over the truncation index, and sign-bookkeeping with `(-1)^k` — a clean, reusable lemma for the gallery's combinatorics corpus.

## Known Results

### What's Already Proven

- Full alternating-row identity $\sum_{k=0}^{n} (-1)^k \binom{n}{k} = 0$ — gallery entry `combinations-formula-oq-05` and Mathlib `Int.alternating_sum_range_choose`.
- Pascal's rule `Nat.succ_sub_one`, `Nat.choose_succ_succ` (`Nat.choose_succ_succ : (n+1).choose (k+1) = n.choose k + n.choose (k+1)`) — Mathlib.
- `Finset.sum_range_succ`, `Finset.sum_range_succ_comm`, and alternating-sum helpers — Mathlib `Mathlib.Algebra.BigOperators`.

### What's Still Open (here)

- The truncated identity $\sum_{k=0}^{j} (-1)^k \binom{n}{k} = (-1)^j \binom{n-1}{j}$ as a top-level theorem (over $\mathbb{Z}$, with the natural-number subtraction handled carefully when $n=0$).
- A clean statement of the underlying telescoping step $(-1)^j\binom{n-1}{j} - (-1)^{j-1}\binom{n-1}{j-1} = (-1)^j\binom{n}{j}$.

### Our Goal

Deliver the partial-sum identity as a verified, 0-axiom theorem over $\mathbb{Z}$, proved by induction on $j$ using Pascal's rule, and re-derive the parent's full cancellation as a one-line corollary ($j=n$). Provide the telescoping step as a named lemma so downstream inversion/inclusion–exclusion entries can reuse it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-05 | direct parent (full alternating-row cancellation) | `Int.alternating_sum_range_choose`, `Finset.sum` |
| combinations-formula | base binomial-coefficient API | `Nat.choose`, Pascal's rule |
| combinations-formula-oq-09 | sibling moment/peel-then-absorb identities | induction on a parameter, `Finset.sum_range_succ` |

## Initial Thoughts

### Potential Approaches

1. **Induction on the truncation index `j`** (primary): Base $j=0$ gives $\binom{n}{0}=1=(-1)^0\binom{n-1}{0}$. Step uses `Finset.sum_range_succ` plus Pascal's rule to show the increment $(-1)^{j+1}\binom{n}{j+1}$ telescopes with the IH $(-1)^j\binom{n-1}{j}$ into $(-1)^{j+1}\binom{n-1}{j+1}$.
   - Why it might work: Pascal's rule is *exactly* the algebraic identity the telescoping needs; Mathlib has it directly.
   - Risk: sign management with `(-1)^k` and casting $\binom{}{}$ from $\mathbb{N}$ to $\mathbb{Z}$; resolved by working in $\mathbb{Z}$ throughout and using `push_cast`.

2. **Telescoping via `Finset.sum_range_succ_sub`** (alternative): write each summand as a difference of consecutive $(-1)^k\binom{n-1}{k}$ terms and apply a telescoping-sum lemma.
   - Why it might work: avoids explicit induction bookkeeping.
   - Risk: requires phrasing the summand as an exact first difference; the edge term at $k=0$ needs care.

### Key Difficulties

- Natural-number subtraction: $\binom{n-1}{j}$ is ill-behaved at $n=0$; state over $n \ge 1$ or define via `Int` and handle $n=0$ separately.
- Sign tracking through the inductive step (`pow_succ`, `neg_one_pow` lemmas).

### What Would a Proof Need?

- Key lemma 1: the one-step telescoping identity $(-1)^{j+1}\binom{n}{j+1} = (-1)^{j+1}\binom{n-1}{j+1} - (-1)^{j}\binom{n-1}{j}$ from Pascal's rule.
- Key lemma 2: `Finset.sum_range_succ` to expose the last term.
- Technical requirements: `push_cast`, `ring`/`linarith` for the sign algebra, `Nat.choose_succ_succ`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The identity is a textbook telescoping consequence of Pascal's rule; the only Lean friction is sign/cast bookkeeping.
- Numerous sibling gallery entries (combinations-formula-oq-09, -oq-06) ship analogous induction-on-a-parameter proofs.
- Mathlib provides every needed primitive (`Nat.choose_succ_succ`, `Finset.sum_range_succ`, `Int.alternating_sum_range_choose`).

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: half a day to a day

## References

### Papers
- Concrete Mathematics (Graham, Knuth, Patashnik), §5.1 — partial sums of alternating binomial coefficients.

### Online Resources
- The "hockey-stick" and alternating partial-sum identities are standard; see any treatment of the binomial transform.

### Mathlib
- `Mathlib.Combinatorics.Choose.Sum` — `Int.alternating_sum_range_choose` and related alternating sums.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum_range_succ`.
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose_succ_succ` (Pascal's rule).

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - alternating-sum
  - telescoping
  - finset-sums
related_proofs:
  - combinations-formula-oq-05
  - combinations-formula
difficulty: low
source: gallery-gap
created: 2026-06-23
```
