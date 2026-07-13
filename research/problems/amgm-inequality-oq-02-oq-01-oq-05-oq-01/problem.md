# Problem: Next Maclaurin Rung — S₂² ≥ S₁S₃ (Newton's Inequality)

**Slug**: amgm-inequality-oq-02-oq-01-oq-05-oq-01
**Created**: 2026-07-04T06:28:11-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For nonnegative reals $x_1,\dots,x_n$, let $e_k$ be the $k$-th elementary symmetric
polynomial and $S_k = e_k / \binom{n}{k}$ the $k$-th Maclaurin average. Prove the second
rung of the Maclaurin / Newton chain:

$$
S_2^{\,2} \ge S_1 S_3 \qquad (n \ge 3).
$$

Equivalently, in the un-averaged **Newton** form — the cleaner statement to formalize
because it avoids denominators — this is the $k=2$ instance of Newton's inequality

$$
e_{k-1}\,e_{k+1} \;\le\; \frac{k}{k+1}\cdot\frac{n-k+1}{n-k}\;e_k^{\,2},
$$

whose $k=2$ case reads $e_1 e_3 \le \tfrac{2(n-1)}{3(n-2)}\,e_2^2$. The exact constant
must be re-derived and pinned down during OBSERVE; the target is that $S_2^2 \ge S_1 S_3$
holds, i.e. the normalized means $S_k$ are log-concave at $k=2$.

### Plain Language

The parent entry proved the **first** Maclaurin rung $S_1^2 \ge S_2$ and observed it is
"Cauchy–Schwarz in disguise" — carrying no inequality content beyond it. This problem is
the **next** rung $S_2^2 \ge S_1 S_3$, the first genuinely harder step: it is **Newton's
inequality**, expressing log-concavity of the elementary symmetric means.

### Why This Matters

This is the first rung of the Maclaurin chain that requires more than Cauchy–Schwarz — it
is where the real content of Newton's inequalities begins. Formalizing it extends the
gallery's Maclaurin/AM–GM line from a Cauchy–Schwarz corollary into genuine log-concavity,
a concrete step toward a full formal proof of the Maclaurin chain
$S_1 \ge \sqrt{S_2} \ge \sqrt[3]{S_3} \ge \cdots$ refining AM–GM.

## Known Results

### What's Already Proven

- **Parent `amgm-inequality-oq-02-oq-01-oq-05`**: first rung $S_1^2 \ge S_2$, via
  Newton–Girard $e_1^2 = p_2 + 2e_2$ + Cauchy–Schwarz $e_1^2 \le n\,p_2$.
- **`amgm-inequality-oq-02-oq-01`**: Newton–Girard square-of-sum identity and the
  diagonal/off-diagonal decomposition.
- **`amgm-inequality-oq-02-oq-01-oq-04`**: general arbitrary-$k$ Newton–Girard recurrence
  over a Finset/CommRing.
- Mathlib: `Mathlib.Algebra.Order.Chebyshev` (`sq_sum_le_card_mul_sum_sq`),
  `Nat.cast_choose_two`, `Finset.sum_mul_sum`, elementary symmetric polynomial API.

### What's Still Open

- Newton's inequality $S_2^2 \ge S_1 S_3$ (this problem), and the general rung
  $S_k^2 \ge S_{k-1} S_{k+1}$.

### Our Goal

Prove the $k=2$ Newton inequality $S_2^2 \ge S_1 S_3$ for nonnegative reals with $n \ge 3$
in Lean 4 / Mathlib. Establish the un-averaged polynomial inequality relating
$e_1, e_2, e_3$ first, then pass to the averaged $S$-form by clearing the binomial
denominators (as the parent did for rung 1).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality-oq-02-oq-01-oq-05 | Direct parent; rung 1 S₁²≥S₂ | Newton–Girard + Cauchy–Schwarz, `nlinarith`, `div_le_div_iff₀` |
| amgm-inequality-oq-02-oq-01 | Newton–Girard identity e₁²=p₂+2e₂ | trichotomy split, `Finset.sum_comm` |
| amgm-inequality-oq-02-oq-01-oq-04 | General-k Newton–Girard recurrence | `Finset` induction over CommRing |

## Initial Thoughts

### Potential Approaches

1. **Direct SOS over the $x_i$** (recommended): expand the cleared difference
   $c_1 e_2^2 - c_2 e_1 e_3$ (with $c_1,c_2$ the correct binomial constants) and exhibit it
   as a nonnegative combination. For $k=2$ the difference has a known Schur-/SOS-type
   certificate; `nlinarith`/`polyrith` with `sq_nonneg (x i - x j)` hints may discharge the
   cleared polynomial inequality once the constant is fixed.
2. **Real-rootedness / Rolle route**: Newton's inequality classically follows because
   $\prod(x+x_i)$ is real-rooted ⇒ so are its derivatives ⇒ a quadratic slice has
   nonnegative discriminant. Mathematically clean but likely heavy to formalize.
3. **Newton-identities + `nlinarith`**: express everything in $e_1,e_2,e_3$ via the
   parent's Newton–Girard machinery, then reduce to an inequality `nlinarith` can close
   with supplied square witnesses.

### Key Difficulties

- **Pinning the exact constant** $\tfrac{2(n-1)}{3(n-2)}$ after converting the binomials —
  get this exactly right in OBSERVE before attempting Lean.
- Finding an explicit SOS certificate valid for all $n$ and all nonnegative $x_i$. Unlike
  rung 1, this genuinely uses the nonnegativity/real-rootedness at general $k$; for $k=2$
  check whether nonnegativity is truly required or (as in rung 1) partly avoidable.
- `nlinarith`/`polyrith` may time out on the $n$-fold symmetric expansion; a hand-built
  certificate over the elementary symmetric variables is likely needed.

### What Would a Proof Need?

- The cleared polynomial inequality relating $e_1, e_2, e_3$ with explicit integer coefficients.
- An SOS / Schur-type certificate (`nlinarith [sq_nonneg (x i - x j), ...]`).
- A `choose 3` cast lemma alongside `Nat.cast_choose_two` to reach the averaged form.
- Positivity of binomials for $n \ge 3$ to pass to the $S$-form (mirrors parent).

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The parent (rung 1) is ~124 lines but is "only" Cauchy–Schwarz; this rung is the first
  with genuine Newton's-inequality content, so expect materially more work.
- The $k=2$ case is the most-documented Newton inequality with known elementary SOS
  proofs, keeping it within reach of `nlinarith` + square hints — unlike the general $k$.
- Risk: if a clean SOS certificate over $e_i$ is elusive, the real-rootedness route is a
  significant formalization undertaking.

**Estimated Effort**:
- Exploration: 0.5–1 day (fix the constant; find an SOS certificate on paper)
- If tractable: 3–5 days
- If hard (needs real-rootedness of derivatives): unknown

## References

### Papers
- G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities*, 2nd ed., CUP, 1952 — Newton's and Maclaurin's inequalities (§2.22).
- C. Maclaurin (1729), original chain of symmetric-mean inequalities.

### Online Resources
- https://en.wikipedia.org/wiki/Newton%27s_inequalities
- https://en.wikipedia.org/wiki/Maclaurin%27s_inequality

### Mathlib
- `Mathlib.Algebra.Order.Chebyshev` — Cauchy–Schwarz / power-mean bounds.
- `Mathlib.RingTheory.MvPolynomial.Symmetric` / `MvPolynomial.esymm` — elementary symmetric polynomial API.
- `Mathlib.Data.Nat.Choose.Cast` — binomial casts to ℝ.

## Metadata

```yaml
tags:
  - analysis
  - inequalities
  - symmetric-polynomials
  - maclaurin
  - newton-inequality
  - log-concavity
related_proofs:
  - amgm-inequality-oq-02-oq-01-oq-05
  - amgm-inequality-oq-02-oq-01
difficulty: high
source: gallery-gap
created: 2026-07-04T06:28:11-07:00
```

**Significance**: 6/10
**Tractability**: 5/10
