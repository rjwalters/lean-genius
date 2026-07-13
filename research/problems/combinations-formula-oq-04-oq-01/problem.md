# Problem: Ultra-Log-Concavity of a Pascal Row

**Slug**: combinations-formula-oq-04-oq-01
**Created**: 2026-07-01T22:11:22-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

The parent proved ordinary log-concavity of a Pascal row: $\binom{n}{k}^2 \ge \binom{n}{k-1}\binom{n}{k+1}$. We strengthen this to **ultra-log-concavity** (ULC). A finite nonnegative sequence $(a_k)_{0 \le k \le n}$ is ultra-log-concave of order $n$ iff the normalized sequence $a_k / \binom{n}{k}$ is log-concave, i.e.

$$
\left(\frac{a_k}{\binom{n}{k}}\right)^{2} \;\ge\; \frac{a_{k-1}}{\binom{n}{k-1}}\cdot\frac{a_{k+1}}{\binom{n}{k+1}}
\qquad (1 \le k \le n-1).
$$

The binomial row itself, $a_k = \binom{n}{k}$, is the extremal ULC sequence: after normalization $a_k/\binom{n}{k} = 1$, so its log-concavity is the *equality* case, and the substantive strengthening we formalize is the ULC inequality in its raw (denominator-cleared, $\mathbb{N}$-arithmetic) form,

$$
(k+1)\,(n-k+1)\;\binom{n}{k}^{2} \;\ge\; k\,(n-k)\;\binom{n}{k-1}\binom{n}{k+1}
\qquad (1 \le k \le n-1),
$$

equivalently the multiplicative-gap statement that $\binom{n}{k}^2 \ge \binom{n}{k-1}\binom{n}{k+1}\bigl(1+\tfrac1k\bigr)\bigl(1+\tfrac1{n-k}\bigr)$, which is strictly stronger than the parent's $\binom{n}{k}^2 \ge \binom{n}{k-1}\binom{n}{k+1}$.

### Plain Language

The parent result says each row of Pascal's triangle "bends downward" in the multiplicative sense: the square of any entry is at least the product of its two neighbours. Ultra-log-concavity says the row bends downward *by a definite margin* — after you divide each entry $\binom{n}{k}$ by the "reference" binomial $\binom{n}{k}$ (turning it into the flat sequence of $1$'s), the resulting sequence is still log-concave, and the amount of slack is exactly the factor $\bigl(1+\tfrac1k\bigr)\bigl(1+\tfrac1{n-k}\bigr) > 1$. In short: the binomial row is not merely log-concave, it is log-concave with room to spare, and the extra room is precisely quantified.

### Why This Matters

Ultra-log-concavity sits at the top of a hierarchy of positivity properties:

$$\text{ultra-log-concave} \;\Longrightarrow\; \text{log-concave} \;\Longrightarrow\; \text{unimodal (no internal zeros)}.$$

ULC is the natural strengthening that is preserved under convolution: Liggett's theorem states that the convolution of two ULC sequences (of orders $m$ and $n$) is ULC of order $m+n$, which underlies stochastic-domination and negative-dependence arguments for sums of independent Bernoulli variables (the coefficients of $\prod(1+p_i x)$). The binomial row $a_k=\binom{n}{k}$ is the model case — indeed the extremal one — of a ULC sequence, and its ULC property is the combinatorial shadow of Newton's inequalities on the elementary symmetric functions $e_k$ of $n$ equal variables. Formalizing the quantified ULC bound thus sharpens the gallery's structural picture of a Pascal row from "log-concave" to "log-concave by the sharp Newton margin."

## Known Results

### What's Already Proven

- Ordinary log-concavity of a Pascal row, $\binom{n}{k}\binom{n}{k+2} \le \binom{n}{k+1}^2$ (strict in the interior) — parent entry `combinations-formula-oq-04` (`Proofs/CombinationsFormulaOQ04.lean`, 0 axioms), via the adjacent-ratio relation `Nat.choose_succ_right_eq`.
- Newton's inequalities $e_k^2 \ge e_{k-1}e_{k+1}\cdot\frac{k+1}{k}\cdot\frac{n-k+1}{n-k}$ for the elementary symmetric functions of $n$ nonnegative reals — Hardy, Littlewood & Pólya, *Inequalities* (1934). Specializing to all variables equal to $1$ gives $e_k = \binom{n}{k}$ and reproduces the ULC inequality above.
- Ultra-log-concavity of the binomial coefficients is classical and is the prototypical example in Stanley's survey *Log-concave and unimodal sequences in algebra, combinatorics, and geometry* (Ann. NY Acad. Sci. 576, 1989).
- Liggett, *Ultra logconcave sequences and negative dependence* (J. Combin. Theory Ser. A 79, 1997): ULC sequences are closed under convolution.
- Mathlib's `Nat.choose_le_middle` records only the unimodal maximum, not log-concavity and not ultra-log-concavity.

### What's Still Open

- The quantified ultra-log-concavity inequality $(k+1)(n-k+1)\binom{n}{k}^2 \ge k(n-k)\binom{n}{k-1}\binom{n}{k+1}$ is not formalized in Lean (Mathlib has neither log-concavity nor its ULC strengthening for `Nat.choose`).
- A Lean statement of ULC as "the normalized sequence is log-concave" (packaging the definition, not just the raw inequality) is open.

### Our Goal

Formalize, over `Nat.choose` in Lean 4 / Mathlib, the strengthened inequality

$$(k+1)(n-k+1)\binom{n}{k}^2 \;\ge\; k(n-k)\binom{n}{k-1}\binom{n}{k+1}\qquad (1 \le k \le n-1),$$

which is the raw (denominator-cleared) form of ultra-log-concavity of the binomial row and strictly refines the parent's log-concavity bound. Secondary target: state the corresponding "normalized sequence is log-concave" packaging over $\mathbb{Q}$ and connect it to the raw $\mathbb{N}$ inequality.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-04 | Direct parent — proves ordinary log-concavity of the row; this entry strengthens it to ULC | `Nat.choose_succ_right_eq` adjacent-ratio, substitution to kill truncated subtraction, cancel positive factor |
| combinations-formula | Grandparent — the basic count $\binom{n}{k}=n!/(k!(n-k)!)$ and the identity family | Factorial identities, `Nat.choose` |
| binomial-theorem | The row is the coefficient sequence of $(1+x)^n$; real-rootedness of this polynomial gives ULC via Newton's inequalities | Generating functions, `Commute.add_pow` / `Nat.choose` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — direct ratio manipulation of consecutive binomials.**
   Use $\binom{n}{k+1}/\binom{n}{k} = (n-k)/(k+1)$, i.e. Mathlib's cleared form $\binom{n}{k+1}(k+1) = \binom{n}{k}(n-k)$ (`Nat.choose_succ_right_eq`). Applying it at $k-1$ and at $k$ gives two exact $\mathbb{N}$ equalities relating $\binom{n}{k-1},\binom{n}{k},\binom{n}{k+1}$; multiply them and clear denominators to reduce the ULC inequality to a manifestly true polynomial inequality in $k$ and $n-k$ (in fact an *equality* for the extremal binomial case, which is why the ULC bound holds with the exact Newton margin). Work in $\mathbb{N}$ throughout, substituting $n = k+1+t$ to make $n-k = t+1$ an honest subtraction.
   - Why it might work: the parent proof already executes exactly this pattern for ordinary log-concavity; the ULC version keeps the $k(n-k)$ / $(k+1)(n-k+1)$ weights instead of discarding them, which is *less* lossy and so no harder.
   - Risk: bookkeeping the two weight factors and the ℕ-vs-ℚ boundary; ensuring the final cancellation stays in ℕ.

2. **Approach B — reduce to Newton's inequality for elementary symmetric functions.**
   The ULC inequality is Newton's inequality $e_k^2 \ge e_{k-1}e_{k+1}\cdot\frac{k+1}{k}\cdot\frac{n-k+1}{n-k}$ specialized to $n$ variables all equal to $1$, where $e_k = \binom{n}{k}$. If Mathlib exposes Newton's inequalities (or real-rootedness $\Rightarrow$ Newton), instantiate the constant polynomial's symmetric functions.
   - Why it might work: gives ULC "for free" as a corollary of a general theorem, and connects to `binomial-theorem`'s $(1+x)^n$.
   - Risk: Mathlib may not have Newton's inequalities in a usable form; specializing `MvPolynomial` elementary-symmetric machinery to equal variables and identifying $e_k$ with `Nat.choose` is heavy.

### Key Difficulties

- **Getting the normalization/definition exactly right.** ULC has several equivalent formulations (normalized-sequence-log-concave, the $(1+\tfrac1k)(1+\tfrac1{n-k})$ multiplicative slack, the $k(n-k)$-weighted inequality); the raw ℕ form must be stated so it is (a) provably equivalent to the intended ULC notion and (b) a genuine strengthening of the parent, not a restatement.
- **ℕ vs ℚ arithmetic.** The clean statement involves rationals $\binom{n}{k}/\binom{n}{k}$; the tractable proof lives in ℕ with cleared denominators. Bridging the two (and handling truncated subtraction $n-k$, plus the edge indices $k=0,k=n$) is the main friction.
- **Avoiding a vacuous or off-by-one weight.** The weights $k$, $n-k$, $k+1$, $n-k+1$ must be pinned so the inequality is the sharp Newton one and not a weaker consequence.

### What Would a Proof Need?

- Key lemma 1: the cleared adjacent-ratio relation `Nat.choose_succ_right_eq : (n.choose (k+1)) * (k+1) = (n.choose k) * (n-k)`, applied at two consecutive indices.
- Key lemma 2: a positivity/cancellation lemma (`Nat.le_of_mul_le_mul_right` / `Nat.mul_le_mul`) to remove the common positive factor after multiplying the two ratio relations.
- Technical requirements: case split on $1 \le k \le n-1$ (edges handled by `Nat.choose_eq_zero_of_lt` / `Nat.choose_pos`); substitution $n = k+1+t$ to make $n-k$ honest; optionally a ℚ-level restatement using `Nat.cast_choose` for the "normalized sequence log-concave" packaging.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Ratios of consecutive binomials are elementary and already handled in the parent via `Nat.choose_succ_right_eq`; the ULC version is the same computation retaining the weight factors, so no new machinery is required for Approach A.
- The parent entry `combinations-formula-oq-04` is a solved, 0-axiom precedent using precisely the technique needed here.
- Mathlib provides all the low-level facts (`Nat.choose_succ_right_eq`, `Nat.choose_pos`, `Nat.choose_eq_zero_of_lt`, cancellation lemmas); the risk is bookkeeping, not missing theory.

**Estimated Effort**:
- Exploration: a few hours (fix the exact statement and normalization)
- If tractable: 1–2 days (Approach A, direct ℕ ratio manipulation)
- If hard: unknown (only if Approach B via general Newton's inequalities is pursued and Mathlib lacks the symmetric-function inequality)

## References

### Papers
- R. P. Stanley, *Log-concave and unimodal sequences in algebra, combinatorics, and geometry* (1989) — survey with the binomial row as the prototypical ultra-log-concave sequence.
- T. M. Liggett, *Ultra logconcave sequences and negative dependence* (1997) — ULC is closed under convolution; negative-dependence applications.
- G. H. Hardy, J. E. Littlewood, G. Pólya, *Inequalities* (1934) — Newton's inequalities on elementary symmetric functions, of which the binomial ULC bound is the equal-variables case.

### Online Resources
- Wikipedia, "Newton's inequalities" — statement of $p_k^2 \ge p_{k-1}p_{k+1}$ for normalized symmetric means and its relation to log-concavity.
- Wikipedia, "Logarithmically concave sequence" — definitions of log-concavity, unimodality, and the ultra-log-concave strengthening.

### Mathlib
- `Mathlib.Combinatorics.Choose.Basic` — `Nat.choose`, `Nat.choose_succ_right_eq` (cleared adjacent ratio), `Nat.succ_mul_choose_eq`, `Nat.choose_symm_diff`, `Nat.choose_eq_zero_of_lt`, `Nat.choose_pos`.
- `Mathlib.Combinatorics.Choose.Factorization` / `Nat.choose_mul_add_le` — auxiliary bounds on products of binomials.
- `Mathlib.Algebra.Order.Monoid.Lemmas` — `Nat.le_of_mul_le_mul_right` for cancelling the common positive factor.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - log-concavity
  - ultra-log-concavity
  - newton-inequality
related_proofs:
  - combinations-formula-oq-04
  - combinations-formula
  - binomial-theorem
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:22-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
