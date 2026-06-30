# Abel's Theorem in the Regular Direction, at Full Strength

## The Question

The parent entry, *Abel Summability at the Boundary*, defined a real sequence
$(a_n)$ to be **Abel summable to $L$** when its power series
$$A(x) = \sum_{n=0}^{\infty} a_n x^n$$
converges for $x \in [0,1)$ and $A(x) \to L$ as $x \to 1^-$. It then established
the **regularity** of the method only for the geometric family $a_n = r^n$ with
$|r| < 1$: there $A(x) = 1/(1-rx) \to 1/(1-r)$, the ordinary sum, by elementary
continuity.

The parent's open question `oq-01` asks for the theorem at full strength:

> **Abel's theorem (regular direction).** If $\sum_n a_n$ converges to $L$, then
> $\sum_n a_n x^n \to L$ as $x \to 1^-$ — for *every* convergent series, not only
> geometric ones.

## Why the General Case Is Genuinely Harder

For $a_n = r^n$ the Abel function has the closed form $1/(1-rx)$, so the boundary
limit is pure continuity of $x \mapsto 1/(1-rx)$ at $x = 1$. For an arbitrary
convergent series there is **no closed form**: the left-limit at $1$ is a real
analytic theorem, proved by **summation by parts** together with a uniform tail
estimate on a Stolz sector. This is exactly the content of **Mathlib's**
`Real.tendsto_tsum_powerSeries_nhdsWithin_lt`, and this entry consumes it rather
than reproving it.

## What This Entry Adds

The parent's `AbelSummableTo` predicate is a **conjunction**:

1. $\forall x \in [0,1),\ \sum_n a_n x^n$ converges (on-disc summability), and
2. $\sum_n a_n x^n \to L$ as $x \to 1^-$ (the boundary limit).

Mathlib's theorem gives only (2). The new mathematics is (1).

### On-disc summability

A convergent series has terms tending to $0$ (`Summable.tendsto_atTop_zero`), so
$|a_n|$ is **bounded** above by some $C$ (`Filter.Tendsto.bddAbove_range`). For
$0 \le x < 1$ each term then satisfies
$$\|a_n x^n\| = |a_n|\,x^n \le C\,x^n,$$
and the geometric majorant $\sum_n C x^n$ is summable
(`summable_geometric_of_lt_one`). The comparison test
(`Summable.of_norm_bounded`) closes it.

The bound by $C x^n$ — rather than by $|a_n|$ — is essential: a conditionally
convergent series such as $\sum (-1)^n/n$ is **not** absolutely summable, so
$|a_n x^n| \le |a_n|$ would not produce a summable majorant. Only $a_n \to 0$ is
used.

## The Theorem

Combining (1) and (2):

$$\textbf{Summable } a \ \Longrightarrow\ \textbf{AbelSummableTo } a \Big(\sum_n a_n\Big).$$

Every convergent real series is Abel summable to its ordinary sum
(`summable_abelSummableTo`), with a `HasSum` variant
(`hasSum_abelSummableTo`).

## The Geometric Case as a Consistency Check

Specialising to $a_n = r^n$, $|r| < 1$: the series converges to $1/(1-r)$
(`hasSum_geometric_of_abs_lt_one`), so by the general theorem it is Abel summable
to $1/(1-r)$ (`geom_abelSummableTo_of_general`) — recovering the parent's
`geom_abelSummableTo` **without computing the boundary limit by hand**. The
parent's hand computation is thereby exhibited as the geometric instance of a
general phenomenon.

## Honest Scope

This is a **packaging** result. The deep analytic theorem (left-continuity of the
Abel function at $1$) is Mathlib's; the contribution is the on-disc summability
lemma, the synthesis into the parent's `AbelSummableTo` vocabulary, and the
explicit reduction of the geometric boundary case to the general statement.
Badge: `mathlib`. 121 lines, 6 theorems, 0 axioms, 0 sorries; each result
depends only on `propext`, `Classical.choice`, `Quot.sound`.
