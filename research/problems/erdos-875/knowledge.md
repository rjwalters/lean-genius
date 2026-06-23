# Erdős #875 — Knowledge Base

## Problem statement (canonical)

Let $A=\{a_1<a_2<\cdots\}\subset\mathbb{N}$ be an infinite set. Define
$$S_r := \{a_{i_1}+\cdots+a_{i_r} : i_1<\cdots<i_r\},\qquad r\ge 1.$$

$A$ is **admissible** iff $S_r\cap S_{r'}=\emptyset$ for all $r\ne r'\ge 1$.

**Erdős–Deshouillers questions** (infinite version of #874):

- How fast must $a_n$ grow?
- How small can $a_{n+1}-a_n$ be?
- For which $c$ is it possible that $a_{n+1}-a_n\le n^c$?

Erdős writes: "it [is not] completely trivial to find such a sequence for which $a_{n+1}/a_n\to 1$."

## Status

**Erdős Database Status**: OPEN
**Tractability Score**: 4/10
**Aristotle Suitable**: No (open conjecture; no Mathlib API for "admissible sequence" exists yet)

## Recorded mathematical facts

### Existence: powers of 2 are admissible

$A=\{2^{n-1}\}_{n\ge 1}=\{1,2,4,8,\dots\}$ is admissible because every $v\in\mathbb{N}_{>0}$ has a *unique* binary representation, so if $v$ is a sum of $r$ distinct powers of $2$ and also of $r'$ distinct powers of $2$, then $r=\mathrm{popcount}(v)=r'$.

Growth rate: $a_{n+1}/a_n=2$ constant. This is the *fast* admissible regime; Erdős asks for the slow regime.

### Super-increasing sequences are admissible

Any $A$ with $a_{n+1}>a_1+\cdots+a_n$ is admissible. Given a sum $v\in S_r$, the largest summand is uniquely determined (greedy / "highest bit"), and recursion on $v-a_{\max}$ recovers the full subset, hence its size $r$.

Such sequences grow at least as fast as $2^{n-1}$.

### Polynomial gaps are not ruled out by elementary pigeonhole

If $a_n\le N^c$ for $n\le N$, disjointness gives
$$\sum_{r=1}^{N}|S_r| \le N\cdot a_N \le N^{c+1}.$$
Trivial lower bound: $|S_r|\ge N-r+1$ (vary the largest element), so $\sum_r|S_r|\ge N(N+1)/2$, well below $N^{c+1}$ for any $c\ge 1$. **No contradiction at this level.**

To get a polynomial-gap impossibility (or possibility), one must engage with non-trivial lower bounds on $|S_r|$ — likely via Plünnecke–Ruzsa $|rA|\le|A+A|^r/|A|^{r-1}$ or additive-energy estimates.

### Greedy admissible sequence (first values, hand-computed)

$a_1=1,\ a_2=2,\ a_3=4$.

* $a_3=3$ fails: $S_1\ni3$ and $S_2\ni1{+}2=3$, collision.
* $a_3=4$ works: $S_1=\{1,2,4\}, S_2=\{3,5,6\}, S_3=\{7\}$ — all pairwise disjoint.

S2 will continue this enumeration by computer and study the asymptotic.

## Sub-questions for follow-up sessions

* **Q1** — slow growth: does an admissible $A$ with $a_{n+1}/a_n\to 1$ exist? Attack: greedy / probabilistic / mixed-radix constructions.
* **Q2** — polynomial-gap impossibility: prove or disprove a lower bound of form $a_{n+1}-a_n\ge n^c$ infinitely often, via Plünnecke–Ruzsa.
* **Q3** — density / asymptotic: derive a non-trivial upper bound on $|A\cap[1,X]|$ from the disjoint-subset-sum constraint, via additive-energy.

## Tags

- erdos
- additive-combinatorics
- sidon-type
- sumset-disjointness

## Related problems

Per problem.md: #2000, #83, #888, #1998, **#874** (finite version), #876, #2, #39, #1. The most directly relevant is **#874**: finite admissible sets, i.e. the same disjointness condition on a finite $A$ with maximum size or maximum sum constrained.

## References

- Erdős, P., *Some of my favourite problems in number theory, combinatorics, and geometry*, 1998 (`[Er98]` in the problem listing).

## Mathlib API survey (deferred to S2)

The admissibility predicate would naturally be phrased in Lean as one of:

```lean
def Admissible (a : ℕ → ℕ) : Prop :=
  StrictMono a ∧
  ∀ r r' : ℕ, r ≠ r' →
    ∀ s : Finset ℕ, s.card = r →
    ∀ s' : Finset ℕ, s'.card = r' →
      (s.image a).sum id ≠ (s'.image a).sum id
```

or, more Mathlib-idiomatic, via `Finset.powersetCard`:

```lean
def Sr (a : ℕ → ℕ) (r : ℕ) (N : ℕ) : Finset ℕ :=
  ((Finset.range N).powersetCard r).image (fun s => (s.image a).sum id)
```

The choice is deferred until S2's slow-growth construction has a concrete shape (greedy / mixed-radix / probabilistic), since each shape suggests a different definitional convenience.

## Sessions

* **S1** (2026-06-09): ORIENT — problem restatement, trivial powers-of-2 construction, pigeonhole gap, Q1/Q2/Q3 factorization. No Lean artifact.

---

*Generated from erdosproblems.com on 2026-01-15. Knowledge enriched 2026-06-09.*
