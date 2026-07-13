# Problem: Fermat Defect-One Conjecture

**Slug**: fermat-defect-one
**Created**: 2026-06-09
**Status**: Actively attempting (Tier 3)
**Gallery**: `src/data/proofs/fermat-defect-one/`
**Lean source**: `proofs/Proofs/FermatDefectOne.lean`
**Aristotle companion**: `proofs/Proofs/FermatDefectOneAristotle.lean`
**Source**: issues #22620, #22628

## Problem Statement

### Formal Statement (Level 2)

For every integer $n \ge 3$, there exist positive integers $a, b, c$ with

$$2 \le a \le b < c, \quad \gcd(a, b, c) = 1, \quad |a^n + b^n - c^n| = 1.$$

On `Nat`, the absolute-value condition splits into a disjunction:

- $a^n + b^n + 1 = c^n$ (negative defect: $a^n + b^n - c^n = -1$)
- $a^n + b^n = c^n + 1$ (positive defect: $a^n + b^n - c^n = +1$)

```lean
theorem fermat_defect_one_exists :
    ∀ n : Nat, 3 ≤ n → FermatDefectExists n := by
  sorry
```

### Plain Language

Fermat's Last Theorem (Wiles, 1995) says $a^n + b^n - c^n = 0$ has no
nontrivial integer solutions for $n > 2$. The defect-one conjecture asks the
next question: can the defect be exactly $\pm 1$? At $n = 3$ both signs are
witnessed by small primitive triples; for $n \ge 4$ no general construction
is known.

### Statement Hierarchy

- **Level 0** (trivial): $a = c$, $b = 1$ gives $c^n + 1 - c^n = 1$ for any $n$.
  Excluded by demanding $2 \le a$ and $a \le b < c$.
- **Level 1** (nontrivial defect-one existence): for every $n \ge 3$,
  $2 \le a \le b < c$ with $|a^n + b^n - c^n| = 1$.
- **Level 2** (primitive nontrivial existence): Level 1 plus $\gcd(a, b, c) = 1$.
  **This is the headline.**
- **Level 3** (signed primitive existence): for every $n \ge 3$ and every
  $\epsilon \in \{-1, +1\}$, a primitive witness with that sign exists. May
  fail at some $(n, \epsilon)$ — a refutation would itself be a result.

## Known Witnesses (verified)

Both signs are verified at $n = 3$ via `native_decide` in
`proofs/Proofs/FermatDefectOne.lean`:

| Sign | Triple $(a, b, c)$ | Arithmetic | gcd |
|------|-------------------|------------|-----|
| Negative ($a^n + b^n + 1 = c^n$) | $(6, 8, 9)$ | $216 + 512 + 1 = 729$ | $\gcd(2, 9) = 1$ |
| Positive ($a^n + b^n = c^n + 1$) | $(9, 10, 12)$ | $729 + 1000 = 1729 = 1728 + 1$ | $\gcd(1, 12) = 1$ |

The positive-defect witness is a unit-shift of the Ramanujan-Hardy taxicab
number $1729 = 1^3 + 12^3 = 9^3 + 10^3$.

No primitive nontrivial defect-one witness is currently known at $n \ge 4$.

## Attack Vectors

A claim file in `claims/` should pick exactly one vector (named exactly as
below) and document what was tried, what happened, and what to try next. See
`research/PROBLEMS-STRUCTURE.md` for the claim-file format.

### 1. `witness-search` — bounded search for $n = 4, 5, 6, \ldots$

For each fixed $n$, enumerate $(a, b, c)$ with $2 \le a \le b < c \le N$,
filter by mod-$p$ pre-tests, and check the defect condition. A single
primitive witness at any $(n, N)$ ships as a verified `native_decide` theorem
of the form

```lean
theorem fermat_defect_witness_n_<k> : FermatDefectWitness <k> <a> <b> <c>
```

and clears that exponent off the open list. Aristotle companion targets
(see `proofs/Proofs/FermatDefectOneAristotle.lean`):

- `witness_n_eq_4_bounded_50` — does $n = 4$ admit a witness with $c \le 50$?
- `witness_n_eq_5_bounded_50` — does $n = 5$ admit a witness with $c \le 50$?

### 2. `modular-obstruction` — Level 3 refutation candidates

For each candidate $(n, \epsilon)$, check whether some prime $p$ obstructs all
solutions: $a^n + b^n \pm 1 \equiv c^n \pmod{p}$ for all $(a, b, c)$. A
Level-3 refutation at any specific $(n, \epsilon)$ is itself a publishable
result. Typical targets: $n \in \{4, 5, 6, 8, 10\}$, $p \in \{3, 5, 7, 11, 13\}$.

### 3. `parameterization` — polynomial families

Search for families $(a(t), b(t), c(t)) \in \mathbb{Z}[t]^3$ with
$a(t)^n + b(t)^n - c(t)^n \equiv \pm 1$ identically. One such family proves
the conjecture for infinitely many witnesses at the given $n$ in a single
shot. Sub-attacks: linear, quadratic, and cubic parameterizations; reuse of
the $n = 3$ benchmark structure.

### 4. `reduction` — Thue / Fermat-Catalan

Does the conjecture (or its negation at specific $n$) follow from known
finiteness results applied in a particular regime? The Fermat-Catalan
equation $x^p + y^q = z^r$ with $1/p + 1/q + 1/r < 1$ has finitely many
primitive solutions (conjectured); the defect-one problem at exponent $n$ is
a unit-offset diagonal slice.

### 5. `structural-lemma` — asymptotic $M(n)$

Let $M(n) = \min \{c : \exists\, (a, b) \text{ with } 2 \le a \le b < c,
\gcd(a, b, c) = 1, |a^n + b^n - c^n| = 1\}$ when this set is non-empty. Any
bound $M(n) = O(n^k)$ (or even $M(n) \le f(n)$ for an explicit $f$) would
be a publishable result.

Bounded-nonexistence theorems contribute lower bounds on $M(n)$. The
Aristotle companion exposes:

- `no_witness_n_eq_4_below_20` — proves $M(4) \ge 21$ if $M(4)$ is finite.

## Connections

| Target | Relationship |
|---|---|
| Fermat's Last Theorem (FLT) | Zero defect impossible at $n > 2$; defect-one asks whether the very next defect is realised. |
| Pillai's conjecture | Finiteness of solutions to $a^x - b^y = c$ for fixed $c$. Defect-one is a richer Pillai-type question. |
| Fermat-Catalan conjecture | $x^p + y^q = z^r$ with $1/p + 1/q + 1/r < 1$ has finitely many primitives. Defect-one at exponent $n$ is the unit-offset diagonal $p = q = r = n$. |
| Thue equations | Finiteness for $F(x, y) = c$ with $F$ irreducible. Relevant to vector 4. |
| Taxicab number 1729 | The $n = 3$ positive-defect witness $9^3 + 10^3 - 12^3 = 1$ is a unit-distance fact about $1729 = 1^3 + 12^3 = 9^3 + 10^3$. |

## References

- Wiles, "Modular elliptic curves and Fermat's Last Theorem" (1995).
- Pillai, "On $a^x - b^y = c$" (1936).
- Darmon and Granville, "On the equations $z^m = F(x, y)$ and $Ax^p + By^q = Cz^r$" (1995).
- Beukers, "The Diophantine equation $Ax^p + By^q = Cz^r$" (1998).
- Waldschmidt, "Perfect powers: Pillai's works and their developments" (2009) —
  [PDF](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/PerfectPowers.pdf).
- Hardy, "Ramanujan: Twelve Lectures…" (1940) — taxicab anecdote.

## Sub-issues

Each attack vector is tracked as its own follow-up issue (filed under
`loom:curated`):

- #22635 — `witness-search` at $n = 4$, $c \le 1000$.
- #22636 — `modular-obstruction` (Level 3) at $n = 4, 5, 6$.
- #22637 — `parameterization` (polynomial families).
- #22638 — `reduction` (Thue / Fermat-Catalan).

Each sub-issue should produce either a verified Lean theorem (positive
result) or a curated claim file in `claims/` (negative result). Both outcomes
count as progress.
