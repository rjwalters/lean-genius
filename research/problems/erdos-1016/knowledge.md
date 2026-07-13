# Erdős #1016 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $h(n)$ be minimal such that there is a graph on $n$ vertices with $n+h(n)$ edges which contains a cycle on $k$ vertices, for all $3\leq k\leq n$. Estimate $h(n)$. In particular, is it true that\[h(n) \geq \log_2n+\log_*n-O(1),\]where $\log_*n$ is the iterated logarithmic function?



Such graphs are called pancyclic. A problem of Bondy \cite{Bo71}, who claimed a proof (without details) of\[\log_2(n-1)-1\leq h(n) \leq \log_2n+\log_*n+O(1).\]Erd\H{o}s \cite{Er71} believed the upper bound is closer to the truth, but could not even prove $h(n)-\log_2n\to \infty$.

A proof of the above lower bound is provided by Griffin \cite{Gr13}. The first published proof of the upper bound appears to be in Chapter 4.5 of George, Khodkar, and Wallis \cite{GKW16}.




References


[Bo71] Bondy, J. A., Pancyclic graphs. {I}. J. Combinatorial Theory Ser. B (1971), 80--84.

[Er71] Erd\H{o}s, P., Some unsolved problems in graph theory and combinatorial analysis. Combinatorial Mathematics and its Applications (Proc.
Conf., Oxford, 1969) (1971), 97-109.

[GKW16] George, John C. and Khodkar, Abdollah and Wallis, W. D., Pancyclic and bipancyclic graphs. (2016), xii+108.

[Gr13] S. Griffin, Minimal Pancyclicity. arXiv:1312.0274 (2013).


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #1015
- Problem #1017
- Problem #2
- Problem #39
- Problem #1

## References

- Er71
- Bo71
- Gr13
- GKW16

## Sessions

### 2026-06-05 (researcher-1) — Repair build break + iteratedLog structural lemmas

**Mode**: REVISIT
**Mode of progress**: build-repair + small structural additions

Discovered that `proofs/Proofs/Erdos1016Problem.lean` was broken on `main`:

1. `iteratedLog` was declared `noncomputable def` without a `termination_by`
   clause. The recursive call is on `Nat.log 2 (n + 2)` which is not a
   structural subterm of `n`, so Lean's structural-recursion check fails
   and well-founded recursion is required. Build error:
   ```
   error: Proofs/Erdos1016Problem.lean:45:18: fail to show termination for iteratedLog
   ```
2. `bondy_quadratic_threshold` used
   `le_of_lt (Nat.log_lt (by omega) (by omega))` to obtain
   `Nat.log 2 n ≤ n`. In current Mathlib (v4.26.0), `Nat.log_lt` is the
   *iff* lemma `Nat.log b n < k ↔ n < b^k`, not a direct propositional
   witness. Build error:
   ```
   error: Proofs/Erdos1016Problem.lean:156:47: Unknown constant `Nat.log_lt`
   ```
3. `rcases le_or_lt n 15 with …` triggered a deprecation warning
   (`le_or_lt` → `le_or_gt`).

**Repairs**:

- Removed `noncomputable` from `iteratedLog` (`Nat.log` is computable) and
  added an explicit `termination_by n => n` + `decreasing_by` block using
  `Nat.log_le_self`, `Nat.pow_log_le_self`, and `Nat.lt_two_pow_self` to
  rule out the `Nat.log 2 (n + 2) = n + 2` equality case.
- Replaced the broken `Nat.log_lt` line with `Nat.log_le_self 2 n`.
- Replaced `le_or_lt` with `le_or_gt`.

**New theorems (5)**:

- `iteratedLog_zero : iteratedLog 0 = 0` (`@[simp]`)
- `iteratedLog_one : iteratedLog 1 = 0` (`@[simp]`)
- `iteratedLog_add_two : iteratedLog (n+2) = 1 + iteratedLog (Nat.log 2 (n+2))`
- `iteratedLog_eq_zero_iff : iteratedLog n = 0 ↔ n ≤ 1`
- `iteratedLog_pos : 2 ≤ n → 1 ≤ iteratedLog n`

These are independent of the documented `IsPancyclic` modelling flaw — they
characterize the iterated logarithm itself and survive any future redesign
of the graph-theoretic encoding.

**Verification**: Docker build (`./proofs/scripts/docker-build.sh
Proofs.Erdos1016Problem`) succeeds cleanly; only a pre-existing
`unused variable edgeCount` linter warning remains.

**State**: 0 sorries, 0 axioms, 12 theorems, 3 defs, 209 LOC (was 158).

**Next**: Build a corrected `SimpleGraph (Fin n)` based pancyclic model in
a separate section; the abstract `IsPancyclic` model remains as a
documented diagnostic scaffold so the relationship between the two
encodings stays explicit.

---

*Generated from erdosproblems.com on 2026-01-15*
