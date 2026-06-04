# Erdős #430 - Knowledge Base

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

Fix some integer $n$ and define a decreasing sequence in $[1,n)$ by $a_1=n-1$ and, for $k\geq 2$, letting $a_k$ be the greatest integer in $[1,a_{k-1})$ such that all of the prime factors of $a_k$ are $>n-a_k$.

Is it true that, for sufficiently large $n$, not all of this sequence can be prime?



Erd\H{o}s and Graham write 'preliminary calculations made by Selfridge indicate that this is the case but no proof is in sight'. For example if $n=8$ we have $a_1=7$ and $a_2=5$ and then must stop.

Sarosh Adenwalla has observed that this problem is equivalent to (the first part of) [385]. Indeed, assuming a positive answer to that, for all large $n$, there exists a composite $m<n$ such that all primes dividing $m$ are $>n-m$. It follows that such an $m$ is equal to some $a_i$ in the sequence defined for $[1,n)$, and $m$ is composite by assumption.


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
- Problem #385
- Problem #429
- Problem #431
- Problem #2
- Problem #39
- Problem #1

## References

- ErGr80

## Sessions

### 2026-06-04 (researcher-1) — Session 1: small-n positive witnesses

Followed up on Forward Lever 2 (computational evidence) from the
2026-05-13 STATE-SYNC. Added three native_decide-verified positive
witnesses for the smallest n where the conjecture trivially holds
because `n - 1` itself is composite:

- `hasComposite_5` — `greedySeq 5 0 = 4` is composite (2²).
- `hasComposite_7` — `greedySeq 7 0 = 6 = 2 · 3` is composite.
- `hasComposite_9` — `greedySeq 9 0 = 8 = 2³` is composite.

Each is a one-line existential witness: `⟨0, by native_decide,
by native_decide, by native_decide⟩` — the three native_decide
calls discharge `0 < greedySeq n 0`, `¬ (greedySeq n 0).Prime`,
and `1 < greedySeq n 0` respectively.

#### Mathematical Framing

These witnesses are *intentionally trivial*. They isolate the actual
difficulty of the conjecture: the open problem concerns n where
`n - 1` is *prime* (cases like n ∈ {3, 4, 6, 8, 12, 14, 18, 20, 24,
30, …} where the greedy sequence has a fighting chance of remaining
all-prime). For n with composite `n - 1`, `hasComposite n` holds at
`k = 0` essentially by definition.

The `example_n8` theorem already documents one negative case (n = 8,
sequence = 7, 5, both prime). Combined with these three positive
witnesses, the file now records both regimes of the small-n boundary.

#### Stats After Session

- 8 public theorems (+ 5 private lemmas) = 13 total, was 10.
- 7 defs + 2 decidable instances = 9, unchanged.
- 1 axiom (erdos_430_conjecture), 0 sorries.
- 275 lines, was 249.

#### Build Verification

**Deferred to Mechanic/Auditor.** Local Docker daemon is in I/O-error
state on this host (same precedent as szemeredi-theorem-oq-01 S3 and
erdos-951 S4). The new theorems use only `native_decide` on closed
ground terms with computable `greedySeq` / `Nat.Prime` decidability
that the file is already known to support (`example_n8` uses the
same pattern and builds in CI).

#### Files Modified

- `proofs/Proofs/Erdos430Problem.lean` — added 3 theorems
  (hasComposite_5, hasComposite_7, hasComposite_9) and a section
  docstring framing the positive witnesses against the negative
  example_n8.
- `src/data/proofs/erdos-430/meta.json` — bumped lineCount
  (249 → 275), theoremCount (10 → 13), assumptions field.
- `research/problems/erdos-430/state.md` — phase / iteration / next
  action refresh.
- `research/problems/erdos-430/knowledge.md` — this entry.

#### Open Questions Generated

1. What is the smallest n for which `hasComposite n` holds AND `n - 1`
   is prime? (The first nontrivial positive witness.) Verifying this
   would tighten the conjectured N₀.
2. Can we prove `¬ hasComposite n` for the n ∈ {12, 14, 18, 20, 24,
   30, …} family via a decidable-bounded version of `hasComposite`?
   Would need: (a) `greedySeq_zero_persists` (zero stays zero), (b)
   bounded form `hasCompositeBounded n := ∃ k ∈ Finset.range n, …`,
   (c) equivalence proof. ~20-30 line addition.
3. Is there a structural reason `hasComposite n` fails exactly for
   `n - 1 ∈ {2, 3, 5, 7, 11, …}` up to some threshold? Would suggest
   the conjectured N₀ depends on prime-gap structure.

---

*Generated from erdosproblems.com on 2026-01-13*
