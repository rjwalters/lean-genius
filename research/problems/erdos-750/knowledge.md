# Erdős #750 - Knowledge Base

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

Let $f(m)$ be some function such that $f(m)\to \infty$ as $m\to \infty$. Does there exist a graph $G$ of infinite chromatic number such that every subgraph on $m$ vertices contains an independent set of size at least $\frac{m}{2}-f(m)$?



In \cite{Er69b} Erd\H{o}s conjectures this for $f(m)=\epsilon m$ for any fixed $\epsilon>0$. This follows from a result of Erd\H{o}s, Hajnal, and Szemer\'{e}di \cite{EHS82}, as described by msellke in the comments.

In \cite{ErHa67b} Erd\H{o}s and Hajnal prove this for $f(m)\geq cm$ for all $c>1/4$.

See also [75].




References


[EHS82] Erd\H{o}s, P. and Hajnal, A. and Szemer\'{e}di, E., On almost bipartite large chromatic graphs. Theory and practice of combinatorics (1982), 117-123.

[Er69b] Erd\H{o}s, P., Problems and results in chromatic graph theory. Proof Techniques in Graph Theory (Proc. Second Ann
Arbor Graph Theory Conf., Ann Arbor, Mich.,
1968) (1969), 27-35.

[ErHa67b] Erd\H{o}s, P. and Hajnal, Andr\'as, On chromatic graphs. Mat. Lapok (1967), 1--4.


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
- Problem #4
- Problem #75
- Problem #749
- Problem #751
- Problem #2
- Problem #39
- Problem #1

## References

- Er94b
- Er95d
- Er69b
- EHS82
- ErHa67b

## Sessions

### Session 2026-04-27 (Session 2) — Identify formalization gap

**Mode**: REVISIT (MODERATE knowledge tier, score 6)
**Outcome**: progress — identified that the open conjecture is described in
docstrings but NOT actually formalized as a Lean proposition.

#### What I Found

The Lean file `proofs/Proofs/Erdos750Problem.lean` (111 lines) currently contains:

- 3 definitions: `HasInfiniteChromatic`, `maxIndSetSize`, `AlmostBipartite`
- 1 private theorem: `fin2_ne_zero_eq_one` (utility for Fin 2)
- 1 main theorem: `bipartite_benchmark` (bipartite graphs achieve `m/2` for the
  independence requirement — this is the **trivial** baseline, not the open conjecture)
- 0 axioms, 0 sorries

**The open Erdős conjecture is NOT formalized as a proposition.** Lines 49–67 of
the Lean file have a sequence of `/-- ... -/` docstrings describing:

- The main conjecture (line 51–52)
- Erdős–Hajnal 1967 result (line 55–56)
- Erdős–Hajnal–Szemerédi 1982 result (line 57–58)
- Open square-root case (line 61–62)
- Open logarithmic case (line 63)
- Problem #75 connection (line 66–67)

But these docstrings are **orphaned** — none of them is followed by an `axiom`,
`theorem`, or `def` declaration. They are prose embedded as docstring syntax,
attached either to nothing (a Lean error if strict) or eventually absorbed by the
next declaration `fin2_ne_zero_eq_one`, where the description doesn't apply.

#### Why The Existing JSON Was Misleading

The JSON `progressSummary` reads `"COMPLETE: Assessed and marked complete."` and
the file has 0 axioms and 0 sorries. By naive metrics this looks finished. But
**the open conjecture has no Lean expression at all**. Compare:

- Erdős #689 (similar OPEN problem, similar tractability) explicitly writes
  `axiom erdos_689_r_fold (r : ℕ) (hr : r ≥ 1) : ∃ N₀, ∀ n ≥ N₀, ∃ a, IsRFoldCover n r a`
  and then derives `erdos_689_double_cover := erdos_689_r_fold 2`. This is a
  proper formalization: the open conjecture is a named Lean proposition.
- Erdős #750 has the analogous `AlmostBipartite` definition and a docstring
  describing the conjecture, but no corresponding `axiom erdos_750 : ...`.

A future session should add the missing axiom (and possibly derived consequences
for the Erdős–Hajnal cases proved in 1967/1982).

#### Recommended Formalization (for next ACT session)

```lean
/-- **Erdős Problem #750 (OPEN)**: For any f : ℕ → ℕ with f → ∞, there exists
    an infinite-chromatic graph that is f-almost-bipartite eventually. -/
axiom erdos_750
    (f : ℕ → ℕ) (hf : Filter.Tendsto f Filter.atTop Filter.atTop) :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V) (m₀ : ℕ),
      HasInfiniteChromatic G ∧ AlmostBipartite G f m₀

/-- **Erdős–Hajnal 1967** (proved in literature, axiomatized here pending
    Mathlib chromatic-graph machinery): Resolves Problem #750 for f(m) = c·m
    with c > 1/4. -/
axiom erdos_hajnal_1967 (c : ℝ) (hc : c > 1/4) : ...

/-- **Erdős–Hajnal–Szemerédi 1982**: Resolves Problem #750 for f(m) = ε·m
    with any ε > 0. -/
axiom ehs_1982 (ε : ℝ) (hε : ε > 0) : ...

/-- The open square-root case follows from `erdos_750` applied to f(m) = ⌊√m⌋. -/
theorem erdos_750_sqrt : ... := erdos_750 (fun m => Nat.sqrt m) sqrt_tendsto_atTop
```

This would raise the file's axiom count from 0 to 3 (or so), but it accurately
reflects what is actually formalized vs. what remains conjectural. Per the
project's axiom integrity policy (CLAUDE.md), an open conjecture should be
expressed as an `axiom`, not as a docstring with no proposition behind it.

#### What I Did This Session

1. Read `proofs/Proofs/Erdos750Problem.lean` and confirmed the orphan-docstring
   pattern.
2. Updated `src/data/research/problems/erdos-750.json`:
   - Filled in `whyMatters`.
   - Documented the formalization gap in `knownResults.open`.
   - Set `phase` to `ORIENT` (was `OBSERVE` at top level / `NEW` in nested state).
   - Cleaned `relatedProofs` (removed self-reference).
3. Wrote this session record.

#### Files Modified

- `src/data/research/problems/erdos-750.json`
- `research/problems/erdos-750/knowledge.md` (this file)
- `research/problems/erdos-750/state.md`

#### Files NOT Modified

- `proofs/Proofs/Erdos750Problem.lean` — disk at 91%/1.2 GB free flagged
  Docker builds as risky; the recommended axiom additions are deferred to a
  session with adequate disk to verify they typecheck.

#### Next Steps

1. ACT (next session with disk): add `axiom erdos_750` and possibly the
   `axiom erdos_hajnal_1967` / `axiom ehs_1982` derived statements; convert the
   orphan docstrings into actual declarations.
2. Build verify with Docker, then the file's `axiomCount` correctly becomes ≥1
   (matching its actual mathematical status as an open-conjecture formalization).

---

*Generated from erdosproblems.com on 2026-01-15; updated by researcher-10 on 2026-04-27.*
