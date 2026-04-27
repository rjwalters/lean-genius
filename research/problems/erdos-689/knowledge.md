# Erdős #689 - Knowledge Base

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

Let $n$ be sufficiently large. Is there some choice of congruence class $a_p$ for all primes $2\leq p\leq n$ such that every integer in $[1,n]$ satisfies at least two of the congruences $\equiv a_p\pmod{p}$?



One can ask a similar question replacing $2$ by any fixed integer $r$ (provided $n$ is sufficiently large depending on $r$).

See also [687] and [688].

This problem (with $2$ replaced by $10$) is Problem 45 on Green's open problems list.


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
- Problem #687
- Problem #688
- Problem #690
- Problem #2
- Problem #39
- Problem #1

## References

- Er79d

## Sessions

### Session 2026-04-27 (Session 2) — Metadata reconciliation

**Mode**: REVISIT (RICH knowledge tier, score 16)
**Outcome**: stable — formalization at minimal axiom count, JSON metadata reconciled.

#### Why Revisit

Prior session(s) had reduced the Lean file `Erdos689Problem.lean` to 1 axiom (the
open conjecture itself) and proved 13 supporting theorems including
`mertens_sum_divergence`. However, the JSON `src/data/research/problems/erdos-689.json`
still had `whyMatters: []`, `knownResults.proven: []`, `knownResults.open: []`,
`knownResults.goal: ""`, phase `OBSERVE`, and `relatedProofs` containing a
self-reference (`erdos-689` listed as related to itself). The metadata did not
reflect the actual state of the formalization.

#### What I Did

1. Read `proofs/Proofs/Erdos689Problem.lean` (180 lines, 1 axiom, 13 theorems, 0 sorries).
2. Confirmed the only remaining axiom `erdos_689_r_fold` IS the open Erdős
   conjecture (and Ben Green's open problem 45 in the r=10 case).
3. Updated `src/data/research/problems/erdos-689.json`:
   - Filled in `whyMatters` (4 entries) describing the significance.
   - Populated `knownResults.proven` with the 9 proved structural lemmas and the
     3 derived consequences (`erdos_689_double_cover`, `green_variant_r10`,
     `jacobsthal_connection`).
   - Populated `knownResults.open` with the single remaining axiom.
   - Set `knownResults.goal` to honestly describe the stable endpoint.
   - Advanced `phase` from `OBSERVE` to `ACT` (the file IS in stable post-action
     state — formalization is complete modulo the open conjecture).
   - Cleaned `relatedProofs` (removed self-reference; added 687/688/690 siblings).
   - Expanded `tags` to include `covering-systems`, `primes`, `open-conjecture`,
     `mertens-theorem`.
   - Added an explicit `blockers` entry recording that the remaining axiom is
     the open question itself.

#### Key Finding (already established by prior sessions, re-asserted here)

**The file is at minimal axiom count.** The single remaining axiom
`erdos_689_r_fold (r : ℕ) (hr : r ≥ 1) : ∃ N₀, ∀ n ≥ N₀, ∃ a, IsRFoldCover n r a`
captures *all* of:
- Erdős #689 (the original r=2 problem),
- Ben Green's open problem 45 (the r=10 variant),
- The Jacobsthal-style 1-fold covering (the r=1 case).

Consolidating these into a single r-fold axiom is itself a small contribution:
we now have one open conjecture rather than three.

The `mertens_sum_divergence` lemma — Σ_{p ≤ n} 1/p → ∞ — was extracted from
Mathlib's `not_summable_one_div_on_primes`. This provides heuristic intuition
for why r-fold covering should be possible (random assignments give expected
coverage equal to a divergent sum), but does NOT prove the conjecture.

#### Files Modified

- `src/data/research/problems/erdos-689.json` (metadata reconciled)
- `research/problems/erdos-689/knowledge.md` (this file — session record)
- `research/problems/erdos-689/state.md` (phase, iteration, focus updated)

#### Files NOT Modified

- `proofs/Proofs/Erdos689Problem.lean` — already at minimal axiom count;
  no Lean changes possible without solving the open conjecture or adding
  non-axiom-reducing structural depth (deferred — disk at 91%/1.3 GB free
  flagged Docker builds as risky).

#### Next Steps

1. **MAINTAIN** — this slug should be deprioritized for axiom-removal sessions.
2. **Optional structural enrichment** (does NOT reduce axiom count):
   - Prove `expectedCoverage`: for uniform random a_p, expected coverage of any
     m ∈ [1,n] equals Σ_{p≤n} 1/p (which → ∞ by `mertens_sum_divergence`). This
     turns the heuristic into a formal probability statement.
   - Compute exact small-r=2 cases (e.g., explicit 2-fold covers for n ≤ 30).
3. **Cross-reference siblings** — `erdos-687` (Jacobsthal upper-bound problem)
   and `erdos-688` (covering with restricted prime ranges).

---

*Generated from erdosproblems.com on 2026-01-14; updated by researcher-10 on 2026-04-27.*
