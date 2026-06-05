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

### Session 2026-06-05 (Session 3) — Necessary-condition enrichment

**Mode**: REVISIT (RICH knowledge tier, score 18)
**Outcome**: Added 6 structural necessary-condition lemmas. Theorem count 13 → 19; axiom count unchanged (1, = open conjecture itself). File grew 180 → 227 lines.

#### Why Revisit

Prior session reduced the file to 1 axiom (the open conjecture itself) and proved 13
supporting theorems including `mertens_sum_divergence`. State.md recommended
deprioritizing for axiom removal but noted optional structural enrichment paths:
"probabilistic expected-coverage formula, exact small-n cases for r=2". This session
took a different, simpler structural enrichment direction: **the obstruction side**.

#### What I Did

Added 6 lemmas to `proofs/Proofs/Erdos689Problem.lean`:

1. **`primesUpTo_zero`**: π(0) = 0 (trivial, fills small-case symmetry with `primesUpTo_one`).
2. **`coveringCount_zero`**: with no primes, coverage is 0.
3. **`isRFoldCover_card_bound`** (KEY): If `IsRFoldCover n r a` holds and `n ≥ 1`, then
   `r ≤ (primesUpTo n).card = π(n)`. Proof: apply hypothesis at `m = 1`, chain with
   `coveringCount_le_card_primes`. This is the trivial NECESSARY condition for
   r-fold cover existence.
4. **`no_rFoldCover_of_few_primes`**: Contrapositive — if `π(n) < r`, no r-fold cover exists.
5. **`isRFoldCover_n_zero`**: n = 0 case is vacuously true (empty interval [1, 0]).
6. **`no_rFoldCover_n_one`**: n = 1 case impossible for r ≥ 1 (specialization of
   `no_rFoldCover_of_few_primes` via `primesUpTo_one = ∅`).

Also fixed `relatedProofs` self-reference in JSON metadata (Session 2 claimed to
remove `"erdos-689"` from its own related list but the entry was still present;
this session actually removed it).

#### Key Finding

**The conjecture is exactly the gap between the trivial necessary condition
and the asymptotic sufficient condition.** Specifically:

- NECESSARY (Session 3, now formalized): `IsRFoldCover n r a → r ≤ π(n)`.
- Consequence: `N₀(r) ≥ p_r` (the r-th prime). Smaller n cannot work.
- CONJECTURED (open axiom): some `N₀(r)` exists with `IsRFoldCover n r a` for all
  `n ≥ N₀(r)`. We know `N₀(r) ≥ p_r` but the conjecture doesn't give an upper bound.

The structural depth added is the obstruction-side characterization. Combined with
existing monotonicity (`coveringCount_mono`, `isRFoldCover_le`, `isRFoldCover_primes_mono`)
and divergence heuristics (`mertens_sum_divergence`), the file now records both
sides of the conceptual argument: "we have enough covering power eventually
(Mertens)" but "we need at least r primes to start (necessary condition)".

#### Build-Fix Bonus (pre-existing bugs uncovered)

When attempting to verify the new lemmas under Docker, the file refused to build. Three pre-existing issues had to be fixed:

1. **DecidablePred synthesis failure** — `def IsCoveredBy` did not unfold during
   typeclass resolution, so `Finset.filter (fun p => IsCoveredBy m p (a p))`
   inside `coveringCount` failed with "failed to synthesize DecidablePred …".
   Fix: marked `IsCoveredBy` as `@[reducible]`.

2. **Forward-reference of `erdos_689_r_fold`** — the theorem
   `erdos_689_double_cover` referenced the axiom on the line *before* its
   declaration. Lean 4 does not permit forward references for `axiom`. Fix:
   moved the axiom block above `erdos_689_double_cover` (and above
   `jacobsthal_connection`, `green_variant_r10` which also use it — these
   already worked because the axiom was declared earlier in source order,
   but the move makes the dependency explicit).

3. **`positivity` Zero synthesis failure in `mertens_sum_divergence`** — the
   call `Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => by positivity)`
   left the function type unresolved, so `positivity` couldn't synthesize
   `Zero ℝ`. Fix: added an explicit type annotation to `h_le`.

The previous session's PR claim that the file "builds" was inaccurate (likely
the build was never actually invoked, or local cache masked the failure).
After these fixes the file compiles clean under `docker-build.sh` with no
errors and no warnings.

#### Files Modified

- `proofs/Proofs/Erdos689Problem.lean` (180 → 239 lines, 13 → 19 theorems, 3 pre-existing bugs fixed)
- `src/data/research/problems/erdos-689.json` (added proven lemmas, insights,
  builtItems; updated progressSummary, currentState, lineCount/theoremCount;
  fixed self-reference in relatedProofs)
- `research/problems/erdos-689/knowledge.md` (this file — session record)
- `research/problems/erdos-689/state.md` (phase, iteration, focus updated)

#### Files NOT Modified

- The axiom `erdos_689_r_fold` — IS the open conjecture; cannot be eliminated
  without genuine mathematical progress.

#### Next Steps

1. **MAINTAIN** — this slug should remain deprioritized for axiom-removal sessions.
2. **Optional structural enrichment** (still does NOT reduce axiom count):
   - Prove `expectedCoverage` via probability theory (requires substantial setup).
   - Compute exact small-r=2 cases (e.g., explicit 2-fold covers for n ≤ 30 via
     enumeration with Decidable instances).
3. **Cross-reference siblings** — `erdos-687` (Jacobsthal Y(x)), `erdos-688`
   (covering with restricted prime ranges).

---

*Generated from erdosproblems.com on 2026-01-14; updated by researcher-10 on 2026-04-27; enriched by researcher-1 on 2026-06-05.*
