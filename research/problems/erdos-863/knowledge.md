# Erdős #863 - Knowledge Base

## Problem Statement

Let $r\geq 2$ and let $A\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a+b$ with $a\leq b$ for any $n$. (That is, $A$ is a $B_2[r]$ set.)

Similarly, let $B\subseteq \{1,\ldots,N\}$ be a set of maximal size such that there are at most $r$ solutions to $n=a-b$ for any $n$.

If $\lvert A\rvert\sim c_rN^{1/2}$ as $N\to \infty$ and $\lvert B\rvert \sim c_r'N^{1/2}$ as $N\to \infty$ then is it true that $c_r\neq c_r'$ for $r\geq 2$? Is it true that $c_r'<c_r$?

Known: $c_1=c_1'=1$ (classical Sidon set bound).

## Status

**Erdős Database Status**: OPEN
**Tractability Score**: 4/10
**Aristotle Suitable**: Companion file created

## Axiom Analysis

3 axioms, all deep or OPEN:
1. `sidon_classical` — Known result (Erdős-Turán upper bound + Singer lower bound). Deep: requires substantial Mathlib formalization.
2. `ErdosProblem863` — Main OPEN conjecture: $c_r' < c_r$ for $r \geq 2$.
3. `erdos_863_weak` — Weaker OPEN conjecture: $c_r \neq c_r'$ for some $r \geq 2$.

None are eliminable with current Mathlib.

## Infrastructure Built (Session 1 — 2026-03-27)

**8 theorems proved in main file:**
- `isB2r_mono` / `isDiffB2r_mono` — B₂[r] monotone in r (term-mode proofs)
- `inRange_mono` / `inRange_empty` — InRange monotonicity and empty set
- `isB2r_empty` / `isDiffB2r_empty` — Empty set is B₂[r]
- `sumRepCount_le_card_sq` / `diffRepCount_le_card_sq` — Representation count ≤ |A|²

**Aristotle companion (Erdos863Aristotle.lean) — 5 sorry targets:**
- `isB2r_singleton` / `isDiffB2r_singleton` — Singleton is B₂[r]
- `isB2r_subset` / `isDiffB2r_subset` — Subset preserves B₂[r]
- `sidon_counting_bound` — |A|² ≤ 4N for Sidon sets in {1,...,N}

## Key Insights

- `IsB2r A 1` is equivalent to `IsSidonSet A` from Erdos340Problem.lean. Future work: prove this connection.
- Counting argument: ordered pairs (a,b) with a ≤ b give C(|A|,2)+|A| distinct sums in {2,...,2N}, so |A|(|A|+1)/2 ≤ 2N-1.
- Cilleruelo-Ruzsa-Trujillo (2002): |A| ≤ (rN)^{1/2} + O(r^{1/2}N^{1/4}) for B₂[r] sets.
- Ruzsa: c_r ~ √r, but c'_r precision insufficient to separate from c_r.

## Related Problems

- Erdős #340 — Greedy Sidon sequence (IsSidonSet definition)
- Erdős #862, #864 — Adjacent problems
- Erdős #530 — Maximum Sidon subsets

## References

- Er92c (Erdős, with Berend and Freud)
- Cilleruelo-Ruzsa-Trujillo (2002) — B₂[r] upper bound

## Sessions

### Session 1 (2026-03-27, researcher-4)
- **Mode**: FRESH
- **Decision**: BUILD — add provable infrastructure, create Aristotle companion
- **Outcome**: 8 theorems proved, companion file created with 5 targets
- **Next**: Aristotle processes companion; connect to Erdos340 IsSidonSet

### Session 2 (PR #7181, 2026-03-27)
- **Outcome**: 4 new theorems proved in main file, all 5 Aristotle
  companion targets fully implemented (no longer stubs):
  - `isB2r_singleton`, `isDiffB2r_singleton` — singletons are B₂[r]/diff B₂[r]
  - `isB2r_subset`, `isDiffB2r_subset` — subsets preserve the property
  - `IsSidonSetLocal` (def) and `isB2r_one_iff_sidon` — establishes
    B₂[1] ↔ Sidon, the key connection to Erdős #340
  - `sidon_counting_bound` — |A|² ≤ 4N for Sidon sets (full proof, not stub)

### Session 3 (2026-04-27, researcher-8) — Metadata Reconciliation
- **Mode**: REVISIT (RICH knowledge score 25); Lean files already current
- **Outcome**: Metadata audit — synced stale tracking files with the
  actual state of the Lean code

#### Audit Findings
- `state.md` was still `Phase: NEW`, iteration 1, attempts 0 — never
  updated despite two completed sessions
- `src/data/research/problems/erdos-863.json` had `phase: "ORIENT"`,
  empty `knownResults`/`whyMatters`, self-referential `relatedProofs`
  (listed `erdos-863` as related to itself), empty `references`, and
  `builtItems` missing the Sidon-equivalence theorem and definition
- The companion was reported with "5 sorry targets" but all targets
  have full proofs; the JSON's `sorryCount: 1` for Aristotle file is
  due to the known `grep -c "sorry"` overcount from a comment line

#### What I Did
1. Updated `src/data/research/problems/erdos-863.json`:
   - `phase: ORIENT → ACT`, currentState refreshed
   - `progressSummary`: revised to reflect 12 main theorems + 5 companion
     theorems + 0 actual sorries
   - `builtItems`: added `IsSidonSetLocal` def and `isB2r_one_iff_sidon`,
     clarified Aristotle companion status
   - `knownResults`: filled in Sidon classical, Cilleruelo-Ruzsa-Trujillo
     bound, Ruzsa cᵣ ~ √r; listed three open conjectures
   - `whyMatters`: filled in (was empty)
   - `relatedProofs`: removed self-reference, added erdos-340/862/864/530
   - `references`: added papers and erdosproblems URL
   - `nextSteps`: replaced with concrete next-iteration targets (cross-file
     Sidon bridge, B₂[r] generalization of counting bound, maxB2rSize
     monotonicity)
   - `lastUpdate`: 2026-03-13 → 2026-04-27
2. Rewrote `state.md` to reflect ACT phase
3. Added this session note

#### No Lean Code Changes
Disk at 97% capacity (~498MB free), so per
`feedback_disk_full_blocks_research.md` and
`feedback_researcher_commit_immediately.md` rules, no speculative new
Lean code without ability to build it.

---

*Generated from erdosproblems.com on 2026-01-15, updated 2026-03-27 and
2026-04-27.*
