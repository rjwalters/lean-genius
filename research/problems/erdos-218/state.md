# Current State

**Phase**: AXIOMATIZED-INFRASTRUCTURE-COMPLETE / CONJECTURES-OPEN (state.md reset from seeker-init stub 2026-01-12 → reality 2026-05-13)
**Since**: 2026-05-13T12:00:00Z (state.md sync; Lean infrastructure progressed via PRs #5383, #7141, #7773, #7795, #8552 between 2026-03-24 and 2026-03-30)
**Iteration**: 7 (post-PR-#7141 STATE-SYNC; doc-only)

## Current Focus

**Erdős Problem #218: Prime Gap Densities** is one of Erdős's open conjectures (Tao: *"looks difficult"*). The slug's Lean formalization (`proofs/Proofs/Erdos218Problem.lean`, 418 LOC, 22 theorems/lemmas, 12 definitions per JSON `leanFiles[]`) builds the full surrounding infrastructure (prime enumeration, gap function, natural-density definition, gap sets, AP equivalence) with **0 sorries** and **2 axioms** — the two axioms are *the* open conjectures themselves (`erdos_218a`, `erdos_218b`), not proof gaps in supporting lemmas.

## What Is Axiomatized vs Proved

### Axiomatized (the open conjectures themselves)

| Axiom | Statement | Status |
|-------|-----------|--------|
| `erdos_218a` | `HasDensity gapIncreasingSet (1/2)` — density of `{n : d_{n+1} ≥ d_n}` is 1/2 | OPEN (Erdős Conjecture 218a) |
| `erdos_218b` | `HasDensity gapDecreasingSet (1/2)` — density of `{n : d_{n+1} ≤ d_n}` is 1/2 | OPEN (Erdős Conjecture 218b) |

Note: Erdős Conjecture 218c (`gapEqualSet.Infinite` — infinitely many `n` with `d_n = d_{n+1}`) is mentioned in the docstring but is NOT currently stated as an axiom. It is equivalent to "infinitely many 3-term APs of consecutive primes" (proved equivalent in the Lean file via `gapEqual_iff_ap` + `infinitely_many_3ap_from_218c`); it is implied by Green-Tao only modulo the consecutive-primes restriction.

### Proved (everything else)

| Theorem | Statement | Approach |
|---------|-----------|----------|
| `nthPrime_prime`, `_strictMono`, `_zero/one/two/three/four` | Prime enumeration via `Nat.nth` | Direct from Mathlib `Nat.nth` API + `decide`/`Nat.nth_count` for concrete values |
| `primeGap_zero/one/two/three`, `primeGap_pos` | `primeGap n := nthPrime (n+1) - nthPrime n` is positive | `unfold` + `rw` from `nthPrime_*` values |
| `hasDensity_iff_upper_lower` | `HasDensity S d ↔ limsup = d ∧ liminf = d` | Standard limit ↔ limsup ∧ liminf characterization |
| `zero_mem_gapIncreasingSet` | `0 ∈ gapIncreasingSet` (primeGap 0 = 1 ≤ primeGap 1 = 2) | Direct from `primeGap_zero` + `primeGap_one` |
| `one_mem_gapEqualSet` | `1 ∈ gapEqualSet` (primeGap 1 = primeGap 2 = 2) | Direct from `primeGap_one` + `primeGap_two` |
| `gapEqualSet_eq_inter` | `gapEqualSet = gapIncreasingSet ∩ gapDecreasingSet` | `ext` + `le_antisymm` |
| `gapEqual_iff_ap` | `n ∈ gapEqualSet ↔ threePrimesInAP n` | `omega` on ℕ subtraction with `strictMono` hypotheses |
| `infinitely_many_3ap_from_218c` | `gapEqualSet.Infinite → apTriples.Infinite` | `convert` via `gapEqual_iff_ap` |
| `example_ap_1`, `ap_357` | `1 ∈ gapEqualSet`, `1 ∈ apTriples` (primes 3,5,7 form AP) | Direct from `one_mem_gapEqualSet` + `gapEqual_iff_ap` |
| `infinite_of_hasDensity_pos` (private) | `HasDensity S d ∧ d > 0 → S.Infinite` | Squeeze: finite ⇒ counting function bounded ⇒ ratio → 0; contradicts `d > 0` via `tendsto_nhds_unique` |
| `gapIncreasingSet_infinite`, `_decreasingSet_infinite` | Both gap-comparison sets are infinite | Apply `infinite_of_hasDensity_pos` to `erdos_218a/b` |
| `partition` | `strictlyIncreasing ∪ strictlyDecreasing ∪ gapEqualSet = univ` | Trichotomy on `<`/`>`/`=` |
| `erdos_218_summary` | Composite summary theorem | Composes the above |

## Per-File Inventory

| File | LOC | Sorries | Axioms | Theorems | Defs | Role |
|------|-----|---------|--------|----------|------|------|
| `Erdos218Problem.lean` | 418 | 0 | 2 | 22 | 12 | Main + only file; infrastructure + 2 open-conjecture axioms |

`meta.json`: `status: axiomatized`, `badge: axiom`, `sorries: 0`, `axiomCount: 2` — all already accurate for the current Lean state.

(Note: JSON `leanFiles[].lineCount: 419` is 1 line off from actual `wc -l` count of 418 — minor drift, not addressed in this STATE-SYNC as it does not affect any consumer.)

## What Has Already Been Eliminated (PR history)

The slug saw substantial axiom-elimination work over ~6 days in late March 2026:

| PR | Date | Effect |
|----|------|--------|
| #5383 | 2026-03-24 | erdos-218 + erdos-738 + erdos-854 — eliminate 22 axioms total (combined slug PR) |
| #7141 | 2026-03-27 | erdos-218 — eliminate 14 axioms via Mathlib `Nat.nth` definitions |
| #7773 | 2026-03-29 | erdos-218 — prove `hasDensity_iff_upper_lower` (8 → 7 axioms) |
| #7795 | 2026-03-29 | meta audit: sorry 0→1, axiom 7→5 |
| #8552 | 2026-03-30 | meta audit: axiomCount=2 not 5, sorries=0 not 1 |
| (final) | now | 2 axioms = 2 open Erdős conjectures (lower bound) |

The remaining 2 axioms are at the **theoretical floor** for this slug: they encode the open mathematical conjectures and cannot be eliminated without resolving the conjectures themselves.

## Active Approach

None pending. Infrastructure is complete and the 2 axioms ARE the open mathematical content; there is no Lean engineering left for the slug as currently scoped.

## Blockers

The two remaining axioms encode genuinely open mathematical problems:

1. **`erdos_218a`** (density of gap-increasing set = 1/2): Erdős's original conjecture from [Er55c], [Er57]. Tao characterized the problem as *"looks difficult"*. No known analytic method to obtain density 1/2 (vs. just "infinite", which is already proved).
2. **`erdos_218b`** (density of gap-decreasing set = 1/2): Same status — open conjecture, no known proof. NOT the set-theoretic complement of 218a (both allow equality at `gapEqualSet`).

Mathlib has no bearer for either conjecture.

## Next Action

Three viable forward levers — but all are research-grade and unlikely to be discharged by routine ACT iterations:

1. **Lever A — Add `erdos_218c` as an explicit axiom + Green-Tao implication chain**: Currently `gapEqualSet.Infinite` is mentioned in docstrings but not formally axiomatized. Adding `axiom erdos_218c : gapEqualSet.Infinite` would expose the AP-of-3-consecutive-primes question explicitly, even though Green-Tao does NOT directly imply it (Green-Tao gives ALL primes contain long APs, not specifically *consecutive* primes). Worth ~20 LOC of explicit statement + connection. Note: this would *increase* axiom count from 2 → 3; weigh against the gain of explicit statement.
2. **Lever B — Partial density bounds**: Prove `0 < density(gapIncreasingSet) < 1` (positive lower bound, strict upper bound) without claiming `= 1/2`. Some recent analytic work (post-Maynard) gives weak quantitative bounds. ~100-200 LOC, would replace `erdos_218a` with a quantitative range, leaving the exact `= 1/2` as a tightened axiom. Major effort with unclear Mathlib bearer.
3. **Lever C — Treat as gallery showcase**: Accept axiomatized status (this slug is correctly tagged `tier: A`, `significance: 7-10`). Focus efforts on related slugs (`erdos-2`, `erdos-21`, sibling problems) instead of pushing on the conjectures themselves.

For routine queue management, **Lever C is the right default**: this slug is in its terminal Lean state until a major number-theory breakthrough lands.

## Attempt Counts

- Total attempts: 6 (multiple PRs from 2026-01 through 2026-03; this STATE-SYNC = doc-only)
- Current approach attempts: 0 (no active research push)
- Approaches tried: 1 (Mathlib `Nat.nth`-based infrastructure — succeeded; reached 2-axiom floor)

## Honesty Block

- **The slug is NOT solved**: Erdős's two density conjectures (`erdos_218a`, `erdos_218b`) remain genuinely open in mathematics. The 2 axioms in the Lean file are honest placeholders for the unsolved conjectures.
- **The Lean infrastructure IS complete**: All supporting lemmas (prime enumeration, gap function, density characterization, gap sets, AP equivalence, infinite-density-implies-infinite-set, summary theorem) are proved with 0 sorries.
- **`meta.status: axiomatized` is correct** per `CLAUDE.md`'s axiom integrity policy: open conjectures must be `axiomatized` (not `verified`, not `conditional`). The 2 axioms in this file ARE assumptions encoded as axioms — they would need to be eliminated by a major mathematical advance, not engineering.
- **`badge: axiom` is correct**: the Lean file declares 2 axioms, and `axiomCount: 2` in the JSON `leanFiles[]` entry matches.
- **The `progressSummary` in the JSON already says "COMPLETED: Proved infinite_of_hasDensity_pos"** — that referred to the most recent engineering completion (eliminating the last fixable axiom). It does NOT mean the slug overall is solved. This STATE-SYNC PR clarifies that distinction.
- This is a doc-only STATE-SYNC: no Lean files, no `meta.json` counts, no annotations were touched. The 2-axiom Lean state is unchanged.

## References

- `proofs/Proofs/Erdos218Problem.lean` — Lean source (latest non-trivial PRs #7141, #7773, all in 2026-03)
- `src/data/research/problems/erdos-218.json` — knowledge graph (this STATE-SYNC updates `currentState` block + `lastUpdate`; refreshes `knowledge.insights` last-line axiom count from 7 → 2)
- Erdős references: [Er55c], [Er57], [Er61], [Er65b], [Er85c]
- OEIS: A333230 (gap-increasing indices), A333231 (gap-decreasing), A064113 (equal-gap)
- Source: https://erdosproblems.com/218
- Related: Green-Tao (2008) — `Mathlib.NumberTheory.LSeries.PrimesInAP` and related (does NOT directly imply Erdős 218c due to "consecutive primes" restriction)
- Sibling slugs: `erdos-2`, `erdos-21`
