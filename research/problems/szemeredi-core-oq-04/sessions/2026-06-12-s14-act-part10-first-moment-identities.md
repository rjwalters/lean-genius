# S14 ACT — Part 10: edge-count primitives + first-moment identities

**Slug**: `szemeredi-core-oq-04` (Algorithmic Szemerédi, ADLRY 1994)
**Researcher**: researcher-1
**Date**: 2026-06-12
**Iteration**: 21 (author-time; parallel with in-flight PRs #22879 and
#22890 — merge-order monotone renumbering applies at the next
STATE-SYNC, per the Iter 14/16 precedent)
**Mode**: ACT (Lean edits, Docker-verified)

## Why this shape (G7 race adaptation)

The Iter 20 ACT plan ("paste Iter 17 §6 Part 9 first-moment skeleton +
Iter 19 §3 Route A helper, 3-5 transient sorries") was **overtaken in
flight**: at session pre-flight two open PRs already occupied the
combinatorial layer of the second-moment route —

* **PR #22879** (researcher-?, 2026-06-12T08:03Z): Part 8b
  `three_quarters_good_of_markov` — step-3 counting (A-side 3/4
  domination given the Markov bound). Touches the slug Lean file +
  `state.md` + JSON.
* **PR #22890** (researcher-?, 2026-06-12T12:13Z): Part 9 Markov
  consequences — `eps_mul_A_bad_card_le_sum_vertexBias`,
  `A_bad_card_le_of_sum_vertexBias_le` + B-side duals, all conditional
  on a moment-sum hypothesis `∑ vertexBias ≤ eps²·|A|`. Touches the
  slug Lean file only.

G7 (no overlapping open PRs) is therefore RED for the *planned* paste —
the Iter 17 §6 skeleton's `A_bad_card_first_moment_markov` is now
materially covered by #22890, and pasting it would duplicate content.
Instead of a doc-only PREP (the 21st), this session ships the
**upstream identity layer** that neither PR touches and that the open
analytic step-2 estimate must be proved against. All new declarations
are **sorry-free** (no transient-sorry budget consumed).

## What shipped (Part 10, `proofs/Proofs/SzemerediCoreOQ04.lean`)

16 new declarations appended as Part 10 (after Part 8, before
`end Szemeredi.OQ04`):

1. `edgeCount` (def) — ℕ-valued, guard-free numerator of
   `edgeDensity`: `((A.product B).filter (fun p => G.Adj p.1 p.2)).card`.
2. `edgeDensity_eq_edgeCount` — density = edgeCount/(|A|·|B|) away
   from the degenerate case.
3. `edgeDensity_empty_left` / `edgeDensity_empty_right` — guard
   collapse lemmas (with `omit [Fintype V] [DecidableEq V]`).
4. `edgeCount_eq_sum_right` — fiberwise degree decomposition
   `e(A,B) = ∑_{b∈B} deg_A(b)` via
   `Finset.card_eq_sum_card_fiberwise` + `Finset.card_bij'`.
5. `edgeCount_eq_sum_left` — A-side dual.
6. `edgeCount_singleton_right` / `edgeCount_singleton_left` — degree
   specializations.
7. `edgeCount_filter_add_filter_neg` — **Route A predicate split**
   (the Iter 19 §3 recommendation, discharged): splitting `B` by any
   decidable predicate splits the edge count additively. One-line from
   the fiberwise decomposition + `Finset.sum_filter_add_sum_filter_not`
   — even cheaper than the ~8-10 LOC interedges route estimated in
   Iter 19 §3.
8. `edgeDensity_singleton_right` / `edgeDensity_singleton_left` —
   singleton densities as degree ratios.
9. `sum_edgeDensity_singleton_right` / `sum_edgeDensity_singleton_left`
   — **first-moment identities** `∑_{b∈B} d(A,{b}) = d(A,B)·|B|` and
   the A-side dual. Unconditional (empty cases included).
10. `sum_edgeDensity_singleton_sub_left` / `_right` — **signed first
    moment vanishes**: `∑_{a∈A} (d({a},B) − d(A,B)) = 0`.
11. `sum_vertexBias_eq_two_mul_pos_part` /
    `sum_vertexBias_B_eq_two_mul_pos_part` — **positive-part doubling**:
    `∑_{a∈A} vertexBias = 2·∑_{a : d({a},B) ≥ d(A,B)} (d({a},B) − d(A,B))`.

## Mathematical significance (honest assessment)

Routine identities, not deep content — but load-bearing structure:

* Items 9-10 explain *why* the open step-2 estimate is irreducibly
  about absolute deviations: the signed first moment is identically
  zero, so no signed shortcut to the Markov input exists.
* Item 11 is the canonical reduction of the absolute first moment to a
  **one-sided** sum over a single subset `A⁺ ⊆ A`. The open analytic
  estimate `∑ vertexBias ≤ f(eps)·|A|` (which feeds #22890's
  `A_bad_card_le_of_sum_vertexBias_le`) is now equivalent to bounding
  `∑_{a∈A⁺} (d({a},B) − d(A,B)) ≤ f(eps)·|A|/2`. **Caveat recorded**:
  `A⁺` is *not* a member of `witnessFamilyB` (the grid contains only
  neighbour patterns `B∩N(a)` / `B\N(a)`), so the surrogate hypothesis
  does not apply to it directly — the genuine ADLRY route converts grid
  control into degree-variance control via the path-counting identity
  `∑_b deg_A(b)² = ∑_a e(A, B∩N(a))`, which is the natural **next
  ACT target** now that `edgeCount_eq_sum_*` and
  `edgeCount_singleton_*` exist to state it cleanly.
* Item 7 closes the Iter 19 §3 pre-paste ask (Route A helper) in
  degree-sum form rather than interedges form.

## Conflict notes for the next STATE-SYNC

* All three 2026-06-12 PRs (this one, #22879, #22890) append to the
  tail region of `SzemerediCoreOQ04.lean`; textual merge conflicts at
  the insertion point are expected and resolve by concatenation
  (keep all three hunks; Part ordering 8b / 9 / 10 in any order before
  `end Szemeredi.OQ04`). Content is pairwise disjoint — no duplicate
  declaration names.
* This PR and #22879 both touch `state.md` + the slug JSON; resolve by
  keeping both narrative entries and taking the higher iteration
  counter.

## Build verification

`./proofs/scripts/docker-build.sh Proofs.SzemerediCoreOQ04`:
* Attempt 1: 4 errors — `simp only [Finset.mem_product]` cannot match
  `A.product B` syntactically (the lemma is stated for `×ˢ`; the
  product appears as a raw `Finset.product` application here, and simp
  left `Quot.lift`-shaped membership). Fixed by replacing the
  `simp`/`rcases` bullets in the two `card_bij'` blocks with term-style
  `Finset.mem_product.mp/.mpr` applications, which unify up to defeq
  (the neighbouring `hmaps` blocks compiled this way on attempt 1).
* Attempt 2: 4 errors — (a) `omit ... in` must precede the docstring,
  not sit between docstring and `lemma`; (b) `rw [← hpb]` in the
  `card_bij'` left-inverse bullets hit a motive-not-type-correct
  failure (the unreduced goal contains `hp`, whose type mentions the
  rewrite target `b`). Fixed by `show (p.1, b) = p` (beta-reduce the
  goal, dropping `hp`) before the rewrite.
* Attempt 3: **green — 7744 jobs, 0 errors**, sorry warnings exactly
  the 2 pre-existing (lines 284/824).

Sorry inventory unchanged: **2** (line 291 archival-unprovable
one-sided + line ~831 deferred-provable symmetric); **0 axioms**;
0 assumption-encoding structure fields. File grows 1054 → ~1390 LOC.

## Next steps

1. **Path-counting identity** (natural S15 ACT):
   `∑_{b∈B} deg_A(b)² = ∑_{a∈A} edgeCount G A (B.filter (G.Adj a ·))`
   — both sides now stateable with Part 10 vocabulary. This is the
   bridge from grid-density control (`IsWitnessRegular`) to B-side
   degree variance, i.e. the genuine step-2 content.
2. Step-2 second-moment estimate
   `∑_{b∈B} vertexBias_B² ≤ 2·eps·|B|` from `IsWitnessRegular` via
   (1) + `density_bound` on `B∩N(a)` members + trivial bound on
   sub-threshold patterns.
3. Assembly: feed (2) into #22890's Markov consequences and #22879's
   3/4-domination, then the final conjoint triangle step at
   `_small_eps` (~831).
