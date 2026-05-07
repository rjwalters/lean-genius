# Research State: birthday-problem-oq-03-oq-01-oq-02-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-08T00:15:00Z
**Iteration**: 6

## Current Focus
Lemmas A and B proved; Lemma C remains the only axiom. Session 6 added
`card_funs_shared_triple` — the cardinality foundation for the Markov-bound
half of the Poisson sandwich for Lemma C.

## Active Approach
Decomposition strategy:
- **Lemma A** `lambda_tendsto` (DONE, Session 4): `λ(d) := C(⌊c·d^(2/3)⌋, 3)/d² → c³/6`.
- **Lemma B** `exp_lambda_tendsto` (DONE, Session 4): `exp(−λ(d)) → exp(−c³/6)`.
- **Lemma C** `p_no_triple_tendsto` (OPEN AXIOM): `P_no_triple(n d, d) → exp(−c³/6)`.
- **Foundation for Lemma C** (Session 6): `card_funs_shared_triple` —
  `|{f : Fin n → Fin d | f i = f j ∧ f j = f k}| = d^(n-2)` for distinct i,j,k.
  Generalizes `card_funs_shared_birthday` (n=2 case). Foundation for the
  Markov bound `P(no triple) ≥ 1 - C(n,3)/d²` (the lower half of the Poisson
  sandwich).

## Attempt Count
- Total attempts: 6 (Sessions 1–6)
- Current approach attempts: 1 (Session 6 added cardinality foundation)
- Approaches tried: 2 (Chen-Stein → BLOCKED; method-of-moments → INCREMENTAL progress)

## Blockers
- Docker build under heavy contention (4 concurrent containers near memory
  ceiling); push without verification per `feedback_docker_build_io_errors.md`.
- Lemma C still requires Bonferroni or method-of-factorial-moments (~500 lines
  of new probability-theoretic infrastructure). Foundation is now in place;
  next session can attempt the union bound + first-moment inequality.

## Next Action
1. **Markov lower bound**: `P(no triple at n, d) ≥ 1 - C(n,3)/d²` via
   `card_funs_shared_triple` + `Finset.card_biUnion_le` over
   `Finset.powersetCard 3 (Finset.univ : Finset (Fin n))`.
2. **First moment formula**: `Σ_f tripleCount n d f = C(n,3) · d^(n-2)`,
   a corollary of the cardinality formula by Fubini.
3. **Bonferroni upper bound**: `P(no triple) ≤ 1 - C(n,3)/d² + S_2(d)` where
   `S_2(d)` is the second-order overlap sum (decomposes by overlap pattern:
   disjoint pairs O(n^6/d^4), share-1 pairs O(n^5/d^4), share-2 pairs O(n^4/d^3)).
4. **Squeeze**: combining Markov + Bonferroni at threshold scaling yields
   `liminf P ≥ 1 - λ` and `limsup P ≤ 1 - λ + λ²/2 + o(1)`. Iterate Bonferroni
   to higher orders until both bounds match `exp(-λ)`. This is the
   method-of-factorial-moments closure.
