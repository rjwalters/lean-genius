# Selection Report: konigsberg-oq-02-oq-01

**Date**: 2026-04-23
**Seeker Batch**: seeker/batch-selections-2026-04-23
**Pool Status**: 71 available, 2 in-progress (seeker worktree)

## Selected Problem

- **ID**: konigsberg-oq-02-oq-01
- **Name**: Hierholzer's Algorithm: Directed Eulerian Circuit Formalization in Lean 4
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Domain diversity**: Recent selections covered Analysis (L'Hôpital), Economics/Combinatorics (Shapley-Folkman), Number Theory (√2 minpoly), Geometry (Minkowski). Graph Theory is unrepresented — this fills that gap.
2. **EMPTY knowledge tier**: No previous research done; OBSERVE phase starts fresh with high discovery potential.
3. **Tractable extension of gallery work**: `konigsberg` (undirected case) is already in the gallery, providing technique templates and infrastructure.
4. **Concrete construction**: Hierholzer's algorithm is constructive and maps naturally to Lean 4's functional style.

## Rejection Summary

- **Candidates considered**: 71 available in pool
- **Domain skew corrected**: Pool had heavy Number Theory/Geometry bias; Graph Theory selected to diversify
- **Rejected moonshots**: twin-primes, Goldbach, Sophie Germain (tractability 2/10)
- **Confidence**: high (clear domain gap, tractable algorithm proof)

## Related Gallery Proofs

- `konigsberg`: Undirected Eulerian circuit — direct predecessor proof
- `konigsberg-oq-02`: Directed graph degree characterization (sister problem)

## Suggested First Steps

1. **OBSERVE**: Check `Mathlib.Combinatorics.SimpleGraph.Euler` for existing directed graph Eulerian lemmas
2. **ORIENT**: Study the `konigsberg` gallery proof structure and adapt for directed graphs
3. **DECIDE**: Choose between Hierholzer constructive proof vs. induction on edge count

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 71 |
| In Progress | 2 |
| Graduated | 661 |

## Candidate Pool Health

- Pool depth: adequate (71 available >> 15 threshold)
- Domain diversity improved with Graph Theory addition
- Next refresh recommended: 30 minutes (standard interval)

## Initialized

- [x] Research workspace created: `research/problems/konigsberg-oq-02-oq-01/`
- [x] problem.md populated with mathematical context
- [x] Registered in database with status 'available'
- [x] Pool synced (research/candidate-pool.json → .lean/state/candidate-pool.json)
- [ ] Ready for /researcher
