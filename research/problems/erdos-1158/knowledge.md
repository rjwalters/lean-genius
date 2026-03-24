# Erdős #1158 - Knowledge Base

## Problem Statement

Is it true that ex_t(n, K_t(r)) ≥ n^{t - r^{1-t} - o(1)}?

Where K_t(r) is the complete t-partite t-uniform hypergraph with r vertices per class,
and ex_t(n, K_t(r)) is the hypergraph Turán number.

## Status

**Erdős Database Status**: OPEN
**Phase**: ACT (initial formalization complete)

**Tractability Score**: 6/10
**Aristotle Suitable**: No (open conjecture, deep axioms)

## Tags

- erdos
- hypergraphs
- extremal-combinatorics
- turan-type

## Related Problems

- Problem #714 (t=2 specialization: Zarankiewicz problem)
- Problem #768 (K_{2,2} = C_4 case)
- Problem #2000
- Problem #83

## References

- Erdős (1964): On extremal problems of graphs and generalized graphs [Er64f]
- Verstraëte survey [Va99, 3.65]

## Sessions

### Session 1 (2026-03-23, researcher-5)

**What Was Done:**
- Fetched full problem statement from erdosproblems.com
- Created Lean 4 formalization: `proofs/Proofs/Erdos1158Problem.lean` (279 lines)
- Created gallery integration: `src/data/proofs/erdos-1158/`
- Defined: UniformHypergraph, containsKtr, isKtrFree, exHypergraph, hypergraphExponent
- Stated conjecture with ε-formulation (erdos1158Conjecture)
- Axiomatized: upper bound (Erdős 1964), weaker lower bound, stepping-up lemma, known t=2 cases
- Proved: erdos_1158_known_cases (combines t=2 r=2,3 results)

**Key Insights:**
- The conjecture generalizes Erdős #714 (Zarankiewicz problem) to t-uniform hypergraphs
- For t=2, the exponent t - r^{1-t} = 2 - 1/r recovers the KST exponent
- The gap is in the constant: known lower bound has C·r^{1-t} with C > 1, conjecture needs C = 1
- Stepping-up lemma (Erdős-Hajnal) converts (t-1)-uniform bounds to t-uniform but compounds the constant gap
- Only algebraic constructions (projective planes, generalized hexagons) achieve tight bounds

**Axiom Classification:**
1. `erdos_upper_bound` — Deep (double-counting generalization of KST)
2. `erdos_lower_bound` — Deep (probabilistic method argument)
3. `conjecture_t2_r2` — Known result (projective planes), deep construction
4. `conjecture_t2_r3` — Known result (Brown 1966), deep construction
5. `stepping_up_lemma` — Deep (Erdős-Hajnal combinatorial construction)

**Next Steps:**
- Try to prove exponent_t2 theorem (currently has sorry for rpow simplification)
- Consider creating Aristotle companion file for routine lemmas
- Potential: formalize the t=2 reduction more explicitly connecting to Erdos714 namespace

---

*Updated by researcher-5 on 2026-03-23*
