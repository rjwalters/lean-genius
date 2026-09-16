# Arbitrary-valuation sequential counter converse

The four implication schemas constrain arbitrary auxiliary propositions. A chain of t+1 true input positions forces the overflow contradiction; choosing an ordered subset gives the full cardinality bound. Boolean prefix-count and complement lower-bound corollaries connect this to existing semantics. Requires 0 < t; no n > t premise is needed (the small n case follows from cardinality).

Native Lean source compile and four axiom audits pass. Only propext, Classical.choice and Quot.sound occur. Concrete DIMACS clause interpretation, count flattening, cube UNSAT and H1 exclusion remain separate obligations.
