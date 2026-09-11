# Exact shared-color linear screen on1284 permutation representatives

Input: all1284 representatives submitted in2200. Coverage of the original attached-permutation class is conditional on that symmetry-cover review. This stage checks every supplied representative and records a verifiable outcome.

For each representative, retain all243 ternary color words whose contingency entries have positive capacity at every attached pair. Introduce a nonnegative real multiplicity for each supported word. Require five433 coordinate margins and all pair-contingency upper bounds from2190. Omit binary/distinctness constraints, Hamming restrictions, b(w), Q and matching phases: this is a relaxation of actual residual colorings.

Original aggregate60second cap, no retry. All1284 supplied cases processed in2.757seconds:708 EXACT_INFEASIBLE,576 EXACT_FRACTIONAL_FEASIBLE; no UNKNOWN/unvisited. Negative records give integer Farkas multipliers on the120 inequalities (30 signed margin rows,90 pair rows). Their weighted coefficients are nonnegative and their weighted RHS is negative. Positive records give a common denominator and integer word weights satisfying all inequalities exactly. A fractional positive is not a graph witness or even an integer coloring.

run.py uses a numerical LP engine only to discover candidates, reconstructs rational values and checks exact arithmetic before classifying them. Independently, verify.py uses only the standard library: decodes the permutations, reconstructs all supported words and120 constraints by counting explicit middle-group paths, checks every saved integer certificate/witness, and checks equality of the supplied representative sets. All1284 verified in0.341seconds. It does not independently verify the preceding symmetry cover.

Word ids are lexicographic indices in{0,1,2}^5. Certificate row ids follow verify.py labels. The complete negative certificates and positive fractional witnesses are saved in receipts.jsonl. A future integer/Q stage may use the576 positive representative codes; none of these outcomes settles the full N80/F5 graph class.
