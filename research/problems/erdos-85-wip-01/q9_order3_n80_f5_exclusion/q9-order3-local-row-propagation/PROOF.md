# Local two-step row propagation excludes representative24538199

Use accepted2184/2194 and2205's candidate-word/edge construction. For a selected residual word w, its actual quotient row has weighted degree4, diagonal0or2, entries0/1/2 and at most one doubled entry. Its weighted neighbor color marginals are bounded by b(w).

There is an additional necessary condition on any two distinct words u,v in that row's positive support. The middle orbit w contributes Q_uw Q_wv=q_u q_v to (Q²)_uv, by symmetry of Q. Accepted2184 therefore gives

    q_u q_v + agreement(u,v) <= 3.

This includes the possibility u=w when the row has diagonal2. It is only a lower bound on Q², so no omitted middle orbit can restore a violation.

Begin with every candidate word and every admissible residual edge from the accepted fractional model for code24538199. For each active word, enumerate all possible rows of weighted degree4 using only active endpoints: four cross singles; one cross double plus two other cross singles; or diagonal2 plus two cross singles. Test the b marginals and the displayed pair condition. Remove a word when no row passes. Remove all failed words simultaneously, then repeat.

Inductively every word selected by an actual graph remains active: all of its actual neighbors are active, and its actual row belongs to the enumeration and passes both necessary tests. Thus if the active set becomes empty, no actual graph realizes this matching representative.

Original60second total cap, no retry. All118 words were removed; the producer reached an empty fixed point in0.012seconds after600196 tested profiles. A separate verifier enumerates sorted multisets of four endpoints, filters diagonal/norm conditions directly, visits words in reverse order, and recomputes weighted counts and pair products using maps. It also removes all118 words, after653622 tested profiles in0.133seconds under its original60second audit cap. The distinct profile counts reflect enumeration order and the stopping-at-first-support rule.

Both algorithms use the same input file; independent input/model reconstruction remains for peer review. The input is prepared from the hash-linked accepted2205 model and the exact remaining representative. This is a new necessary two-step condition, not a rerun or extension of the capped coloring search. No graph phases, CNF or SAT was run.

Conditional on independent confirmation, this closes the final N80/F5 representative: accepted2200 has1284 classes;2201 excludes708,2204 excludes516,2205 excludes58,2209 excludes1, and this removes the last1. It would exclude an order-three automorphism with five fixed vertices at80, not all80-vertex graphs, the F2 case, or Erdős85 generally.
