# Exact joint rows when the high graph is empty, D5/s5

Inputs: the complete601 representative matching cases in2469, using2467/2468's highmatching and symmetry covers. Exactly24 surviving cases have empty high graph. (The highmatching-domain filters remove any other empty-high cases.) Each of the ten high vertices has five low neighbors, giving50 incidences. There are50 low vertices and each can have at most one high neighbor by its endpoint budget. Therefore every low vertex has exactly one high neighbor and zero residual defect neighbors.

All residual defect columns and the entire RR commutator must consequently be supplied by the ten high rows. For each of five high involution-orbit representatives, use its complete Q-domain from2467 and its involution image. Each choice contributes an integer vector of ten column counts followed by the45 off-diagonal commutator entries. The target is(q,Dcomm). Every actual assignment selects one vector from each of the five domains summing exactly to this target.

The meet-in-the-middle computation records all two-domain sums and their choices, then enumerates every three-domain sum and looks up its target complement. It preserves all choices colliding at a sum, so its output is exhaustive. This is a new exact equality model for the empty-high subcase, not a resumed capped product search.

The original30-second computation completes all24 cases in0.994796 seconds, covering72973467 implicit full products. Five cases have no assignments; nineteen cases have59 assignments total. For every output assignment, direct reconstruction also checks that high-low demand at each residual support exactly equals the number of low vertices there. These are necessary defect assignments, not graph realizations.

No graph solver, global Erdős85 result, or Lean theorem is claimed. The downstream low-neighbor parity check handles the59 outputs separately.
