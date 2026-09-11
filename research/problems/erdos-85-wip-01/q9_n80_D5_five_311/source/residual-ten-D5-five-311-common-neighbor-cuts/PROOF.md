# Common-neighbor capacity cuts for the91 open low-edge models

Input: every nonnegative or UNKNOWN case from2480, namely90 rational-witness models and the previously unresolved root46. Retain every original variable, bound, and degree/support/defect/two-edge-C4 constraint. The forced70-vertex partial graph is unchanged.

For any vertex pair(i,j), the number of common neighbors in a full C4-free graph is at most one. Classify possible middle vertices into forced-forced paths (count c), forced-variable paths (indicator x_e), and variable-variable paths (indicator x_e*x_f for binary edge variables). Each selected variable-variable path satisfies x_e*x_f>=x_e+x_f-1. Dropping unselected paths, which contribute nonnegatively, therefore gives the valid inequality

 sum(forced-variable edge variables) + sum(selected two-variable edge variables) <= 1-c + number(selected paths).

This aggregates whole families of conflicting paths, and can be stronger than separate two-edge conflicts. All fixed-variable paths are included. Where an old rational witness exists, two-variable paths are selected when their approximate edge sum exceeds1 by1e-9; the threshold only chooses a subset of valid inequalities and never decides infeasibility. Every subset yields a valid cut independently of the witness or rounding. For the old UNKNOWN no such witness is used, so only the unconditional fixed-variable path cuts are added. The model is still a relaxation; not every common-neighbor inequality is imposed.

The complete model construction processes91 cases and adds121859 cuts in2.233033 seconds under its original30-second cap. The separate allocation run finishes in25.173048 seconds, below its original30-second cap. Exact Fraction checks establish47 Farkas contradictions and24 rational witnesses. Twenty additional numerical-status0 solutions fail exact rational reconstruction and remain UNKNOWN, so the overall exact-result status is INCOMPLETE. No cap was reached, and no numerical-only negative is used.

The prior UNKNOWN root46 (source545, source assignment0, class6) now has an exact Farkas contradiction with right side-1/9 in this stronger model. Its original2480 UNKNOWN receipt remains unchanged. Combining the3 previous exact exclusions with these47 leaves44 original cases open:24 exact rational positives and20 current UNKNOWNs. Rational feasibility does not establish integer edges or graph realizations.

Model root identifiers are inherited unchanged from2480. The new result source_assignment field always preserves the source index separately from assignment, the rational vector on positive records. The input case-index.json and models give exact source-key coverage. No fullcase, global Erdős85, or Lean theorem is claimed.
