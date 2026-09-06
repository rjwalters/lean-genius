# Weight-three dense triangle-free classification: threshold audit

Node: A.5.3 / A-REG-NONBIP / mixed weight-three triangle-free defect.
Status: literature applicability audit, not a branch exclusion.
Checked 2026-09-06 by codex-sol-2.

The defect component has order `n=3q` and regular degree `r=q-1`.
The question is whether dense triangle-free classification supplies the
missing exhaustive family after the interval and Clebsch examples.

## The published thresholds do not cover these parameters

Brandt–Thomassé, *Dense triangle-free graphs are four-colorable: A solution
to the Erdős-Simonovits problem*, Corollary 4.1 (PDF p.4), classifies
twin-free maximal triangle-free weighted graphs with minimum weighted
degree **strictly greater than 1/3** as Andrásfai or Vega graphs.
Corollary 4.2 gives four-colorability above `n/3` for ordinary graphs.
Our uniform weights give `r/n=1/3-1/(3q)`, below the threshold.
[Primary manuscript](https://perso.ens-lyon.fr/stephan.thomasse/liste/vega11.pdf).

Wang–Yang–Zhao, *Triangle-free Graphs with Large Minimum Common Degree*,
arXiv:2408.05547v1, requires minimum common degree over distinct nonadjacent
pairs strictly greater than `floor(n/8)` to obtain a homomorphism to C5.
There is no such lower bound among our established coupled hypotheses.
[Primary paper and abstract](https://arxiv.org/abs/2408.05547v1).

## Two apparent repairs fail before any search

**Reweighting cannot improve a regular graph's minimum weighted degree.**
For any nonnegative vertex weights `w` summing to one in an r-regular
graph with adjacency D,

```text
sum_x (D w)_x = sum_y r*w_y = r,
min_x (D w)_x <= r/n.
```

Uniform weights attain the bound. Thus no choice of weights on this fixed
D reaches 1/3, much less exceeds it. Aggregating weights over twin classes
does not escape the argument: every weight on the quotient lifts to a
weight on the original graph with identical weighted neighborhood sums.
This is our elementary deduction, not an additional classification theorem.

**Maximal triangle-free completion need not add any edge.** The existing
Clebsch blow-up `D=C tensor J3` on 48 vertices is already maximal
triangle-free. Its distinct nonadjacent pairs have common-neighbor counts
15 (48 pairs within fibers) or 6 (720 pairs between nonadjacent base
vertices). Every missing edge therefore creates a triangle. The minimum
common degree is exactly `48/8=6`, so it also misses the strict common-degree
threshold. This counterexample satisfies the internal cubic-H conditions
recorded in the Clebsch control; it does not satisfy the full incidence Gram.
It refutes these repairs from D/internal data, not a possible theorem using B.

The calculation is reproducible with the standard library:

```python
from collections import Counter
S = {1, 2, 4, 8, 15}
N = [{y for y in range(48) if (x//3) ^ (y//3) in S}
     for x in range(48)]
assert {len(a) for a in N} == {15}
assert all(not (N[x] & N[y]) for x in range(48) for y in N[x])
counts = Counter(len(N[x] & N[y])
                 for x in range(48) for y in range(x+1, 48)
                 if y not in N[x])
assert counts == {6: 720, 15: 48}
```

## A bounded-exception statement survives, but is not a bridge yet

The degree-sum argument behind Brandt–Thomassé Lemma 3 (PDF p.6)
has a precise below-threshold remainder. If an induced C6, denoted Z,
has no vertex adjacent to three or more of its vertices, let
`t_x=|N_D(x) intersect Z|`. Then `0<=t_x<=2` and

```text
sum_x (2-t_x) = 2*(3q) - 6*(q-1) = 6.
```

Consequently at most six vertices have fewer than two neighbors on Z;
writing a_i for the number with t_x=i gives `2*a_0+a_1=6`.
All other vertices have one of nine independent two-element neighborhood
types on C6. Equal types do not imply twins or equitability. This is a
conditional structure with bounded exceptions, not proof that such a C6
exists, nor a classification of its remaining edges. A bounded check of
all six-subsets of the 16-vertex Clebsch base found no induced C6 without
a triple dominator; it supplies no universal C6-existence statement.

Decision: stop the direct classification-import route. A useful next theorem
must exploit the same H and actual incidence B, or prove a new structural
result at `n/3-1`; reweighting, maximal completion, and the cited degree
thresholds alone do not supply the missing link. No Lean wrapper or further
fixed-q enumeration is called for by this audit.
