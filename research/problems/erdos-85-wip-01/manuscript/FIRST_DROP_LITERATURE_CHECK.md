# Literature check: would the 48-to-49 result be the first decided drop?

Checked 25 August 2026.  This note distinguishes the Erdős--85 function

\[
F(N)=\min\{d:\text{ every }N\text{-vertex graph of minimum degree }d
\text{ contains }C_4\}
\]

from Boza's Ramsey function
\(r(s)=R(C_4,K_{1,s})\).  The manuscript currently calls the former `f`,
while Boza calls the latter `f`; quotations of numerical values must say
which convention is in use.

## Verdict

If the certificate campaign proves
`minDegreeForC4 48 = 8` and `minDegreeForC4 49 = 7`, it is defensible to
write:

> This is, to our knowledge, the first decided strict drop of the
> Erdős--85 minimum-degree function (on its stated domain \(N\geq4\)).

The qualifier is necessary.  The maintained problem record still labels
Problem 85 open, records no partial solution, and warns that its literature
list may be incomplete.  The present search found no prior decided drop, but
that is not the same as a systematic-review proof of priority.

Do not write that Afzaly--McKay already proved `F(49) = 7`, and do not cite
their 49-vertex records as an upper bound on minimum degree.  Their page
explicitly labels that row as a lower-bound collection rather than an
exhaustive computation.

## Evidence

### 1. Maintained statement and status of Erdős Problem 85

The Erdős Problems record states the problem for \(N\geq4\), defines the
minimum degree that forces a four-cycle, gives its Ramsey reformulation, and
currently marks it open.  It says that no solution or partial solution is
claimed in the comments.

- Thomas Bloom (maintainer), "Erdős Problem #85":
  <https://www.erdosproblems.com/85>

This also removes the apparent boundary counterexample: values at orders
below four are outside the problem's stated domain, so the artificial
transition into `F(4)` is not a prior in-domain drop.

### 2. Boza's current exact-value table

Version 2 of Boza's paper was posted 12 June 2026.  Its table gives

- \(r(35)=42\) and \(r(36)=43\), which correspond to
  \(F(35)=F(36)=7\), not a drop;
- \(r(41)=49\);
- \(r(42)\in\{49,50\}\).

Thus the order-49 nonexistence result would select \(r(42)=49\), producing
the Ramsey plateau \(r(41)=r(42)=49\) equivalent to
\(F(49)=7<8=F(48)\).  A SAT witness would instead select \(r(42)=50\) and
there would be no drop at 49.

Across Boza's decided table, no consecutive equality yielding an in-domain
strict drop of `F` is reported.  The equality \(r(1)=r(2)=4\) lies at the
lower boundary, before the first transition inside the stated \(N\geq4\)
domain.  Some later Ramsey entries remain ranges, so the paper cannot rule
out every earlier *undecided* candidate drop; it does show that none is
already decided by that table.

- Luis Boza, "Exact Values and Bounds for Ramsey Numbers of \(C_4\) Versus
  a Star Graph," arXiv:2409.12770v2, especially Section 3 and its tables:
  <https://arxiv.org/html/2409.12770v2>

### 3. Afzaly--McKay's 49-vertex records

Afzaly and McKay's combinatorial-data page lists, for `H={C4}` at 49
vertices, `ne >= 174` and `ng >= 6`.  Its legend is explicit: when both
numbers carry `>=`, the graphs are merely the best examples found and the
authors have not proved that graphs with more edges are impossible.  The
associated file is correspondingly named `c4_n49e174.maybe.s6`.

- Narjess Afzaly and Brendan McKay, "Extremal Graphs and Turan numbers":
  <https://users.cecs.anu.edu.au/~bdm/data/extremal.html>
- The six sparse6 records:
  <https://users.cecs.anu.edu.au/~bdm/data/extremal/c4_n49e174.maybe.s6>

As a reproducibility check, all six sparse6 lines were decoded with
NetworkX 3.6.1 and independently tested for the common-neighbor
characterization of `C4`-freeness.  Every graph has 49 vertices, 174 edges,
and minimum degree 6.  Their degree distributions are:

| records | degree distribution |
|---|---|
| 1--2 | \(6^4,7^{36},8^9\) |
| 3--4 | \(6^5,7^{34},8^{10}\) |
| 5--6 | \(6^7,7^{30},8^{12}\) |

These records are useful corroborating lower-bound examples for `F(49)>=7`.
They do not exclude a different 49-vertex `C4`-free graph of minimum degree
7, which is precisely the obligation discharged by the current certified
stratum campaign.

## Manuscript guardrails

1. Keep the priority phrase epistemic: "to our knowledge" or "we are aware
   of no earlier decided strict drop."
2. Say "decided" only after all four H1/H3/H5/H7 inputs pass the cold
   certificate and dependency-cone audit.
3. Cite Boza for the Ramsey table and the open `r(42)` entry; cite
   Afzaly--McKay only for their example records and label their status
   accurately.
4. Avoid an unqualified "first drop": the headline mathematical result of
   this finite campaign is one strict drop, whereas Erdős Problem 85 asks
   about eventual behavior and cannot be settled by a finite computation.
