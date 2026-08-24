# Size-two cyclic polarity/net literature audit

## Question

Can loopless reciprocity be viewed as a polarity of a net, transversal
design, or partial geometry, so that a classical absolute-point theorem
forces an empty/nonempty internal-fibre pattern and closes the no-empty
packing exclusion?

## What the classical theorems actually assume

A polarity is an incidence-reversing involution between points and lines.
Absolute points correspond to diagonal incidences (loops in the polarity
graph).  In a **generalized quadrangle** with a polarity, every line contains
exactly one absolute point, so the absolute points form an ovoid.  The same
source derives strong arithmetic restrictions for a generalized quadrangle
of order `(s,s)`.  These conclusions use the generalized-quadrangle axiom:
for every point and nonincident line there is a unique connecting point.

Reference: Simeon Ball, *An Introduction to Finite Geometry*, section 4.2,
Propositions 4.2.1--4.2.2 and Theorem 4.2.3:
<https://citeseerx.ist.psu.edu/document?doi=bd387fa4ac730b98cda687faa5fc227b2b713cfc&repid=rep1&type=pdf>.

Debroey--Thas obtain formulas for the number of absolute points of a
**symmetric semipartial geometry**, but again assume uniform parameters:
regular point/line degrees and fixed intersection numbers for collinear and
noncollinear pairs.  Their matrix proof uses the resulting quadratic
incidence-matrix identity.

Reference: I. Debroey and J. A. Thas, *On polarities of symmetric semi
partial geometries*, Rend. Accad. Naz. Lincei 62 (1977), 606--612:
<https://www.bdim.eu/item?fmt=pdf&id=RLINA_1977_8_62_5_606_0>.

At the level of an arbitrary partial linear space, a polarity need not have
any absolute points.  Even symmetric incidence designs with zero diagonal
(fixed-point-free polarity) are known.  Thus reciprocity alone has no Baer-
type absolute-point consequence.

## Why the packing interface does not meet those hypotheses

The size-two cyclic code supplies:

- exact row/column hit margins;
- a symmetric, loopless cell adjacency relation; and
- common-target uniqueness only for pairs of sources in the **same
  difference fibre**.

It does not currently supply uniform common-neighbour numbers for
cross-fibre pairs, the point--nonincident-line uniqueness axiom of a
generalized quadrangle, or the semipartial-geometry quadratic incidence
identity.  The uncontrolled cross-fibre blocks of `K^2` are precisely the
missing intersection parameters.  Promoting the code to one of the
classical geometries would therefore assume the main unresolved structure
rather than derive it.

Nets and transversal designs do not repair this gap.  A net requires exact
constant intersections between nonparallel blocks; the code only has an
upper cap in selected parallel classes.  Standard net existence theory also
allows broad nonclassical families and gives no polarity theorem at this
weaker level.  Background definition and parameter scope:
<https://encyclopediaofmath.org/wiki/Net_in_finite_geometry>.

## Verdict

The direct polarity/absolute-point shortcut is **cut** at the present
interface.  The applicable classical results begin only after imposing the
cross-fibre intersection regularity that our spectral and completed-square
audits identified as missing.

A geometry route could revive if the caps plus exact hits first prove a
uniform cross-fibre `K^2` law.  At that point the Debroey--Thas symmetric
semipartial-geometry matrix identity would be relevant.  Until then, citing
Baer, generalized quadrangles, nets, or polarities does not address the
no-empty packing theorem.
