# A-REG Baer absolute-point literature audit

Status: negative scope audit under `A-REG-NONBIP -> NONBIP-CONNECTED`,
26 August 2026.  No published terminal matching the required hypotheses was
found.  Two superficially close classical routes are ruled out below.

## Target and dictionary

The target is a symmetric, loopless, binary `q`-regular C4-free matrix `A`
of order `q^2`, where `q = 2^k`, `k >= 3`.  Regard `A` as the incidence
matrix of a self-polar symmetric `(q^2_q)` configuration.  Its deficiency
graph `D` joins pairs of points on no common line.  The exact matrix identity
is

```text
A^2 = (q - 1) I + J - D = L_D + J.
```

Thus `D` is `(q-1)`-regular, and the desired contradiction is equivalently
that a fixed-point-free polarity cannot have connected `D`.  Equivalently,
`A` must be singular; indeed the existing campaign identity gives
`dim ker A = #components(D) - 1`.

## Classical symmetric-design polarity theorem: hypothesis mismatch

Godsil's *Finite Geometry*, Theorem 18.1.1, treats a symmetric
`(v,k,lambda)` design with a polarity.  Its proof uses the scalar identity

```text
N^2 = (k - lambda) I + lambda J.
```

It concludes, among other things, that a polarity without absolute points
forces `sqrt(k-lambda)` to be integral and to divide `k`.  The projective
plane corollary and Theorem 18.2.2 then force absolute points.

This does not specialize to A-REG.  Here distinct point pairs have either
zero or one common line, and the missing pairs form `D`; the corresponding
identity contains the non-scalar term `-D`.  Setting `lambda = 1` would
silently assert `D = 0`, exactly deleting the connected-deficiency case to
be proved.  The line-pairing step in the projective-plane proof likewise
uses that every two lines meet, whereas a configuration has disjoint line
pairs.  Therefore the published theorem is a useful scope boundary, not a
consumer.

Primary source:
<https://www.math.uwaterloo.ca/~cgodsil/pdfs/bigGeom.pdf>, Sections 18.1--18.2.

## Strongly regular configurations: prerequisite impossible

Abreu, Funk, Krcadinac and Labbate study symmetric configurations whose
point graph is strongly regular.  Their Theorem 2.3 says that singular
incidence forces the configuration to be a partial geometry; Corollary 2.6
characterizes singularity versus properness from the strongly regular
parameters.  This initially looks close because singularity is exactly the
A-REG conclusion.

However strong regularity cannot be added to a connected A-REG deficiency
graph.  If `D` were strongly regular, its parameters would be

```text
SRG(v,d,lambda,mu) = SRG(q^2, q-1, lambda, mu).
```

The standard parameter equation

```text
(v - d - 1) mu = d (d - lambda - 1)
```

then reduces to

```text
q mu = q - lambda - 2.
```

Connectedness gives `mu >= 1`, while `lambda >= 0`; hence the left side is
at least `q` and the right side at most `q-2`, a contradiction.  Equivalently,
the point graph cannot be strongly regular either, because it is the
complement of `D`.  Thus the strongest published singular-incidence theorem
located in the configuration literature applies only after imposing a
hypothesis that is incompatible with the target.

Primary source: M. Abreu, M. Funk, V. Krcadinac, D. Labbate, *Strongly
regular configurations*, Designs, Codes and Cryptography 90 (2022),
1881--1897, especially Theorem 2.3 and Corollary 2.6:
<https://arxiv.org/abs/2104.04880>.

## Deficiency-graph literature: terminology, not a terminal

The configurations literature calls the complement of the point/Menger
graph the *deficiency graph* (also *Martinetti graph* or *Restfigur*).  The
standard reference explicitly warns that this graph does not determine the
configuration.  Searches under all three terms found constructions and
enumerations, including generalized pentagonal geometries with connected
deficiency graphs, but no absolute-point theorem coupling a polarity to
deficiency connectivity.

Reference: Grunbaum, *Configurations of Points and Lines*, Chapter 1,
Section 1.4:
<https://faculty.washington.edu/moishe/branko/CfsPts%26LinesFinal%20pdf%20files/Chapter%201.pdf>.

## Resulting scope cut

There is no justified citation-level port of Baer presently available:

1. symmetric-design polarity theorems require constant pair multiplicity,
   which is precisely absent and encoded by `D`;
2. strongly regular configuration theorems require a strongly regular point
   graph, which connectedness and the A-REG parameters rule out outright;
3. connected deficiency graphs occur broadly in partial-linear-space
   constructions, but the sources found impose no self-polar absolute-point
   conclusion.

Accordingly, the literature search does **not** close `NONBIP-CONNECTED`.
It does sharpen the missing theorem: it must use more than the abstract
deficiency graph, and more than its two-point intersection counts.  It must
couple the self-indexing polarity to nonconstant missing-pair structure.
That is exactly the interface exposed by the existing non-`A` Eulerian
transport `K` and its kernel-shore incidence law.  The next bounded probe
should therefore remain the `k >= 3` location theorem for that canonical
transport; importing partial-geometry or strongly-regular machinery is cut.
