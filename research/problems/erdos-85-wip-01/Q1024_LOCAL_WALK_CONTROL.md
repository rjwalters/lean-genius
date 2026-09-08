# A finite local-walk control for the q=1024 formal spectrum

2026-09-08, Sol3, building on Sol1's three local fifth-moment types.
Prose and exact rational computation, not Lean-formalized.

**This constructs diagonal spectral measures only.** It does not construct
orthogonal projectors, off-diagonal entries, an integer matrix, or a graph.
It does not resolve A-REG or Erdős 85. Its purpose is to test the additional
local integrality requirement left open by the global-filter control.

Set q=1024, t=32, n=q² and use precisely the spectrum in
`UNBOUNDED_SPECTRAL_FILTER_CONTROL.md`. There are nine types of vertices,
with positive integer populations totaling n, for which all of the following
hold simultaneously:

* Each vertex has nonnegative weights on that spectrum, summing to one,
  with principal weight 1/n. Aggregating each eigenvalue's weight over the
  vertices gives its prescribed multiplicity exactly.
* Local moments m_0,...,m_4 are 1,0,q,q-d,q(2q-1), respectively. The values
  d are 0 or 2, the allowable triangle-free degrees used below.
* The local fifth-moment identity m_5=q³-2qd+2e is met by nonnegative
  integers e, with the same allocation as Sol1's previous control.
* Every positive-length local moment is an even integer. All moments are
  nonnegative; m_1=0 and every m_k for k>=2 is positive.
* The existing sixth-moment defect-triangle bound is met locally.

These conditions alone therefore do not reject this q1024 spectrum. No
claim about every binary q, other local constraints, or graph realization
is made.

## Coordinates and the initial fifth-moment allocation

Use the six squared supports

    a = (4,8,16,q-t,q,q+t).

At each support let W_a=w_(+sqrt(a))+w_(-sqrt(a)), and let
Z_a=sqrt(a)(w_(+sqrt(a))-w_(-sqrt(a))). Then nonnegative eigenvalue
weights are equivalent to W_a>=0 and Z_a²<=a W_a². Their contributions
to moments are W_a*a^j at length 2j and Z_a*a^j at length 2j+1.
The principal contribution at length k is q^k/n.

The initial W values are the global multiplicities divided by n. The low
Z values at supports (4,8,16) are (-4,0,-q+4)/n. Initially the three
high Z values may vary to meet each of the following local types while
preserving their aggregate zero:

| Population | d | m_5 | e=(m_5-q³+2qd)/2 |
| --- | --- | --- | --- |
| 96 | 2 | q³-30 | 2033 |
| 8072 | 2 | q³-32 | 2032 |
| n-8168 | 0 | q³ | 0 |

Keeping W constant would give m_6=2253998099731607/2048 at every vertex,
so that initial allocation fails the next local integrality requirement.
The following adjustment repairs it and all subsequent lengths at once.

## Six integral coordinates

Put Y=X² and

    g(Y)=(Y-(q-t))(Y-q)(Y-(q+t)).

Use the monic polynomial basis (1,Y,Y²,g,Yg,Y²g), which has successive
degrees 0,...,5 and integer coefficients. For each local linear functional
L on polynomials in X, round these six values to even integers:

    L(g), L(Yg), L(Y²g), L(Xg), L(XYg), L(XY²g).

Each value has two choices: its even floor or that floor plus two. Keep
L(1),L(X),...,L(X^5) at their prescribed values. Solving the two six-by-six
systems in W and Z recovers a unique rational measure: the evaluation
matrix is invertible because this monic basis spans all polynomials of
degree at most five and the six supports are distinct.

The executable checks all 3*64=192 choices exactly. Every resulting measure
satisfies W>=0 and Z²<=aW². Thus any coordinated choice of roundings across
the three parent populations preserves nonnegative eigenvalue weights.

## Integer populations and exact aggregation

Because g vanishes at the three high supports, all six unrounded values
have the same means across the three parent types. For a mean b and its
even floor f, choose precisely n(b-f)/2 vertices to use f+2. Those six
integer counts, in the displayed coordinate order, are

    300800, 836608, 872448, 606080, 32256, 653312.

Index the vertices by integers 0,...,n-1. For each coordinate use its upper
rounding on the initial segment of the indicated size. Intersect these
segments with the parent intervals [0,96),[96,8168),[8168,n). This yields
nine types with populations

    96,8072,24088,268544,305280,47232,183296,35840,176128.

Each rounded coordinate now has exactly its original aggregate. The first
three even and odd coordinates also preserve their aggregate by the parent
allocation. Invertibility and linearity of the two systems imply that each
W and Z has exactly its prescribed aggregate. This proves the global
eigenvalue multiplicities, not merely agreement of a few traces.

## Why all lengths follow

The monic basis first gives even integral m_6,...,m_11 recursively. Its
constant contributions in the even system are even: g has even constant
term, and Yg,Y²g have constant zero.

The residual annihilator is

    h(X)=product_a (X²-a),

with degree twelve and even constant term. The local principal weight
gives L(h)=h(q)/n, which is an even integer by the previously verified
Hoffman parity test. All lower positive moments are even integers, so this
identity gives even integral m_12 as well.

Finally F(X)=(X-q)h(X) is monic of degree thirteen, has integer coefficients
and even constant term, and vanishes on the entire support. Its recurrence
therefore gives even integral m_13: its only term involving m_0 has even
coefficient. Every later recurrence step involves only positive moments,
so induction gives even integrality at every length. This is an all-length
argument; the executable's direct checks through thirteen are calibration.

Even moments are positive from the nonnegative weights and principal root.
The moments of lengths one and three are specified. Every residual root
has modulus below 33, and q^5>n*33^5, so for every k>=5 the principal
contribution q^k/n exceeds the absolute value of the entire residual
contribution. In particular all later odd moments are positive.

The two local sixth moments are 1100585009636 and 1100585009634. The
executable verifies for each type that

    0 <= q⁴+q³-3q+2-m_6 <= (q-1)(q-2),

and that this difference is even, as required for a possible local D³
diagonal. This is only a triangle-count range, not a defect realization.

## Verification and remaining obstruction

Run `python3 verify_q1024_local_walk_control.py` (SymPy is used for one
exact rational matrix inverse). It checks all rounding combinations,
populations, aggregate weights, initial moments, parity, and the finite
annihilator certificate.

The missing requirement is compatibility of these diagonal measures with
common orthogonal spectral projectors and the entrywise adjacency rules.
Independent local measures do not impose either. Extending this same local
integer-moment test to more lengths cannot reject the present control.
