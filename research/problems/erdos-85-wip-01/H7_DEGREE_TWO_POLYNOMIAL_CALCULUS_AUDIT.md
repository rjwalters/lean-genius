# H7 degree-two polynomial-calculus audit

## Candidate

Divergence round 72 proposed changing proof systems again: represent the 861
semantic low-edge variables as Boolean polynomials, reduce exact degrees modulo
two, translate an all-negative C4 clause to a forbidden-edge-product monomial,
and search for a low-degree Polynomial Calculus/Nullstellensatz refutation.
Such a refutation would be an explicit linear combination yielding `1` and
could be checked coefficient by coefficient.

This audit applies the predeclared sparse Macaulay memory gate to the hard
missing parent `F6/type2`.  It uses the exact native-parent builder from
`check_h7_t0_pseudo_boolean.py`; it does not alter or approximate the mask,
variable order, or the degree equations before reduction modulo two.

## Generator census

After the 42 degree equations and before the 21 mask units, the canonical C4
constraints have polynomial degree distribution

```text
degree 2:  15,680
degree 4: 671,580
```

There are no cubic generators.  In the squarefree Boolean quotient on 861
variables, the monomial counts through degrees two, three, and four are
371,092, 106,380,282, and 22,845,351,537 respectively (including the constant).
A naive closed Macaulay system has approximately 52,745 rows at degree two,
29,844,206 rows at degree three, and 10,606,876,196 rows at degree four before
mask multiples.  Degree three is therefore already outside the memory gate
while still excluding every one of the 671,580 quartic C4 generators; degree
four is wholly infeasible by this representation.

## Exact degree-two result

`sat49/probe_h7_degree_two_pc.py` constructs the complete affordable system
over `GF(2)`:

1. every exact low-degree equation reduced modulo two;
2. every product of such an equation by each of the 861 variables;
3. the Boolean squarefree identities, implemented by identifying `x_i^2`
   with `x_i`;
4. all 15,680 quadratic C4 monomials;
5. every mask unit and its product by each variable.

An initial Z3 XOR solve reached its 60-second cap with `UNKNOWN`.  This was a
backend limitation, not a mathematical verdict.  The checked-in probe also
contains a direct exact incremental sparse Gaussian eliminator, with unit
tests for consistent, inconsistent, and dependent affine systems.  It gives:

```text
F=6
type_index=2
Macaulay columns = 371,091 nonconstant squarefree monomials
equations        = 69,986
rank             = 59,331
maximum pivot width = 9,040
verdict          = SAT
wall time        = 18.5 seconds
```

Here `SAT` means precisely that the affine Macaulay linear system is
consistent.  It is a degree-two pseudo-solution, not an H7 graph and not a SAT
claim about the original parent.

## Verdict

**Cut.**  Degree-two Polynomial Calculus cannot refute the hard parent.
Degree three is two orders of magnitude larger in columns, still has no access
to the dominant quartic C4 constraints, and violates the stated memory gate.
Degree four is many billions of rows and columns.  Do not implement a generic
Groebner/Macaulay engine or sweep other masks.  Revisit algebraic certificates
only if a new symmetry quotient or invariant collapses the quartic generators
before linearization.
