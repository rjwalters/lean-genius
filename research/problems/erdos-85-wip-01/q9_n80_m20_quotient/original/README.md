# Necessary orbit quotients for N80/delta9/free-Z20

This is a small integer quotient enumeration, not a graph search or solver verdict. No CNF is modified.

Accepted2140 gives9-regularity. With four20-vertex cyclic orbits, the symmetric equitable degree matrix Q has row sums9 and diagonal entries0,1,2, because an internal circulant of degree at least3 has a C4. For i!=j, (Q²)ij counts two-step walks from a fixed vertex in orbit i to orbit j; C4-freeness requires (Q²)ij<=20. For i=j, subtract the9 immediate returns to the starting vertex: (Q²)ii-9<=19, hence (Q²)ii<=28. If two diagonal entries both equal1, their internal shift is the involution10; any cross edge between these orbits gives a C4 with its translate. Their cross degree must be0.

The script enumerates diagonal entries in{0,1,2} and the three cross degrees01,02,12 in{0,...,9}; the other three cross degrees are uniquely forced by the first three row sums, then the fourth row is checked. This visits exactly1526 nonnegative regular integer quotients. The path inequalities and involution condition leave10 labelled quotients in three permutation classes:

```
0 3 3 3       2 1 2 4       2 2 2 3
3 0 3 3       1 2 4 2       2 2 3 2
3 3 0 3       2 4 2 1       2 3 2 2
3 3 3 0       4 2 1 2       3 2 2 2
```

Their labelled multiplicities are1,6,3. Therefore no internal degree-one orbit survives these necessary conditions. This enumeration does not prove that any retained quotient lifts to a graph, or exclude N80/m20. The generic encoding and prepared CNF remain unchanged. Independent review is required before using the cover as an additional search restriction.
