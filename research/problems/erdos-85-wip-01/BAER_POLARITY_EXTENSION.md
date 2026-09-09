# Every polarity of a Baer-deleted plane has absolute points

Let Pi be a finite projective plane of order Q=r^2, r>=2, and let B be a
Baer subplane of order r. Delete all points and lines of B, retaining the
incidences between exterior points and exterior lines; call this structure S.

**Claim.** Every polarity of S extends uniquely to a polarity of Pi
preserving B, and has at least one absolute exterior point. In fact, its
number of absolute exterior points is at least

    r^2+1 - floor((r^2+r+1)(r+1)/(2r+1)) > 0.

This would rule out obtaining a regular loopless polarity graph by changing
the polarity on this SAME incidence structure. It does not rule out trades
that change the incidence structure. The proof is not Lean formalized.

## Recover the deleted points and lines intrinsically

For each deleted line ell, let U_ell be its exterior points. Its size is
Q-r. These sets partition the exterior points: distinct deleted lines
intersect only inside B, and

    (r^2+r+1)(r^2-r) = r^4-r

is the total number of exterior points. Dually, the sets V_p of exterior
lines through deleted points p form a partition of the exterior lines,
each of size Q-r.

Two distinct exterior points have no common exterior line exactly when
their joining line was deleted, equivalently when they belong to the same
U_ell. Thus the relation consisting of equality or absence of a common
line of S recovers the U_ell classes intrinsically. Dually, equality or
absence of a common point of S recovers the V_p classes. These statements
are made about this given Baer-deleted plane; no general configuration
completion theorem is being assumed.

The missing incidence p in ell can also be recovered from S:

    p in ell  iff there are NO incidences between U_ell and V_p.   (1)

If p is on ell, each exterior line through p meets ell only at the deleted
point p. If p is not on ell, any such exterior line meets ell in an exterior
point (it has only one Baer point). Conversely, joining p to an exterior
point of ell gives an exterior line. Hence in this case incidences between
U_ell and V_p form a perfect matching of size Q-r, which is nonzero.

## Extend any polarity

A polarity of S interchanges the two intrinsic types of classes. Extend it
to deleted lines by their U classes and to deleted points by their V classes.
Incidence is preserved for each of the four possible old/deleted point-line
types: within S by assumption, for mixed types by class membership, and for
the deleted/deleted type by (1). This defines a duality of Pi. Applying it
twice fixes S and every recovered class, so it is an involution and thus a
polarity. The extension is unique because all recovered classes are nonempty
and distinct. It preserves B and restricts to a polarity of B.

## Too few absolute points can lie inside B

An elementary bound suffices. For a polarity of an order-r projective plane,
let a be its number of absolute points and v=r^2+r+1. Two distinct absolute
points x,y cannot satisfy x incident with y's polar line: by reciprocity,
the distinct polar lines of x and y would both contain x and y, contradicting
uniqueness of a joining line. Therefore each absolute point has exactly r
incidences with polar lines indexed by nonabsolute points. Counting these
cross incidences, while each nonabsolute row has at most r+1 incidences,
gives

    a*r <= (v-a)(r+1),
    a <= v(r+1)/(2r+1) < r^2+1.

The last strict inequality follows after clearing the positive denominator:

    (r^2+1)(2r+1) - (r^2+r+1)(r+1) = r^2(r-1) > 0.

Baer's absolute-point theorem says every polarity of an order-Q finite
projective plane has at least Q+1 absolute points. Applying it to the
extended polarity and subtracting the upper bound inside B proves the
claim, including the explicit positive lower bound outside B.

Reference for this sole external theorem: R. Baer, *Polarities in finite
projective planes*, Bull. Amer. Math. Soc. 52 (1946), 77-93.
https://doi.org/10.1090/S0002-9904-1946-08506-7

The original publisher URL was inaccessible in this session. The exact
lower-bound statement was checked in W. M. Kantor, *On homologies of finite
projective planes*, Israel J. Math. 16 (1973), Lemma 3.4, printed page 354:
https://pages.uoregon.edu/kantor/PAPERS/HomologiesPlanes.pdf

## Application and limits

For odd r and Q=r^2, S has Q^2-r exterior points, an even number in the
odd-degree drop band, and every point is on Q retained lines. A polarity
therefore gives a symmetric binary matrix with constant row sum Q. An
absolute point contributes a loop; after deleting loops its degree is Q-1.
Since an absolute point must remain, no choice of polarity on S supplies
minimum degree Q. This closes the alternate-polarity proposal on the
unchanged Baer-deleted incidence structure, not the cofinal construction
problem or Erdős 85.
