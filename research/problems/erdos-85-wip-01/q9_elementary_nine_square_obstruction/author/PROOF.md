# Small arithmetic replacement for the331776-case character check

Use the mathematical reduction in2215, but take only a nontrivial character with kernel L_A. Its three component determinant factors F,S,T lie in the following sets (independent choices are a valid overapproximation):

 F in {270,297,423,432,450,459,666,693},
 S in {48,99},
 T in {1911,2751,2940,3960,4221,5700,6060,8700}.

For F, substitute x,y in{6,9}, t in{1,4} into(9x-3)y-9t. For S, substitute d in{1,-2} into(8-d)^2-1. For T, substitute z in{6,9} and three v_i in{7,10} into z*v1*v2*v3-(v1*v2+v1*v3+v2*v3); the value depends only on how many v_i equal7, giving eight possibilities. Thus these sets do not require any group-line enumeration.

We prove F*S*T is never a square by prime-exponent parity. Six values of T have an odd prime factor that occurs in no F or S:

 1911=3*7^2*13,
 2751=3*7*131,
 4221=3^2*7*67,
 5700=2^2*3*5^2*19,
 6060=2^2*3*5*101,
 8700=2^2*3*5^2*29.

The respective unique primes13,131,67,19,101,29 remain to odd exponent in the product.

For the other two values, write sf(n) for the product of primes occurring to odd exponent in n. Then sf(2940)=15 and sf(3960)=110; sf(48)=3 and sf(99)=11. Consequently sf(S*T) belongs to{5,165,330,10}. On the other hand the squarefree parts of the eight F values are respectively

 {30,33,47,3,2,51,74,77}.

These sets are disjoint. A product of two positive integers is a square precisely when their squarefree parts agree, so F*S*T is nonsquare in the remaining cases too.

Therefore the single L_A-character already contradicts the integer-square determinant necessity of2215. This replaces its full finite enumeration by the displayed small integer calculations. check.py regenerates all three sets and checks all128 products with math.isqrt, without third-party libraries. The conceptual graph/group/character reduction remains dependent on2215 and its predecessors; this note does not assert a global N78 exclusion or solve Erdős85.
