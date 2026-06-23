#!/usr/bin/env python3
"""First rigorous FINITE upper bound on f(n) for Erdos #733 OQ-01.

f(n) = #{ realizable multisets M of >=3-rich-line sizes } (researcher-8's reformulation;
distinctness of induced sequences verified n<=12). Writing mu(M) for the minimum number
of points realizing exactly the >=3-lines M, f(n) = #{ M : mu(M) <= n }.

KEY NEW NECESSARY CONDITION (lower bound on mu, hence UPPER bound on f):
distinct rich lines pairwise share <= 1 point, so the C(a_i,2) point-pairs covered by
distinct lines are DISJOINT subsets of the C(P,2) pairs. Hence any realization of M needs
    sum_i C(a_i, 2)  <=  C(P, 2)        (the "Fisher/pair" bound)
and trivially P >= max_i a_i.  Define
    lb(M) = min P with C(P,2) >= sum C(a_i,2) and P >= max(M).
Then lb(M) <= mu(M), so  U(n) := #{ M : lb(M) <= n }  satisfies  f(n) <= U(n).

The construction lower bracket L(n)=G(n) (researcher-8, three realizable families) gives
f(n) >= L(n). Together: L(n) <= f(n) <= U(n), a two-sided rigorous bracket.

Sanity: at the EXACTLY known values f(3..6) = 2,3,5,9 we must have L <= f <= U.
The pair bound is provably valid but LOOSE (e.g. M=[3,3,3,3,3] has lb=6 yet is NOT
realizable in 6 points: that needs a triangle-decomposition of K6, impossible since K6
vertices have odd degree 5). So U is an over-count, not f itself; it does not pin f(7).
"""
import sys
from math import comb

NMAX = 12
PAIRCAP = comb(NMAX, 2)

# all multisets of parts in [3,NMAX] with pairsum <= PAIRCAP (complete for mu<=NMAX)
multisets = set()
def gen(maxpart, cur, pairsum):
    multisets.add(tuple(cur))
    for a in range(min(maxpart, NMAX), 2, -1):
        ps = pairsum + comb(a, 2)
        if ps <= PAIRCAP:
            cur.append(a); gen(a, cur, ps); cur.pop()
gen(NMAX, [], 0)

def pairsum(M): return sum(comb(a, 2) for a in M)

def lb(M):                      # valid lower bound on mu(M)
    ps = pairsum(M); P = max(M) if M else 0
    while comb(P, 2) < ps: P += 1
    return P

def ub(M):                      # realizable budget => upper bound on mu(M) (researcher-8)
    if not M: return 0
    k = len(M); s = sum(M)
    b = [s, s - (k - 1)]
    if all(a >= k - 1 for a in M): b.append(s - comb(k, 2))
    return min(b)

exact = {3: 2, 4: 3, 5: 5, 6: 9}
fail = 0
rows = []
for n in range(3, NMAX + 1):
    L = sum(1 for M in multisets if ub(M) <= n)
    U = sum(1 for M in multisets if lb(M) <= n)
    rows.append((n, L, U, exact.get(n)))
    if not (L <= U):                          fail += 1; print("BRACKET INVERTED", n)
    if n in exact and not (L <= exact[n] <= U):fail += 1; print("EXACT OUT OF BRACKET", n)

print(f"{'n':>3} {'L=G(n)':>7} {'U(pair)':>8} {'exact':>6} {'2^n-1':>7}")
for n, L, U, e in rows:
    print(f"{n:>3} {L:>7} {U:>8} {str(e if e is not None else '?'):>6} {2**n-1:>7}")

if fail:
    print(f"FAILED: {fail} consistency violations"); sys.exit(1)
print("OK: L(n) <= f(n) <= U(n) consistent with all known exact values; "
      f"f(7) in [{rows[4][1]},{rows[4][2]}] (placeholder 2^7-1=127).")
