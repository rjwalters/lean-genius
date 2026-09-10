"""Exact polynomial dual: the fixed psi3 triple root with R=2 has delta<=1."""
import sympy as s
from verify_q7_h3_local_galois_measures import roots,target
Y=list(map(s.Rational,['-814049641/3590000','1206/359','93867/718','0','-8375/359','-67/718','469/359']))
for root in roots:
    slack=s.simplify(sum(Y[k]*root**k for k in range(7)))
    assert slack.is_nonnegative is True
constant=sum(a*b for a,b in zip(Y,target(3,0,2,0)))
slope=sum(a*b for a,b in zip(Y,target(3,0,2,1)))-constant
assert constant==s.Rational(508202539,120265000)
assert slope==-s.Rational(938,359)
upper=constant/(-slope)
assert upper==s.Rational(508202539,314230000) and upper<2
# Degree(D,z)=3 permits at most3 local defect triangles.
for delta in range(4):
    value=sum(a*b for a,b in zip(Y,target(3,0,2,delta)))
    assert value==constant+slope*delta
    if delta>=2:assert value<0
print('PASS exact root-positive polynomial forces delta<=508202539/314230000<2, hence integer delta<=1')
print('Combined with the separate universal secondary ledger, excludes e(R8)=2 for this fixed psi3 only.')
