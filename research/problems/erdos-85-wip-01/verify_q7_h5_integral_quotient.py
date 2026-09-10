#!/usr/bin/env python3
"""Exact arithmetic certificate for the H5 integral quotient argument.

The graph-to-Perron-space reduction is a separate paper proof.
"""
import itertools
import json

import sympy as sp


def main():
    a = sp.symbols('a')
    field_poly = a*a-7*a+5
    reduce = lambda p: sp.rem(sp.expand(p), field_poly, a)
    g = reduce(12*a*a-20*a+10)
    j = reduce(20*a*a-40*a+40)
    assert g == 64*a-50 and j == 100*a-60
    alpha,beta,gamma,delta = sp.symbols('alpha beta gamma delta')
    expression = sp.Poly(reduce(g*(alpha+beta*a)-j*(gamma+delta*a)),a)
    equations = expression.all_coeffs()
    solution = sp.solve(equations,[alpha,gamma])
    assert solution == {alpha:10*delta-7*beta,gamma:-beta/2}
    candidates=[]
    for b,d in itertools.product((0,1),repeat=2):
        # From0<=q0<=5,0<=p0<=7. Bounds are deliberately weaker than
        # additional t1/t2/t3 count bounds; proving impossible here suffices.
        for A in range(-7*b,8-7*b):
            for C in range(-7*d,8-7*d):
                if reduce(g*(A+b*a)-j*(C+d*a)) == 0:
                    candidates.append([A,b,C,d])
    assert candidates == [[0,0,0,0]]
    # A rational cross-entry passes these linear/box conditions if integrality
    # is dropped: beta=delta=1/2, alpha=3/2,gamma=-1/4.
    rational = {alpha:sp.Rational(3,2), beta:sp.Rational(1,2),
                gamma:sp.Rational(-1,4),delta:sp.Rational(1,2)}
    assert all(sp.simplify(e.subs(rational))==0 for e in equations)
    assert 0 <= (alpha+7*beta).subs(rational) <= 7
    assert 0 <= (gamma+7*delta).subs(rational) <= 7
    profiles=[]
    for tau in (1,2):
        core=[10-tau,3*tau,10-3*tau,tau]
        assert sum(core)==20 and all(n>=0 for n in core)
        assert sum(t*core[t] for t in range(4))==20
        assert sum(t*t*core[t] for t in range(4))==40
        assert core[0]>0 and core[1]>0
        profiles.append({'triples':tau,'core_support_counts':core})
    print(json.dumps({'scope':'Arithmetic certificate; graph reduction remains paper',
        'sympy_version':sp.__version__, 'g':str(g),'j':str(j),
        'linear_solution':{str(k):str(v) for k,v in solution.items()},
        'integral_cross_entries':candidates,
        'rational_negative_control':{str(k):str(v) for k,v in rational.items()},
        'profiles':profiles,'C4free_minimum_degree6_requires_order_at_least':31,
        'proposed_closed_C_subset_order':24},indent=2))


if __name__ == '__main__':
    main()
