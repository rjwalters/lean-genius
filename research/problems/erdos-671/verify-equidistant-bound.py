#!/usr/bin/env python3
"""
Numerical check supporting the ONE tractable sorry of Erdos671Problem.lean:
  equidistant_diverges : lebesgueConstant (equidistantNodes n) >= 2^(n-1)/n^2

Confirms (n=2..25): the bound HOLDS (statement is true), the roadmap point
x* = -1 + h/2 (h = 2/(n-1)) already carries it, and the dominant Lagrange basis
index at x* is ~ floor((n-2)/2) = n/2 - 1 (NOT floor(n/2)). Use that m in the
factorial lower bound when formalizing step 3. Requires numpy.
"""

import numpy as np

def equidistant_nodes(n):
    return np.array([-1.0 + 2.0*k/(n-1) for k in range(n)])

def lebesgue_function(nodes, x):
    # sum_i |L_i(x)|
    n = len(nodes); s = 0.0
    for i in range(n):
        num = 1.0; den = 1.0
        for k in range(n):
            if k != i:
                num *= (x - nodes[k]); den *= (nodes[i] - nodes[k])
        s += abs(num/den)
    return s

def lebesgue_const(nodes, samples=4001):
    xs = np.linspace(-1, 1, samples)
    return max(lebesgue_function(nodes, x) for x in xs)

def basis_at(nodes, i, x):
    num=1.0; den=1.0
    for k in range(len(nodes)):
        if k!=i: num*=(x-nodes[k]); den*=(nodes[i]-nodes[k])
    return abs(num/den)

print(" n |   Lambda_n   |  2^(n-1)/n^2  | bound holds | argmax-near-x* | dominant index")
for n in range(2, 26):
    nodes = equidistant_nodes(n)
    Ln = lebesgue_const(nodes)
    bound = 2.0**(n-1)/n**2
    holds = Ln >= bound
    # roadmap claim: x* = -1 + h/2 (h=2/(n-1)) midpoint of first subinterval; dominant basis index ~ n/2
    h = 2.0/(n-1); xstar = -1 + h/2
    contribs = [basis_at(nodes, i, xstar) for i in range(n)]
    dom = int(np.argmax(contribs))
    print(f"{n:2d} | {Ln:12.4g} | {bound:12.4g} | {str(holds):5} | lam(x*)={lebesgue_function(nodes,xstar):.3g} | dom_i={dom} (n/2={n//2})")
