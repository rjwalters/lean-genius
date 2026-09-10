#!/usr/bin/env python3
"""Exact arithmetic checks for the H5/H7 worksheet; not a graph search or proof.

Requires SymPy. Writes JSON to stdout, never launches a solver or Lean replay.
The field/Perron and graph arguments remain paper proofs requiring review.
"""
import itertools
import json
import math

import sympy as sp


def incidence(h, triples):
    masks = [tuple(t) for t in triples]
    covered = {p for t in triples for p in itertools.combinations(t, 2)}
    assert len(covered) == 3 * len(triples)
    masks += [p for p in itertools.combinations(range(h), 2) if p not in covered]
    for i in range(h):
        masks += [(i,)] * (8 - sum(i in m for m in masks))
    masks += [()] * (49 - h - len(masks))
    assert len(masks) == 49 - h
    return sp.Matrix([[int(i in m) for m in masks] for i in range(h)]), masks


def component_arithmetic(h, triple_free):
    # Necessary arithmetic only; no assertion that any listed tuple is realizable.
    records = []
    choices = [(s, k) for s in range(2, 9, 2) for k in range(0, h, 2)]
    for c in (1, 3):  # Conditional on the paper proof that c is odd.
        for pieces in itertools.combinations_with_replacement(choices, c):
            if sum(s for s, k in pieces) != 8 or sum(k for s, k in pieces) != h - 1:
                continue
            if any((triple_free or k in (0, 2)) and s < k + 2 for s, k in pieces):
                continue
            # At each high vertex, 2s-k=2*singletons+pairs. If zero,
            # every support is a triple and hs must be divisible by3.
            if any(2*s < k or (2*s == k and h*s % 3) for s, k in pieces):
                continue
            records.append([{"s": s, "k": k, "order": 6*s-k} for s, k in pieces])
    return records


def main():
    x, h = sp.symbols("x h")
    Q = sp.Matrix([[0, 8, h+7], [0, 7, h], [1, -1, 0]])
    assert sp.expand(Q.charpoly(x).as_expr() - (x**3-7*x**2-7*x+49-h)) == 0
    profiles = [(5, [], [14,20,10,0]),
                (5, [(0,1,2)], [13,23,7,1]),
                (5, [(0,1,2),(0,3,4)], [12,26,4,2]),
                (7, [], [7,14,21,0])]
    out = {"scope": "exact setup checks; no graph exclusion or realizability test",
           "sympy_version": sp.__version__, "profiles": []}
    for hv, triples, expected in profiles:
        B, masks = incidence(hv, triples)
        counts = [sum(len(m) == i for m in masks) for i in range(4)]
        assert counts == expected
        assert B * B.T == 7*sp.eye(hv) + sp.ones(hv)
        assert B * sp.ones(49-hv, 1) == 8*sp.ones(hv, 1)
        G = B.col_join(sp.ones(1, 49-hv))
        gram_det = int((G*G.T).det())
        delta = 343 - 22*hv - hv*hv
        assert gram_det == 7**(hv-1)*delta
        a = (7+sp.sqrt(49-4*hv))/2
        b = 7-a
        assert sp.simplify(a*b-hv) == 0
        # D and C act on columns (1,t) by these matrices.
        D2, C2 = sp.Matrix([[6,hv],[-1,-1]]), sp.Matrix([[7,hv],[-1,0]])
        z = sp.Matrix([a,-1])
        assert sp.simplify(D2*z-(a-1)*z) == sp.zeros(2,1)
        assert sp.simplify(C2*z-a*z) == sp.zeros(2,1)
        totals = [49-hv, sum(len(m) for m in masks), sum(len(m)**2 for m in masks)]
        # Actual triangle/local-state constraints, not mere hand-entered bounds.
        states = {t: [tau for tau in range(4) if 0 <= 7-2*t-2*tau <= 6-t]
                  for t in range(4)}
        lower = math.ceil(sum(counts[t]*min(states[t]) for t in range(4))/3)
        upper = sum(counts[t]*max(states[t]) for t in range(4))//3
        out["profiles"].append({"h": hv, "triples": triples, "support_counts": counts,
            "gram_det": gram_det, "gram_square_class": 13 if hv == 5 else 35,
            "totals_m_T_U": totals, "triangle_interval": [lower,upper],
            "component_arithmetic_conditional_on_paper_lemmas": component_arithmetic(hv, not triples)})
    assert out["profiles"][3]["totals_m_T_U"] == [42,56,98]
    assert (98//2-56//2) % 2 == 1
    assert [len(p["component_arithmetic_conditional_on_paper_lemmas"]) for p in out["profiles"]] == [1,2,2,1]
    # The H5 equal-component conic has an exact field solution. This does
    # not give an integral graph operator or establish graph realizability.
    a = sp.symbols('a')
    field_poly = a*a-7*a+5
    reduce = lambda p: sp.rem(sp.cancel(p),field_poly,a)
    g, j = 64*a-50, 100*a-60
    G = 2*g+j
    delta = reduce(j*G)
    gram = sp.diag(g,g,j)
    v1, v2 = sp.Matrix([1,-1,0]), sp.Matrix([j,j,-2*g])
    assert reduce((v1.T*gram*v2)[0]) == 0
    assert reduce((v1.T*gram*v1)[0]-2*g) == 0
    assert reduce((v2.T*gram*v2)[0]-2*g*delta) == 0
    u, v = (2*a-9)/4, (32*a-199)/2320
    assert reduce(u*u+delta*v*v-(7-a)) == 0
    out['h5_component_conic'] = {'delta':str(delta),'u':str(u),'v':str(v),
        'identity_remainder':0,'scope':'Conic witness only; no graph/spectrum realization'}
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
