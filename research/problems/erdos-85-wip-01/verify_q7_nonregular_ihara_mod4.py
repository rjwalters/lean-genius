#!/usr/bin/env python3
"""Polynomial calibration only, not a spectrum search or graph verifier."""
import json
import math
import random

import sympy as sp


def trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def mul(a, b, mod=4):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j]+x*y) % mod
    return trim(out)


def square_test(p):
    p = trim([x % 4 for x in p])
    root = [p[i] % 2 for i in range(0, len(p), 2)]
    return p == mul(root, root)


def reduced_polynomial(h, c):
    k = 48-2*h
    assert len(c) <= k+1 and c[0] == 1
    # Direct coefficient expansion of (1+6u²)^k*c(u/(1+6u²)),
    # independent of the derivative shortcut in the proof.
    R = [0]*(2*k+1)
    for j, cj in enumerate(c):
        for i in range(k-j+1):
            R[j+2*i] = (R[j+2*i]+cj*math.comb(k-j,i)*6**i) % 4
    H = [1,-7,12,-42-h,78+h,-294,252]
    if h == 5:
        H = mul(H, [1,0,-1])
    return mul(H, R)


def main():
    u, h = sp.symbols('u h')
    Q = sp.Matrix([[0,8,h+7],[0,7,h],[1,-1,0]])
    H = sp.expand((sp.eye(3)-u*Q+u*u*sp.diag(7,6,6)).det())
    assert sp.expand(H-(1-7*u+12*u*u-(42+h)*u**3+(78+h)*u**4-294*u**5+252*u**6)) == 0
    q = 1+u+u*u
    rows = []
    rng = random.Random(85050910)
    for hv in (5,7):
        k = 48-2*hv
        f = sp.expand(H.subs(h,hv)*(1-u*u if hv == 5 else 1))
        g = 1+u+u**3+u**4 if hv == 5 else 1+u**3
        W = sp.Poly(sp.expand((g*g-f*q-2*f*u**3*sp.diff(q,u))/2),u)
        assert all(c.is_Integer for c in W.all_coeffs())
        difference = W.as_expr() if hv == 5 else W.as_expr()-u*f
        assert all(int(c) % 2 == 0 for c in sp.Poly(difference,u).all_coeffs())
        passed = failed = 0
        for _ in range(16):
            S = [1]+[rng.randrange(2) for _ in range((k-2)//2)]
            target = mul([1,1 if hv == 5 else 3,1],mul(S,S))
            c = target+[0]*(k+1-len(target))
            assert square_test(reduced_polynomial(hv,c))
            passed += 1
            # Same parity, one changed mod-four coefficient: must fail.
            j = rng.randrange(1,k+1)
            c[j] = (c[j]+2) % 4
            assert not square_test(reduced_polynomial(hv,c))
            failed += 1
        rows.append({'h':hv,'degree':k,'passing_polynomial_controls':passed,
                     'failing_same_parity_mutations':failed,
                     'W_mod2':str(sp.Poly(W,u,modulus=2).as_expr())})
    print(json.dumps({'scope':'Exact algebra and polynomial controls only; no spectral or graph realizability',
                      'sympy_version':sp.__version__, 'controls':rows},indent=2))


if __name__ == '__main__':
    main()
