#!/usr/bin/env python3
"""
spherical-law-of-cosines-oq-03 (researcher-3) — EXACT symbolic certificate for
Part VII: the dual law in POLAR form (`dual_law_polar_form`).

Part VII of `proofs/Proofs/SphericalLawOfCosinesOQ03.lean` realises the polar-triangle
duality the OQ's significance line names: the (unnormalised) polar vertices are the edge
normals  U = v×w,  V = w×u,  W = u×v,  and the dual law of the original triangle is a
side-law-shaped relation among them.

This script certifies, EXACTLY (sympy, no floating point), the two facts the Lean proof
relies on:

  (A) the polar inner-product identities are component-wise polynomial identities in the
      vertex coordinates, under the unit constraints ⟨u,u⟩=⟨v,v⟩=⟨w,w⟩=1:
        ⟨v×w, w×u⟩ = cos a·cos b − cos c          (polar_inner_uv)
        ⟨w×u, u×v⟩ = cos b·cos c − cos a          (polar_inner_vw)
        ⟨u×v, v×w⟩ = cos c·cos a − cos b          (polar_inner_wu)
      where cos a=⟨v,w⟩, cos b=⟨w,u⟩, cos c=⟨u,v⟩;

  (B) the capstone `linear_combination dual_spherical_law_cleared` certificate has
      residual identically 0:
        (goal_lhs − goal_rhs) − (dscl_lhs − dscl_rhs) ≡ 0.

Docker-independent. Requires sympy.
"""
import sympy as sp


def dot(a, b):
    return a[0] * b[0] + a[1] * b[1] + a[2] * b[2]


def cross(a, b):
    return (a[1] * b[2] - a[2] * b[1],
            a[2] * b[0] - a[0] * b[2],
            a[0] * b[1] - a[1] * b[0])


def part_A():
    u = sp.symbols('u1 u2 u3')
    v = sp.symbols('v1 v2 v3')
    w = sp.symbols('w1 w2 w3')

    ca = dot(v, w)   # cos a
    cb = dot(w, u)   # cos b
    cc = dot(u, v)   # cos c

    # Unit constraints; substitute ⟨w,w⟩, ⟨u,u⟩, ⟨v,v⟩ = 1 where they appear.
    # binet_cauchy is an unconditional identity, so each polar inner product equals a
    # polynomial that contains exactly one ⟨·,·⟩=1 self-term; we verify the reduction by
    # checking the difference vanishes on the unit variety via the Gröbner-free route:
    # expand the cross-product inner product and the claimed RHS, then substitute the
    # self-dot = 1 relations and confirm equality.
    subs_unit = []
    # we cannot literally set ⟨w,w⟩=1 as a single symbol; instead verify the binet form:
    #   ⟨v×w, w×u⟩ = ⟨v,w⟩⟨w,u⟩ − ⟨v,u⟩⟨w,w⟩   (unconditional)
    # then with ⟨w,w⟩=1 this is ca·cb − cc. Check the unconditional binet identity first.
    checks = {
        'binet ⟨v×w,w×u⟩': (dot(cross(v, w), cross(w, u))
                            - (dot(v, w) * dot(w, u) - dot(v, u) * dot(w, w))),
        'binet ⟨w×u,u×v⟩': (dot(cross(w, u), cross(u, v))
                            - (dot(w, u) * dot(u, v) - dot(w, v) * dot(u, u))),
        'binet ⟨u×v,v×w⟩': (dot(cross(u, v), cross(v, w))
                            - (dot(u, v) * dot(v, w) - dot(u, w) * dot(v, v))),
    }
    ok = True
    for name, expr in checks.items():
        z = sp.expand(expr)
        print(f'  {name}: residual = {z}  ->  {"OK" if z == 0 else "FAIL"}')
        ok = ok and (z == 0)
    # With ⟨w,w⟩=⟨u,u⟩=⟨v,v⟩=1 the binet RHS collapses to the claimed polar forms:
    #   ca·cb − ⟨v,u⟩ = ca·cb − cc, etc. (⟨v,u⟩=⟨u,v⟩=cc). Symbolically obvious.
    print('  (under unit constraints the binet RHS = ca·cb−cc, cb·cc−ca, cc·ca−cb)')
    return ok


def part_B():
    ca, cb, cc = sp.symbols('ca cb cc')   # cos a, cos b, cos c
    tp2 = 1 - ca**2 - cb**2 - cc**2 + 2 * ca * cb * cc   # [u v w]^2 (unit vectors)

    # dual_spherical_law_cleared (unit form)
    dscl_lhs = (cc - ca * cb) * (1 - cc**2)
    dscl_rhs = -(ca - cb * cc) * (cb - ca * cc) + tp2 * cc

    # polar inner products after rewrites
    puv = ca * cb - cc          # ⟨v×w, w×u⟩
    pvw = cb * cc - ca          # ⟨w×u, u×v⟩
    pwu = cc * ca - cb          # ⟨u×v, v×w⟩
    pww = 1 - cc**2             # ⟨u×v, u×v⟩

    # capstone goal:  -puv*pww = -pvw*pwu + tp2*cc
    goal_lhs = -puv * pww
    goal_rhs = -pvw * pwu + tp2 * cc

    residual = sp.expand((goal_lhs - goal_rhs) - (dscl_lhs - dscl_rhs))
    print(f'  dscl identity holds: {sp.simplify(dscl_lhs - dscl_rhs) == 0}')
    print(f'  capstone residual (linear_combination dscl): {residual}  ->  '
          f'{"OK" if residual == 0 else "FAIL"}')
    print(f'  capstone identity holds: {sp.simplify(goal_lhs - goal_rhs) == 0}')
    return residual == 0


if __name__ == '__main__':
    print('Part (A): polar inner-product identities (binet_cauchy, component-wise):')
    a_ok = part_A()
    print('\nPart (B): capstone linear_combination certificate:')
    b_ok = part_B()
    print('\nALL EXACT CHECKS PASS' if (a_ok and b_ok) else '\nFAILURE')
