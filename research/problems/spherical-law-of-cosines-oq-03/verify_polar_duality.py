#!/usr/bin/env python3
"""
spherical-law-of-cosines-oq-03  (researcher-1) — the POLAR-TRIANGLE DERIVATION
of the dual law (the structural "why" the OQ's significance line names but the
file never actually exhibits).

The file proves the primal law (cos c = cos a cos b + sin a sin b cos C) and the
dual law (cos C = −cos A cos B + sin A sin B cos c) INDEPENDENTLY (algebraic /
cross-product). The OQ's significance is "demonstrates the polar-triangle
duality" — but that duality is the statement that the dual law IS the primal law
applied to the POLAR (dual) triangle. This script exhibits exactly that.

## Polar triangle
For a spherical triangle with unit vertex vectors u, v, w, the polar triangle has
vertices
    u' = ± (v×w)/‖v×w‖,   v' = ± (w×u)/‖w×u‖,   w' = ± (u×v)/‖u×v‖,
sign chosen so each primed vertex lies in the same hemisphere as the original
(u'·u > 0, etc.). Classical duality:
    side a' (=∠v'w')  = π − A,    angle A'  = π − a,   and cyclically.
Hence the PRIMAL law on the polar triangle,
    cos a' = cos b' cos c' + sin b' sin c' cos A',
substituting a'=π−A, b'=π−B, c'=π−C, A'=π−a and using cos(π−x)=−cos x,
sin(π−x)=sin x, becomes
    −cos A = cos B cos C − sin B sin C cos a   ⟺   cos A = −cos B cos C + sin B sin C cos a,
the DUAL law. So dual(original) = primal(polar). This is the polar duality.

We verify on random spherical triangles (numpy):
  (1) the side/angle swap  a' = π−A, b' = π−B, c' = π−C, A' = π−a, B' = π−b, C' = π−c;
  (2) double polar: (T')' = T (involution);
  (3) primal law evaluated on the polar triangle == dual law on the original.

Docker-independent.  Requires numpy.
"""
import numpy as np

rng = np.random.default_rng(20260615)


def rand_triangle():
    """Three random unit vectors forming a nondegenerate spherical triangle."""
    while True:
        M = rng.standard_normal((3, 3))
        u, v, w = (r / np.linalg.norm(r) for r in M)
        # nondegenerate: pairwise non-parallel and positively oriented volume
        if abs(np.dot(np.cross(u, v), w)) > 0.15:
            return u, v, w


def sides(u, v, w):
    """Arc lengths a=∠(v,w), b=∠(u,w), c=∠(u,v)."""
    a = np.arccos(np.clip(np.dot(v, w), -1, 1))
    b = np.arccos(np.clip(np.dot(u, w), -1, 1))
    c = np.arccos(np.clip(np.dot(u, v), -1, 1))
    return a, b, c


def angles(u, v, w):
    """Vertex angles via the spherical law of cosines for sides."""
    a, b, c = sides(u, v, w)
    A = np.arccos(np.clip((np.cos(a) - np.cos(b) * np.cos(c)) / (np.sin(b) * np.sin(c)), -1, 1))
    B = np.arccos(np.clip((np.cos(b) - np.cos(a) * np.cos(c)) / (np.sin(a) * np.sin(c)), -1, 1))
    C = np.arccos(np.clip((np.cos(c) - np.cos(a) * np.cos(b)) / (np.sin(a) * np.sin(b)), -1, 1))
    return A, B, C


def polar(u, v, w):
    """Polar triangle vertices, hemisphere-sign-fixed."""
    up = np.cross(v, w); up = up / np.linalg.norm(up) * np.sign(np.dot(np.cross(v, w), u))
    vp = np.cross(w, u); vp = vp / np.linalg.norm(vp) * np.sign(np.dot(np.cross(w, u), v))
    wp = np.cross(u, v); wp = wp / np.linalg.norm(wp) * np.sign(np.dot(np.cross(u, v), w))
    return up, vp, wp


if __name__ == "__main__":
    print("spherical-law-of-cosines-oq-03 :: polar-triangle derivation of the dual law")
    print("=" * 76)
    e_swap = e_invol = e_dual = 0.0
    N = 200000
    for _ in range(N):
        u, v, w = rand_triangle()
        a, b, c = sides(u, v, w)
        A, B, C = angles(u, v, w)
        up, vp, wp = polar(u, v, w)
        ap, bp, cp = sides(up, vp, wp)
        Ap, Bp, Cp = angles(up, vp, wp)
        # (1) side/angle swap a' = π - A, A' = π - a, cyclic
        e_swap = max(e_swap,
                     abs(ap - (np.pi - A)), abs(bp - (np.pi - B)), abs(cp - (np.pi - C)),
                     abs(Ap - (np.pi - a)), abs(Bp - (np.pi - b)), abs(Cp - (np.pi - c)))
        # (2) involution: polar of polar == original (up to the sign-fix => same triangle)
        upp, vpp, wpp = polar(up, vp, wp)
        e_invol = max(e_invol, np.linalg.norm(upp - u), np.linalg.norm(vpp - v), np.linalg.norm(wpp - w))
        # (3) PRIMAL law on polar triangle reproduces DUAL law on original.
        #     primal-on-polar: cos a' = cos b' cos c' + sin b' sin c' cos A'
        primal_polar = np.cos(ap) - (np.cos(bp) * np.cos(cp) + np.sin(bp) * np.sin(cp) * np.cos(Ap))
        #     dual-on-original (the OQ statement): cos A = -cos B cos C + sin B sin C cos a
        dual_orig = np.cos(A) - (-np.cos(B) * np.cos(C) + np.sin(B) * np.sin(C) * np.cos(a))
        # both must be ~0, AND primal-on-polar is algebraically the dual-on-original
        # after the π-x substitution: verify the substituted identity directly
        subst = (-np.cos(A)) - (np.cos(B) * np.cos(C) - np.sin(B) * np.sin(C) * np.cos(a))
        e_dual = max(e_dual, abs(primal_polar), abs(dual_orig), abs(subst))
    print(f"random nondegenerate spherical triangles: {N}")
    print(f"  (1) side/angle swap  a'=π−A, A'=π−a (cyclic):      max err = {e_swap:.2e}")
    print(f"  (2) involution  (polar)²  = identity:               max err = {e_invol:.2e}")
    print(f"  (3) primal(polar) ≡ dual(original) [OQ statement]:  max err = {e_dual:.2e}")
    print("-" * 76)
    ok = e_swap < 1e-9 and e_invol < 1e-9 and e_dual < 1e-9
    print("RESULT:", "PASS — the dual law IS the primal law of the polar triangle" if ok else "FAIL")
    print("This exhibits the polar-triangle duality the OQ's significance names:")
    print("  dual_law(T)  =  primal_law(polar T)  under  side↔π−angle, angle↔π−side.")
