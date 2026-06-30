#!/usr/bin/env python3
"""
Durable, build-free verification for spherical-law-of-cosines-oq-03:

    "Dual spherical law of cosines (angles version)"

The gallery proves the SIDE law (`SphericalLawOfCosines.lean`):
    cos c = cos a cos b + sin a sin b cos C.
OQ-03 asks for the DUAL (polar) law relating the three ANGLES A,B,C and one side:
    cos C = − cos A cos B + sin A sin B cos c.

This script confirms, on random spherical triangles (3 random unit vectors), with
the SAME vertex/side/angle conventions as the Lean file:
  - vertex A,B,C are unit vectors; side a = arc(B,C), b = arc(C,A), c = arc(A,B);
  - angle at a vertex = dihedral angle = angle between the perpendicular projections
    of the other two vertices onto the vertex (matches Lean `angleC` via projectPerp).

Checks:
  (1) SIDE law (sanity, matches the proven Lean theorem):
        cos c == cos a cos b + sin a sin b cos C   (and cyclic).
  (2) DUAL/ANGLE law (the OQ-03 target):
        cos C == − cos A cos B + sin A sin B cos c  (and cyclic).
  (3) POLAR-DUALITY route: build the polar triangle (vertices = unit normals to the
      face planes, sign-fixed); its sides = π − (original angles) and its angles =
      π − (original sides). Applying the SIDE law to the polar triangle IS the dual
      law — confirming the intended proof path.

Run: python3 verify_dual_law.py
"""

import math
import random


def dot(u, v):
    return sum(a * b for a, b in zip(u, v))


def norm(u):
    return math.sqrt(dot(u, u))


def normalize(u):
    n = norm(u)
    return tuple(a / n for a in u)


def cross(u, v):
    return (u[1] * v[2] - u[2] * v[1],
            u[2] * v[0] - u[0] * v[2],
            u[0] * v[1] - u[1] * v[0])


def sub(u, v):
    return tuple(a - b for a, b in zip(u, v))


def scale(u, s):
    return tuple(a * s for a in u)


def arc(u, v):
    """Arc length between unit vectors = angle in [0,pi]."""
    return math.acos(max(-1.0, min(1.0, dot(u, v))))


def project_perp(u, n):
    """Component of u perpendicular to unit vector n (matches Lean projectPerp)."""
    return sub(u, scale(n, dot(u, n)))


def vertex_angle(P, Q, R):
    """Interior angle of the spherical triangle at vertex P (between sides PQ, PR).
       = angle between projections of Q and R perpendicular to P (dihedral angle)."""
    q = project_perp(Q, P)
    r = project_perp(R, P)
    nq, nr = norm(q), norm(r)
    c = dot(q, r) / (nq * nr)
    return math.acos(max(-1.0, min(1.0, c)))


def random_unit(rng):
    while True:
        v = (rng.gauss(0, 1), rng.gauss(0, 1), rng.gauss(0, 1))
        if norm(v) > 1e-6:
            return normalize(v)


def polar_triangle(A, B, C):
    """Polar (dual) triangle: each vertex is the unit normal to the opposite face
       plane, signed so that it lies in the same hemisphere as the opposite vertex.
       A' is normal to plane(B,C) with A'·A > 0, etc."""
    Ap = normalize(cross(B, C))
    if dot(Ap, A) < 0:
        Ap = scale(Ap, -1)
    Bp = normalize(cross(C, A))
    if dot(Bp, B) < 0:
        Bp = scale(Bp, -1)
    Cp = normalize(cross(A, B))
    if dot(Cp, C) < 0:
        Cp = scale(Cp, -1)
    return Ap, Bp, Cp


TOL = 1e-9


def check_triangle(A, B, C):
    # sides (opposite the like-named vertex)
    a = arc(B, C)
    b = arc(C, A)
    c = arc(A, B)
    # angles at vertices
    Aang = vertex_angle(A, B, C)
    Bang = vertex_angle(B, C, A)
    Cang = vertex_angle(C, A, B)

    res = {}

    # (1) side law: cos c = cos a cos b + sin a sin b cos C  (+ cyclic)
    s1 = abs(math.cos(c) - (math.cos(a) * math.cos(b) + math.sin(a) * math.sin(b) * math.cos(Cang)))
    s2 = abs(math.cos(a) - (math.cos(b) * math.cos(c) + math.sin(b) * math.sin(c) * math.cos(Aang)))
    s3 = abs(math.cos(b) - (math.cos(c) * math.cos(a) + math.sin(c) * math.sin(a) * math.cos(Bang)))
    res["side_law"] = max(s1, s2, s3)

    # (2) dual/angle law: cos C = - cos A cos B + sin A sin B cos c  (+ cyclic)
    d1 = abs(math.cos(Cang) - (-math.cos(Aang) * math.cos(Bang) + math.sin(Aang) * math.sin(Bang) * math.cos(c)))
    d2 = abs(math.cos(Aang) - (-math.cos(Bang) * math.cos(Cang) + math.sin(Bang) * math.sin(Cang) * math.cos(a)))
    d3 = abs(math.cos(Bang) - (-math.cos(Cang) * math.cos(Aang) + math.sin(Cang) * math.sin(Aang) * math.cos(b)))
    res["dual_law"] = max(d1, d2, d3)

    # (3) polar-duality relations: polar sides = pi - original angles;
    #     polar angles = pi - original sides.
    Ap, Bp, Cp = polar_triangle(A, B, C)
    pa = arc(Bp, Cp); pb = arc(Cp, Ap); pc = arc(Ap, Bp)
    pA = vertex_angle(Ap, Bp, Cp); pB = vertex_angle(Bp, Cp, Ap); pC = vertex_angle(Cp, Ap, Bp)
    # polar side a' opposite A' ; relation: a' = pi - A  (angle at original vertex A)
    rel_sides = max(abs(pa - (math.pi - Aang)), abs(pb - (math.pi - Bang)), abs(pc - (math.pi - Cang)))
    rel_angles = max(abs(pA - (math.pi - a)), abs(pB - (math.pi - b)), abs(pC - (math.pi - c)))
    res["polar_sides"] = rel_sides
    res["polar_angles"] = rel_angles

    return res


def main():
    rng = random.Random(20260614)
    worst = {"side_law": 0.0, "dual_law": 0.0, "polar_sides": 0.0, "polar_angles": 0.0}
    N = 0
    fails = 0
    for _ in range(20000):
        A = random_unit(rng); B = random_unit(rng); C = random_unit(rng)
        # skip near-degenerate (collinear / coincident) triangles
        if norm(cross(sub(B, A), sub(C, A))) < 1e-3:
            continue
        # skip triangles with a tiny side (angle near 0) for numeric safety
        if min(arc(B, C), arc(C, A), arc(A, B)) < 1e-3:
            continue
        r = check_triangle(A, B, C)
        N += 1
        for k in worst:
            worst[k] = max(worst[k], r[k])
        if r["dual_law"] > 1e-7 or r["side_law"] > 1e-7:
            fails += 1

    print("=" * 70)
    print("spherical-law-of-cosines-oq-03  —  dual (polar) law, angles version")
    print("=" * 70)
    print(f"random non-degenerate spherical triangles tested: {N}")
    print(f"  (1) side law   cos c = cos a cos b + sin a sin b cos C   max err = {worst['side_law']:.2e}")
    print(f"  (2) DUAL law   cos C = -cos A cos B + sin A sin B cos c   max err = {worst['dual_law']:.2e}")
    print(f"  (3) polar sides   a' = pi - A   (cyclic)                 max err = {worst['polar_sides']:.2e}")
    print(f"  (3) polar angles  A' = pi - a   (cyclic)                 max err = {worst['polar_angles']:.2e}")
    ok = all(v < 1e-7 for v in worst.values()) and fails == 0
    print("-" * 70)
    print("RESULT:", "ALL CHECKS PASS (identities hold to ~1e-9)" if ok else f"FAILURES: {fails}")
    print("=" * 70)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
