#!/usr/bin/env python3
"""
Durable numerical verification for spherical-law-of-cosines-oq-03
(the DUAL / angles law of cosines) and the vector identities the Lean
proof `proofs/Proofs/SphericalLawOfCosinesOQ03.lean` relies on.

Verifies, over random spherical triangles (unit vectors u, v, w in R^3):

  1. Dual law (trig form):   cos C = -cos A cos B + sin A sin B cos c
  2. Binet-Cauchy:           <BxC, CxA> = <B,C><C,A> - <A,B><C,C>
  3. ||v x w|| = sin a       (side sine = norm of the cross product)
  4. cos(interior C) = -<NA,NB>/(||NA|| ||NB||),  NA=BxC, NB=CxA
  5. triple product squared = Gram determinant
  6. normal forms:  cos A = (ca - cb cc)/(sb sc),  sin A = |[u v w]|/(sb sc)
  7. the cleared polynomial identity proved by `ring` in `dual_poly`:
       (cc - ca cb)(1-cc^2) = -(ca-cb cc)(cb-ca cc)
                               + (1-ca^2-cb^2-cc^2+2 ca cb cc) cc
  8. the geometric cleared identity `dual_spherical_law_cleared`:
       (cc - ca cb)(1-cc^2) = -(ca-cb cc)(cb-ca cc) + [u v w]^2 cc

Interior angles are computed independently via tangent projections at each
vertex (the parent file's `angleC` definition), so the normal forms in (6)
are a genuine cross-check, not a tautology.

Run:  python3 research/scripts/verify-spherical-dual.py
Exit code 0 on success (all max errors below tolerance).
"""
import numpy as np

TOL = 1e-9
N = 300_000
DEGEN = 1e-6  # skip near-degenerate triangles (a side sine near 0)


def rand_unit(rng):
    v = rng.normal(size=3)
    return v / np.linalg.norm(v)


def angle_at(P, Q, R):
    """Interior angle at vertex P of the spherical triangle, between the
    great-circle arcs PQ and PR, via tangent (perpendicular) projections."""
    tq = Q - np.dot(Q, P) * P
    tr = R - np.dot(R, P) * P
    nq, nr = np.linalg.norm(tq), np.linalg.norm(tr)
    if nq < 1e-12 or nr < 1e-12:
        return None
    return np.arccos(np.clip(np.dot(tq, tr) / (nq * nr), -1.0, 1.0))


def main():
    rng = np.random.default_rng(20260614)
    errs = {k: 0.0 for k in
            ["dual", "binet", "norm_sin", "cos_normal_pair",
             "triple_gram", "cosA_nf", "sinA_nf", "poly", "geom_cleared"]}
    checks = 0
    for _ in range(N):
        A, B, C = rand_unit(rng), rand_unit(rng), rand_unit(rng)
        ca, cb, cc = np.dot(B, C), np.dot(C, A), np.dot(A, B)  # cos a, cos b, cos c
        if min(1 - ca * ca, 1 - cb * cb, 1 - cc * cc) < DEGEN:
            continue
        a = np.arccos(np.clip(ca, -1, 1))
        sa, sb, sc = np.sqrt(1 - ca * ca), np.sqrt(1 - cb * cb), np.sqrt(1 - cc * cc)

        Aang, Bang, Cang = angle_at(A, B, C), angle_at(B, C, A), angle_at(C, A, B)
        if Aang is None or Bang is None or Cang is None:
            continue

        # (1) dual law
        lhs = np.cos(Cang)
        rhs = -np.cos(Aang) * np.cos(Bang) + np.sin(Aang) * np.sin(Bang) * cc
        errs["dual"] = max(errs["dual"], abs(lhs - rhs))

        # cross products / normals
        NA, NB, NC = np.cross(B, C), np.cross(C, A), np.cross(A, B)

        # (2) Binet-Cauchy
        errs["binet"] = max(errs["binet"], abs(np.dot(NA, NB) - (ca * cb - cc)))
        # (3) ||v x w|| = sin(side)
        errs["norm_sin"] = max(errs["norm_sin"], abs(np.linalg.norm(NA) - sa))
        # (4) cos(interior C) via normals
        val = -np.dot(NA, NB) / (np.linalg.norm(NA) * np.linalg.norm(NB))
        errs["cos_normal_pair"] = max(errs["cos_normal_pair"], abs(np.cos(Cang) - val))

        # (5) triple^2 = Gram det
        tp = np.dot(A, np.cross(B, C))
        gram = 1 - ca * ca - cb * cb - cc * cc + 2 * ca * cb * cc
        errs["triple_gram"] = max(errs["triple_gram"], abs(tp * tp - gram))

        # (6) normal forms for the angle at A (independent cross-check)
        errs["cosA_nf"] = max(errs["cosA_nf"], abs(np.cos(Aang) - (ca - cb * cc) / (sb * sc)))
        errs["sinA_nf"] = max(errs["sinA_nf"], abs(np.sin(Aang) - abs(tp) / (sb * sc)))

        # (7) dual_poly (ring identity)
        pl = (cc - ca * cb) * (1 - cc * cc)
        pr = -(ca - cb * cc) * (cb - ca * cc) + gram * cc
        errs["poly"] = max(errs["poly"], abs(pl - pr))

        # (8) dual_spherical_law_cleared (geometric, with actual triple product)
        gl = (cc - ca * cb) * (1 - cc * cc)
        gr = -(ca - cb * cc) * (cb - ca * cc) + (tp * tp) * cc
        errs["geom_cleared"] = max(errs["geom_cleared"], abs(gl - gr))

        checks += 1

    print(f"checks: {checks}")
    ok = True
    for k, e in errs.items():
        status = "PASS" if e < TOL else "FAIL"
        if e >= TOL:
            ok = False
        print(f"  [{status}] {k:18s} max err = {e:.3e}")
    print("ALL PASS" if ok else "SOME FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
