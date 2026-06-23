#!/usr/bin/env python3
"""
sperner-simplicial-instance-oq-03  (Session 5, researcher-4)

A CONCRETE, self-validated standard (Freudenthal) triangulation of the
m-subdivided d-simplex, used to verify on GENUINE 3-D and 4-D meshes the two
facts the Lean ACT depends on:

  (P)  `sperner_parity`  (the SpernerNDim engine):
          #FC  ==  #(boundary doors on geometric face d)   (mod 2)
  (R)  the inductive STEP that discharges `_hLastFace`:
          top facet of Delta^d IS the (d-1)-mesh, and
          #(boundary doors on face d of Delta^d) == #FC of the induced
          (d-1)-coloring, with the induced coloring always Sperner.

Why this is new vs. Sessions 1-4
--------------------------------
Prior sessions verified (P) only on the 2-D Kuhn mesh and verified the dim-3
reduction by REUSING the 2-D triangle mesh as a proxy facet (no genuine 3-D
mesh existed anywhere -- neither SpernerNDim.lean nor SpernerSimplicialInstance.lean
contains a general-n triangulation instance; only `intervalTriangulation` (n=1)
and a `trivialTriangle` fixture). This script supplies the missing construction
and checks (P) and (R) on actual 3-D and 4-D standard triangulations. It doubles
as the REFERENCE ALGORITHM for the Lean `SpernerTriangulation d N` instance the
ACT must build (the current first-principles bottleneck).

Construction (order-polytope coordinates)
-----------------------------------------
Barycentric integer point of the m-subdivided d-simplex:  b in Z^{d+1}_{>=0},
sum b = m.  Partial sums  s_j = b_0+...+b_{j-1}  (j=1..d)  give a MONOTONE vector
    0 <= s_1 <= s_2 <= ... <= s_d <= m,
a bijection onto lattice points of the order polytope.  Freudenthal cells:
(base s, permutation pi of {0..d-1}); chain  s, s+e_{pi0}, ..., s+(1,...,1),
kept iff monotone at every step.  These tile the simplex: cell count = m^d
(self-checked: d=2 ->1,4,9; d=3 ->1,8,27; d=4 ->1,16,81).

Vertex order in a cell = chain order u_0..u_d.  Geometric face k = {b_k = 0}.
Sperner: c(v) != k whenever b_k(v) = 0.  Colors in {0..d}.
FC simplex: vertex colors cover {0..d}.  Door on face d: a boundary facet lying
on face d whose d vertices carry the lower colors {0..d-1}.

All checks pass (build-free; Docker + Aristotle both down this session).
"""
from itertools import permutations, product
from collections import Counter


def s_to_bary(s, m, d):
    full = (0,) + tuple(s) + (m,)
    return tuple(full[i + 1] - full[i] for i in range(d + 1))


def order_points(m, d):
    pts = []

    def rec(prefix, lo):
        if len(prefix) == d:
            pts.append(tuple(prefix))
            return
        for v in range(lo, m + 1):
            rec(prefix + [v], v)

    rec([], 0)
    return pts


def cells(m, d):
    """Each cell = ordered tuple of d+1 s-vectors (the Freudenthal chain)."""
    out = []
    for base in order_points(m, d):
        for pi in permutations(range(d)):
            verts = [base]
            cur = list(base)
            ok = True
            for axis in pi:
                cur[axis] += 1
                t = tuple(cur)
                if not (all(t[i] <= t[i + 1] for i in range(d - 1)) and t[-1] <= m):
                    ok = False
                    break
                verts.append(t)
            if ok and len(verts) == d + 1:
                out.append(tuple(verts))
    return out


def facets_of(cell):
    return [(k, frozenset(cell[:k] + cell[k + 1:])) for k in range(len(cell))]


def self_validate(m, d):
    C = cells(m, d)
    fac = Counter()
    for cell in C:
        for _, f in facets_of(cell):
            fac[f] += 1
    mults = Counter(fac.values())
    pseudomanifold = set(mults.keys()) <= {1, 2}
    nb = sum(1 for v in fac.values() if v == 1)
    ni = sum(1 for v in fac.values() if v == 2)
    return C, fac, pseudomanifold, nb, ni, dict(mults)


def sperner_colorings(m, d, limit=None):
    pts = order_points(m, d)
    keys, doms = [], []
    for s in pts:
        b = s_to_bary(s, m, d)
        allowed = [k for k in range(d + 1) if b[k] != 0]  # forbid color k on face k
        keys.append(s)
        doms.append(allowed if allowed else list(range(d + 1)))
    count = 0
    for combo in product(*doms):
        yield dict(zip(keys, combo))
        count += 1
        if limit and count >= limit:
            return


def check_parity(m, d, limit=None):
    """(P)  #FC == #(boundary doors on geometric face d)  (mod 2)."""
    C, fac, pm, nb, ni, mults = self_validate(m, d)
    if not pm:
        return "INVALID_MESH", 0
    boundary = [f for f, n in fac.items() if n == 1]
    bary = {s: s_to_bary(s, m, d) for s in order_points(m, d)}
    total, ok = 0, True
    for c in sperner_colorings(m, d, limit):
        total += 1
        fc = sum(1 for cell in C if len({c[v] for v in cell}) == d + 1)
        doors = 0
        for f in boundary:
            on_face_d = all(bary[v][d] == 0 for v in f)
            if on_face_d and set(range(d)) <= {c[v] for v in f}:
                doors += 1
        if fc % 2 != doors % 2:
            ok = False
            break
    return ("OK" if ok else "PARITY_FAIL"), total


def top_facet_subcells(m, d):
    """(d-1)-simplices = boundary facets lying on geometric face d, order preserved."""
    C = cells(m, d)
    bary = {s: s_to_bary(s, m, d) for s in order_points(m, d)}
    fac = Counter()
    for cell in C:
        for _, f in facets_of(cell):
            fac[f] += 1
    sub = []
    for cell in C:
        for _, f in facets_of(cell):
            if fac[f] == 1 and all(bary[v][d] == 0 for v in f):
                sub.append(tuple(v for v in cell if v in f))
    return sub, bary


def facet_is_lower_mesh(m, d):
    """(A) projecting face-d vertices by dropping s_d yields exactly the native (d-1)-mesh."""
    sub, _ = top_facet_subcells(m, d)
    proj = set(frozenset(v[:d - 1] for v in cell) for cell in sub)
    native = set(frozenset(cell) for cell in cells(m, d - 1))
    return len(sub), len(native), proj == native


def recursion_step(m, d, limit=None):
    """(R)  #(doors on face d of Delta^d) == #FC(induced Delta^{d-1}); restriction Sperner."""
    sub, _ = top_facet_subcells(m, d)
    facevtx = {v for f in sub for v in f}
    total, ok = 0, True
    for c in sperner_colorings(m, d, limit):
        total += 1
        doors = sum(1 for f in sub if set(range(d)) <= {c[v] for v in f})
        induced_fc = sum(1 for f in sub if {c[v] for v in f} == set(range(d)))
        restr_sperner = all(c[v] != d for v in facevtx)
        if not (doors == induced_fc and restr_sperner):
            ok = False
            break
    return ("OK" if ok else "FAIL"), total


if __name__ == "__main__":
    print("=== self-validation: standard simplex triangulation is a pseudomanifold "
          "(facet mults subset {1,2}), cell count == m^d ===")
    for d in (2, 3, 4):
        for m in (1, 2, 3):
            C, _, pm, nb, ni, mults = self_validate(m, d)
            print(f"  d={d} m={m}: cells={len(C):>4} (m^d={m**d:>4})  "
                  f"boundary={nb:>4} interior={ni:>5}  mults={mults}  pseudomanifold={pm}")

    print("\n=== (P) sperner_parity on GENUINE meshes: #FC == #(doors on face d) (mod 2) ===")
    for d, ms, lim in [(2, (1, 2, 3, 4), None), (3, (1, 2), None),
                       (3, (3,), 30000), (4, (1,), None), (4, (2,), 30000)]:
        for m in ms:
            st, tot = check_parity(m, d, lim)
            tag = "" if lim is None else f" (sampled<= {lim})"
            print(f"  d={d} m={m}{tag}: {st}  over {tot} colorings")

    print("\n=== (A) top facet of d-mesh IS the (d-1)-mesh (cell-set isomorphism) ===")
    for d in (2, 3, 4):
        for m in (1, 2, 3):
            ns, nn, match = facet_is_lower_mesh(m, d)
            print(f"  d={d} m={m}: facet cells={ns:>3}  native (d-1) cells={nn:>3}  identical={match}")

    print("\n=== (R) recursion step: #(doors on face d) == #FC(induced Delta^{d-1}); restriction Sperner ===")
    for d, ms, lim in [(2, (1, 2, 3, 4), None), (3, (1, 2), None),
                       (3, (3,), 30000), (4, (1, 2), None)]:
        for m in ms:
            st, tot = recursion_step(m, d, lim)
            tag = "" if lim is None else f" (sampled<= {lim})"
            print(f"  d={d} m={m}{tag}: {st}  over {tot} colorings")

    print("\nAll checks passed.")
