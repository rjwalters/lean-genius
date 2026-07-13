#!/usr/bin/env python3
"""
Durable verification cert for abel-ruffini-oq-04-oq-02-oq-04.

OQ: the parent `solvable_iff_le_four` classifies Sₙ (solvable iff n ≤ 4). Extend
the *paradigm* to other infinite families:
  * dihedral Dₙ  -- solvable for ALL n (cyclic rotation subgroup of index 2);
  * GL₂(𝔽_q)     -- NOT solvable once |𝔽_q| ≥ 4 (PSL₂ is simple non-abelian).

This cert decides solvability the definitional way (Mathlib's `IsSolvable` =
derived series eventually trivial): it computes the derived series
  D₀ = G,  D_{k+1} = ⟨ [x,y] : x,y ∈ D_k ⟩
and reports SOLVABLE iff some D_k = {1}, else NOT-SOLVABLE (the series stabilizes
at a nontrivial perfect subgroup -- the "obstruction core").

It is a regression oracle for a future Lean formalization and pins the exact
boundary the OQ asks about. Pure stdlib; the largest group is GL₂(𝔽₅) (order 480).
"""

from itertools import product as iproduct


def derived_series_solvable(elements, mul, inv, e, name, max_steps=12):
    """elements: iterable of group elements (hashable). mul/inv/e: group ops.
    Returns (is_solvable, derived_length_or_None, core_size)."""
    G = frozenset(elements)

    def closure(gens):
        gens = set(gens)
        gens.add(e)
        elems = set(gens)
        frontier = list(gens)
        while frontier:
            x = frontier.pop()
            for g in list(gens):
                for prod in (mul(x, g), mul(g, x)):
                    if prod not in elems:
                        elems.add(prod)
                        frontier.append(prod)
        return frozenset(elems)

    def commutator_subgroup(H):
        comms = set()
        Hl = list(H)
        for x in Hl:
            xi = inv(x)
            for y in Hl:
                # [x,y] = x y x^-1 y^-1
                comms.add(mul(mul(x, y), mul(xi, inv(y))))
        return closure(comms)

    D = G
    for k in range(max_steps):
        if len(D) == 1:
            print(f"[SOLVABLE]     {name}: |G|={len(G)}, derived length {k}")
            return True, k, 1
        nxt = commutator_subgroup(D)
        if nxt == D:
            print(f"[NOT-SOLVABLE] {name}: |G|={len(G)}, derived series stabilizes "
                  f"at a perfect core of size {len(D)} != 1")
            return False, None, len(D)
        D = nxt
    print(f"[INCONCLUSIVE] {name}: did not stabilize in {max_steps} steps")
    return None, None, len(D)


# ---------- dihedral group D_n (order 2n) ----------
def dihedral(n):
    # element (s, k): s in {0,1} reflection flag, k in Z_n.
    elems = [(s, k) for s in (0, 1) for k in range(n)]
    e = (0, 0)

    def mul(a, b):
        s1, k1 = a
        s2, k2 = b
        if s1 == 0:
            return (s2, (k1 + k2) % n)
        else:
            return (1 - s2, (k1 - k2) % n)

    def inv(a):
        s, k = a
        return (0, (-k) % n) if s == 0 else (1, k)  # reflections are involutions

    return elems, mul, inv, e


# ---------- general linear group GL_2(F_p), p prime ----------
def gl2(p):
    e = (1, 0, 0, 1)

    def det(m):
        a, b, c, d = m
        return (a * d - b * c) % p

    elems = [m for m in iproduct(range(p), repeat=4) if det(m) != 0]

    def mul(x, y):
        a, b, c, d = x
        e1, f1, g1, h1 = y
        return ((a * e1 + b * g1) % p, (a * f1 + b * h1) % p,
                (c * e1 + d * g1) % p, (c * f1 + d * h1) % p)

    def inv(m):
        a, b, c, d = m
        di = pow(det(m), p - 2, p)  # Fermat inverse of the determinant
        return ((d * di) % p, (-b * di) % p, (-c * di) % p, (a * di) % p)

    return elems, mul, inv, e


def main():
    print("=== Dihedral D_n: solvable for ALL n (claim: derived length <= 2) ===")
    dih_ok = True
    for n in (3, 4, 5, 6, 7, 8):
        elems, mul, inv, e = dihedral(n)
        ok, dl, _ = derived_series_solvable(elems, mul, inv, e, f"D_{n}")
        dih_ok = dih_ok and (ok is True) and (dl is not None and dl <= 2)

    print("\n=== GL_2(F_p): solvable for p<=3, NOT solvable for p>=5 ===")
    expect = {2: True, 3: True, 5: False}   # p=5: PSL_2(F_5) ~ A_5 simple
    gl_ok = True
    for p in (2, 3, 5):
        elems, mul, inv, e = gl2(p)
        ok, _, _ = derived_series_solvable(elems, mul, inv, e, f"GL_2(F_{p})")
        gl_ok = gl_ok and (ok is expect[p])

    print("\n=== RESULT ===")
    if dih_ok and gl_ok:
        print("ALL CHECKS PASSED.")
        print(" * D_n solvable for n=3..8 with derived length <= 2 (cyclic-by-C2).")
        print(" * GL_2(F_2), GL_2(F_3) solvable; GL_2(F_5) NOT solvable")
        print("   (derived series stabilizes at SL_2(F_5), order 120, perfect;")
        print("    PSL_2(F_5) ~ A_5 is simple non-abelian -- the obstruction).")
        print(" * Boundary note: GL_2(F_4) is also NOT solvable (PSL_2(F_4) ~ A_5);")
        print("   not computed here to avoid GF(4) arithmetic. So the OQ's |F|>=4")
        print("   threshold is exact. See knowledge.md for the Mathlib bearers.")
    else:
        print(f"FAILURES: dihedral_ok={dih_ok}, gl_ok={gl_ok}")
        raise SystemExit(1)


if __name__ == "__main__":
    main()
