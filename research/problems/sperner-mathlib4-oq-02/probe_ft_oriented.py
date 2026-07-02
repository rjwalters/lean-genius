#!/usr/bin/env python3
"""
Oriented Freund-Todd door seed on the hexagon boundary + interior degree structure.

Research probe for sperner-mathlib4-oq-02.  Follow-up to probe_ft_pathfollowing.py,
which established (over all 256 labelings):
  * the {+1,-1} exact-complementary door rule -> rooms all degree <=2 (paths/cycles),
    BUT hemisphere {+1,-1} boundary-door count is NOT parity-invariant (even 176/odd 80);
  * so the odd boundary seed is not the raw {+1,-1} count.

This probe tests the ORIENTED refinements (which researcher-7 pointed at abstractly)
and the sign-flip interior degree structure, to pin down exactly which boundary count
is invariantly ODD and which interior door rule terminates.

Encoding identical to Lean:  Fin4 0->+1,1->+2,2->-1,3->-2 ; negL=[2,3,0,1] ;
v(i+3)=-v(i) antipodal ; hemisphere arc = boundary edges b0,b1,b2 (v0->v1->v2->v3=-v0).
"""
from itertools import product

negL = [2, 3, 0, 1]
def sgnbit(x):  # ZMod2 sign: {+1,+2}->0, {-1,-2}->1   (Fin4 0,1 -> 0 ; 2,3 -> 1)
    return 0 if x < 2 else 1
def signed(x):
    return [1, 2, -1, -2][x]

def Vlabels(a, b, c):
    return [a, b, c, negL[a], negL[b], negL[c]]

# ---- candidate boundary seeds on the HEMISPHERE arc b0,b1,b2 (v0..v3) ----
def seed_counts(a, b, c):
    V = Vlabels(a, b, c)
    arc = [(V[i], V[i + 1]) for i in range(3)]     # v0->v1, v1->v2, v2->v3
    out = {}
    # (1) sign-flip edges (sgn bit differs) -- the VERIFIED odd seed (arc_sign_changes)
    out['signflip'] = sum(1 for (x, y) in arc if sgnbit(x) != sgnbit(y))
    # (2) raw {+1,-1} complementary edges
    out['pm1_raw'] = sum(1 for (x, y) in arc if {signed(x), signed(y)} == {1, -1})
    # (3) directed +1 -> -1 edges
    out['pm1_dir'] = sum(1 for (x, y) in arc if signed(x) == 1 and signed(y) == -1)
    # (4) directed positive-sign -> negative-sign (sgn 0 -> 1)
    out['sgn_dir_pos_to_neg'] = sum(1 for (x, y) in arc if sgnbit(x) == 0 and sgnbit(y) == 1)
    # (5) directed negative -> positive
    out['sgn_dir_neg_to_pos'] = sum(1 for (x, y) in arc if sgnbit(x) == 1 and sgnbit(y) == 0)
    # (6) any complementary edge {+k,-k}
    out['comp_any'] = sum(1 for (x, y) in arc if signed(x) == -signed(y))
    return out

# ---- interior degree via sign-flip doors on the full disk ----
def triangle_signflip_doors(i, V, d):
    """sides of T_i=(c,v_i,v_{i+1}) that are sign-flip edges."""
    labs = [(d, V[i]), (d, V[(i + 1) % 6]), (V[i], V[(i + 1) % 6])]
    return [k for k, (x, y) in enumerate(labs) if sgnbit(x) != sgnbit(y)]

def main():
    keys = ['signflip', 'pm1_raw', 'pm1_dir', 'sgn_dir_pos_to_neg',
            'sgn_dir_neg_to_pos', 'comp_any']
    parity = {k: {'even': 0, 'odd': 0} for k in keys}
    # interior sign-flip door degree histogram over all triangles+labelings
    signflip_tri_deg = {}
    total = 0
    for a, b, c in product(range(4), repeat=3):
        total += 1
        sc = seed_counts(a, b, c)
        for k in keys:
            parity[k]['odd' if sc[k] % 2 else 'even'] += 1
        V = Vlabels(a, b, c)
        for d in range(4):
            for i in range(6):
                dg = len(triangle_signflip_doors(i, V, d))
                signflip_tri_deg[dg] = signflip_tri_deg.get(dg, 0) + 1

    print(f"free boundary labelings (a,b,c): {total}")
    print("\nHEMISPHERE-arc boundary seed parity (want a candidate that is 100% ODD):")
    for k in keys:
        p = parity[k]
        inv = 'ODD-invariant' if p['even'] == 0 else ('EVEN-invariant' if p['odd'] == 0 else 'mixed')
        print(f"  {k:22s}: even={p['even']:3d} odd={p['odd']:3d}   [{inv}]")
    print("\nInterior sign-flip-door degree per triangle (all 256*6 triangles):")
    print(f"  histogram: {signflip_tri_deg}")
    print("  -> sign-flip doors give degrees:", sorted(signflip_tri_deg),
          "(if only {0,2}: pure sign-flip graph is ALL cycles, no interior endpoint)")

if __name__ == '__main__':
    main()
