#!/usr/bin/env python3
"""
Freund-Todd / Prescott-Su almost-complementary path-following on the hexagon.

Research probe for sperner-mathlib4-oq-02 ("Tucker's lemma and Borsuk-Ulam
from abstract door-counting").

GOAL: The abstract engine (SpernerTuckerPathFollowing.exists_interior_degree_one)
needs a max-degree-<=2 graph on "rooms" whose degree-1 boundary endpoints are ODD
in count, then hands back an interior degree-1 room -- the Tucker witness.

Prior sessions VERIFIED (in Lean, 0-axiom):
  * the odd boundary seed is the HEMISPHERE SIGN-DEGREE (arc_sign_changes_odd),
    NOT any unsigned complementary-edge count (which is even / non-invariant);
  * the full all-signs complementary-EDGE door graph IS paths-and-cycles
    (hsimplex/hdoor), but its boundary doors are even -> engine can't fire on it.

This probe checks the {+1,-1} exact-complementary door rule directly:
does it give (a) rooms of degree <=2, (b) an ODD hemisphere boundary seed?

Encoding identical to Lean:  Fin4 0->+1,1->+2,2->-1,3->-2 ; negL=[2,3,0,1] ;
v(i+3)=-v(i) antipodal ; hemisphere arc = boundary edges b0,b1,b2.
Triangles T_i=(centre, v_i, v_{i+1}); spokes s_i={c,v_i}; boundary b_i={v_i,v_{i+1}}.
"""
from itertools import product

negL = [2, 3, 0, 1]
def signed(x):
    return [1, 2, -1, -2][x]

def boundary_labels(a, b, c):
    return [a, b, c, negL[a], negL[b], negL[c]]

def has_complementary_edge(V, d):
    for i in range(6):
        if signed(d) == -signed(V[i]):
            return True
    for i in range(6):
        if signed(V[i]) == -signed(V[(i + 1) % 6]):
            return True
    return False

def edge_is_pm1_door(lx, ly):
    return {signed(lx), signed(ly)} == {1, -1}

def triangle_doors(i, V, d):
    lab_c, lab_i, lab_j = d, V[i], V[(i + 1) % 6]
    doors = []
    if edge_is_pm1_door(lab_c, lab_i):
        doors.append(('s', i))
    if edge_is_pm1_door(lab_c, lab_j):
        doors.append(('s', (i + 1) % 6))
    if edge_is_pm1_door(lab_i, lab_j):
        doors.append(('b', i))
    return doors

def main():
    maxdeg_hist = {}
    half_even = half_odd = all_even = all_odd = 0
    has_comp_all = True
    total = 0
    for a, b, c, d in product(range(4), repeat=4):
        total += 1
        V = boundary_labels(a, b, c)
        md = max((len(triangle_doors(i, V, d)) for i in range(6)), default=0)
        maxdeg_hist[md] = maxdeg_hist.get(md, 0) + 1
        bdoors_all = [i for i in range(6) if edge_is_pm1_door(V[i], V[(i + 1) % 6])]
        bdoors_half = [i for i in (0, 1, 2) if edge_is_pm1_door(V[i], V[(i + 1) % 6])]
        (half_odd, half_even) = (half_odd + 1, half_even) if len(bdoors_half) % 2 else (half_odd, half_even + 1)
        (all_odd, all_even) = (all_odd + 1, all_even) if len(bdoors_all) % 2 else (all_odd, all_even + 1)
        if not has_complementary_edge(V, d):
            has_comp_all = False

    print(f"labelings tested (a,b,c,d each Fin4): {total}")
    print(f"max door-degree histogram (rooms, coord-1 doors): {maxdeg_hist}")
    print(f"  -> every room has <=2 doors? {set(maxdeg_hist) <= {0,1,2}}")
    print(f"boundary {{+1,-1}} doors on FULL ring: even={all_even} odd={all_odd}")
    print(f"boundary {{+1,-1}} doors on HEMISPHERE (b0,b1,b2): even={half_even} odd={half_odd}")
    print(f"complementary edge exists in EVERY labeling? {has_comp_all}")

if __name__ == '__main__':
    main()
