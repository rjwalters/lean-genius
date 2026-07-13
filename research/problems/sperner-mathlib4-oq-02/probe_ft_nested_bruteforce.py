#!/usr/bin/env python3
"""
Brute-force ALL oriented edge-local door predicates on the hexagon+centre
triangulation of B^2, testing whether ANY of them supplies the exact hypothesis
the abstract path-following engine needs to close n = 2 Tucker.

Research probe for sperner-mathlib4-oq-02 ("Tucker's lemma / Borsuk-Ulam from
abstract door-counting").  Follow-up to probe_ft_pathfollowing.py and
probe_ft_oriented.py, and to the impossibility file
SpernerTuckerHexagonSignFlipCycles.lean.

## The exact requirement (from SpernerTuckerPathFollowing.exists_interior_degree_one)
The engine returns an interior degree-1 room (the Tucker witness) as soon as it is
given a door graph on the triangulation with
  (A) full-boundary-circle door count ODD  (invariantly over all antipodal labellings), and
  (B) every triangle door-degree <= 2      (so the room graph is paths+cycles).
Handshake then forces #(interior degree-1 rooms) = #(boundary doors) = odd (mod 2),
hence >= 1 interior witness.

## Why the two known single-coordinate rules both fail (re-derived here, then generalised)
Both the sign-flip rule and the exact {+1,-1} complementary rule are NEGATION-SYMMETRIC
(D(x,y) = D(-x,-y)).  On the antipodal 6-cycle v_{i+3} = -v_i the boundary edges then
split into 3 antipodal pairs -> the full-circle count is always EVEN -> (A) fails.
So (A) FORCES a negation-asymmetric (oriented) rule.  This probe asks the sharp question:
does ANY oriented edge-local predicate D : Fin4 x Fin4 -> Bool satisfy both (A) and (B)?

## Encoding (identical to the Lean files)
Fin4  0->+1, 1->+2, 2->-1, 3->-2 ;  negL = [2,3,0,1] ;  antipodal v_{i+3} = negL[v_i].
Boundary oriented edges of the hexagon disc: v_i -> v_{i+1}, i=0..5 (v6=v0).
Triangle T_i = (centre d, v_i, v_{i+1}); its 3 oriented sides: d->v_i, v_i->v_{i+1}, v_{i+1}->d.
A door predicate D is an arbitrary subset of the 16 ordered pairs (x,y) in Fin4 x Fin4,
encoded as a 16-bit mask.  Interior doors "see" the centre label because (d, v_i) is an edge.
"""
from itertools import product

negL = [2, 3, 0, 1]

# free boundary labellings: v0,v1,v2 in Fin4, then v3,v4,v5 = negL of them (antipodal).
BOUNDARY = []
for a, b, c in product(range(4), repeat=3):
    V = [a, b, c, negL[a], negL[b], negL[c]]
    BOUNDARY.append(V)                     # 64 antipodal boundary labellings

# ordered pair index helper: pair (x,y) -> bit position x*4+y
def bit(x, y):
    return x * 4 + y

# Precompute, for each boundary labelling, the list of oriented boundary edges (x,y).
BOUND_EDGES = [[(V[i], V[(i + 1) % 6]) for i in range(6)] for V in BOUNDARY]

# Precompute, for each (boundary labelling, centre d), the 6 triangles' oriented sides.
# We only need (B) [max triangle degree <= 2]; centre d ranges over Fin4.
TRIS = []   # list of (list-of-triangles); each triangle = 3 oriented pairs
for V in BOUNDARY:
    for d in range(4):
        tris = []
        for i in range(6):
            vi, vj = V[i], V[(i + 1) % 6]
            tris.append([(d, vi), (vi, vj), (vj, d)])
        TRIS.append(tris)

def full_circle_odd_invariant(mask):
    """(A): full 6-edge boundary door count is ODD for EVERY antipodal labelling."""
    for edges in BOUND_EDGES:
        cnt = sum(1 for (x, y) in edges if (mask >> bit(x, y)) & 1)
        if cnt % 2 == 0:
            return False
    return True

def max_tri_degree_le2(mask):
    """(B): every triangle has door-degree <= 2 for EVERY labelling+centre."""
    for tris in TRIS:
        for tri in tris:
            deg = sum(1 for (x, y) in tri if (mask >> bit(x, y)) & 1)
            if deg > 2:
                return False
    return True

def has_interior_deg1_witness_invariant(mask):
    """Bonus: for EVERY labelling+centre, is there >=1 triangle of door-degree exactly 1
       whose degree-1 side is an INTERIOR edge (d,v)?  (the actual witness room)."""
    for tris in TRIS:
        found = False
        for tri in tris:
            doors = [k for k, (x, y) in enumerate(tri) if (mask >> bit(x, y)) & 1]
            # sides: 0 = (d,vi) interior, 1 = (vi,vj) boundary, 2 = (vj,d) interior
            if len(doors) == 1 and doors[0] in (0, 2):
                found = True
                break
        if not found:
            return False
    return True

def is_undirected(mask):
    """D(x,y) == D(y,x) for all x,y: doors are unordered facets (what the
       undirected path-following engine `exists_interior_degree_one` requires,
       since an interior edge (d,v) is one shared facet of its two triangles)."""
    for x in range(4):
        for y in range(4):
            if ((mask >> bit(x, y)) & 1) != ((mask >> bit(y, x)) & 1):
                return False
    return True

def main():
    print(f"antipodal boundary labellings: {len(BOUNDARY)}   full labellings (x centre): {len(TRIS)}")
    print("Enumerating all 2^16 = 65536 oriented edge-local door predicates D...")
    passA = []
    for mask in range(1 << 16):
        if full_circle_odd_invariant(mask):
            passA.append(mask)
    print(f"\n(A) invariant-ODD full-circle boundary seed: {len(passA)} predicates pass")

    passAB = [m for m in passA if max_tri_degree_le2(m)]
    print(f"(A)&(B) invariant-odd seed AND every-triangle-degree<=2: {len(passAB)} predicates")

    # The faithful test: the engine's doors are UNDIRECTED shared facets.
    passABsym = [m for m in passAB if is_undirected(m)]
    print(f"(A)&(B)&UNDIRECTED (usable by the shared-facet path engine): {len(passABsym)} predicates")
    if not passABsym:
        print("  ==> IMPOSSIBILITY: NO *undirected* edge-local door rule (nested or not,")
        print("      centre-aware) closes n=2 Tucker.  Every (A)&(B) winner is a DIRECTED")
        print("      sign rule whose door is not symmetric across a shared interior facet,")
        print("      so it cannot instantiate the undirected shared-door path engine.")
        print("      Strengthens the single-coordinate impossibility to the whole undirected")
        print("      edge-local class: the bridge needs oriented 2-cell (pivot) data.")
    else:
        for m in passABsym[:10]:
            pairs = [(x, y) for x in range(4) for y in range(4) if (m >> bit(x, y)) & 1]
            sg = ['+1', '+2', '-1', '-2']
            print(f"  UNDIRECTED closing mask=0x{m:04x}: {[f'{sg[x]}-{sg[y]}' for (x,y) in pairs if x<=y]}")

    if not passAB:
        print("\n==> RESULT: NO oriented edge-local door predicate closes n=2 Tucker.")
        print("    The Freund-Todd/Prescott-Su bridge CANNOT be any function of edge")
        print("    endpoint labels alone (even oriented / centre-aware): it must use")
        print("    genuinely 2-cell (orientation-of-the-triangle) data.  New impossibility.")
    else:
        full = [m for m in passAB if has_interior_deg1_witness_invariant(m)]
        print(f"(A)&(B)&(interior deg-1 witness always present): {len(full)} predicates")
        show = full if full else passAB
        print(f"\n==> RESULT: FOUND {len(show)} closing predicate(s). Examples (16-bit masks):")
        for m in show[:10]:
            pairs = [(x, y) for x in range(4) for y in range(4) if (m >> bit(x, y)) & 1]
            sg = ['+1', '+2', '-1', '-2']
            human = [f"{sg[x]}->{sg[y]}" for (x, y) in pairs]
            print(f"  mask=0x{m:04x}: doors = {human}")

    # Diagnostic: confirm the two known single-coordinate rules fail (A) as predicted.
    def mk(pred):
        m = 0
        for x in range(4):
            for y in range(4):
                if pred(x, y):
                    m |= 1 << bit(x, y)
        return m
    def sgnbit(x):
        return 0 if x < 2 else 1
    signed = [1, 2, -1, -2]
    signflip = mk(lambda x, y: sgnbit(x) != sgnbit(y))
    pm1 = mk(lambda x, y: {signed[x], signed[y]} == {1, -1})
    print("\nDiagnostic (known rules):")
    print(f"  sign-flip  full-circle-odd-invariant? {full_circle_odd_invariant(signflip)} (expect False: negation-symmetric)")
    print(f"  {{+1,-1}}    full-circle-odd-invariant? {full_circle_odd_invariant(pm1)} (expect False: negation-symmetric)")

if __name__ == '__main__':
    main()
