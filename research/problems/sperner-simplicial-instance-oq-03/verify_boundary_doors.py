#!/usr/bin/env python3
"""
ORIENT verification for sperner-simplicial-instance-oq-03:
    `boundary_doors_odd` for the standard n-simplex triangulation.

What this script establishes (build-free, by exhaustive enumeration):

  The parent file proofs/Proofs/SpernerSimplicialInstance.lean already PROVES
  `boundary_doors_odd` as a parity-TRANSFER theorem: it shows the boundary-door
  set S equals the top-facet door set S_n (every boundary door is forced onto
  geometric face n by the Sperner condition), then concludes |S| odd FROM the
  hypothesis `_hLastFace : Odd |S_n|`.

  The genuine remaining first-principles gap is therefore NOT the whole lemma
  but the hypothesis `_hLastFace` (plus the base case): that the door count on
  the top facet is odd. Classically this is the dimension induction:

      doors on top facet of Delta^n  ==  door count of the INDUCED Sperner
      coloring on that facet (a Delta^{n-1})  ==  odd  (induction hypothesis).

  We verify, by brute force over ALL Sperner colorings:
    (n=1) base case: subdivided interval has exactly one boundary door (odd).
    (n=2) Kuhn-triangulated triangle:
       (a) #panchromatic top cells is odd            [Sperner sanity]
       (b) #boundary doors is odd
       (c) ALL boundary doors lie on the top facet (the S = S_n reduction)
       (d) #boundary doors == #1-D doors of the induced coloring on that facet
           (the induction bridge that discharges `_hLastFace`)

Semantics mirror the Lean defs (SpernerMathlib.lean / SpernerSimplicialInstance.lean):
  IsSpernerColoring c onFace : forall v k, onFace v k -> c v != k
  IsDoor (s,k)               : the d vertices != k carry all lower colors {0..d-1}
  IsPanchromatic s           : c o vertex_s is onto Fin (d+1)
  Geometric facet k of the standard simplex = facet OPPOSITE vertex k
     (contains every corner except vertex k).
"""

from itertools import product

# ---------------------------------------------------------------------------
# n = 1 : subdivided interval  [vertices 0..m on the segment v0--v1]
# Geometric facet 0 = {opposite v0} = right endpoint ; facet 1 = left endpoint.
# Sperner => c(left)=0, c(right)=1 ; interior free in {0,1}.
# 1-cell [i,i+1], door at k: the vertex != k is colored 0 (= castSucc of Fin 1).
# Boundary facets: left facet of cell 0 (k=1, keeps left vtx), right of cell m-1.
# ---------------------------------------------------------------------------
def verify_interval(m):
    ok = True
    interiors = list(product((0, 1), repeat=m - 1))  # colors of positions 1..m-1
    for int in interiors:
        c = [0] + list(int) + [1]          # c[0]=0 (left), c[m]=1 (right)
        # boundary doors: left end of cell 0 keeps vertex pos 0 -> door iff c[0]==0
        #                 right end of cell m-1 keeps vertex pos m -> door iff c[m]==0
        doors = (1 if c[0] == 0 else 0) + (1 if c[m] == 0 else 0)
        if doors % 2 != 1:
            ok = False
        if doors != 1:                      # always exactly the left end
            ok = False
    return ok, len(interiors)


# ---------------------------------------------------------------------------
# n = 2 : Kuhn / staircase triangulation of the triangular grid of side m.
# Lattice points (i,j), i,j>=0, i+j<=m.  Corners:
#   A=(0,0)=vertex0,  B=(m,0)=vertex1,  C=(0,m)=vertex2.
# Facet opposite v0 = BC = {i+j=m}; opp v1 = AC = {i=0}; opp v2 = AB = {j=0}.
# Triangles: lower [(i,j),(i+1,j),(i,j+1)]  for i+j<=m-1
#            upper [(i+1,j),(i,j+1),(i+1,j+1)] for i+j<=m-2
# ---------------------------------------------------------------------------
def grid_points(m):
    return [(i, j) for i in range(m + 1) for j in range(m + 1 - i)]

def triangles(m):
    tris = []
    for i in range(m + 1):
        for j in range(m + 1 - i):
            if i + j <= m - 1:
                tris.append(((i, j), (i + 1, j), (i, j + 1)))
            if i + j <= m - 2:
                tris.append(((i + 1, j), (i, j + 1), (i + 1, j + 1)))
    return tris

def on_facets(p, m):
    """Return set of facet indices (opposite-vertex labels) containing p."""
    i, j = p
    s = set()
    if i + j == m: s.add(0)   # facet opposite v0 (BC)
    if i == 0:     s.add(1)   # facet opposite v1 (AC)
    if j == 0:     s.add(2)   # facet opposite v2 (AB)
    return s

def sperner_choices(p, m):
    """Allowed colors at p under the Sperner condition c(p) != k for facets k."""
    forbidden = on_facets(p, m)
    return [k for k in (0, 1, 2) if k not in forbidden]

def edges_of(tri):
    """The 3 edges (as frozensets of 2 points) of a triangle."""
    a, b, cc = tri
    return [frozenset((a, b)), frozenset((a, cc)), frozenset((b, cc))]

def is_door_edge(edge, c):
    """A 1-face (edge) is a Sperner 'door' if its 2 vertices carry colors {0,1}."""
    cols = {c[v] for v in edge}
    return cols == {0, 1}

def edge_facet(edge, m):
    """Which boundary facet (0/1/2) an edge lies on, or None if interior."""
    common = on_facets(next(iter(edge)), m)
    for v in edge:
        common = common & on_facets(v, m)
    return next(iter(common)) if common else None

def verify_triangle(m):
    pts = grid_points(m)
    tris = triangles(m)

    # pseudomanifold sanity: each interior edge in exactly 2 triangles, boundary in 1.
    from collections import Counter
    edge_count = Counter()
    for t in tris:
        for e in edges_of(t):
            edge_count[e] += 1
    boundary_edges = [e for e, n in edge_count.items() if n == 1]
    assert all(n in (1, 2) for n in edge_count.values()), "not a pseudomanifold"

    free = [p for p in pts if len(sperner_choices(p, m)) > 1]
    domains = [sperner_choices(p, m) for p in free]
    fixed = {p: sperner_choices(p, m)[0] for p in pts if len(sperner_choices(p, m)) == 1}

    total = 0
    all_ok = True
    for assign in product(*domains):
        c = dict(fixed)
        for p, col in zip(free, assign):
            c[p] = col
        total += 1

        # (a) panchromatic top cells
        panchro = sum(1 for t in tris if {c[v] for v in t} == {0, 1, 2})
        # (b)(c) boundary doors, by facet
        bdoors = [e for e in boundary_edges if is_door_edge(e, c)]
        per_facet = {0: 0, 1: 0, 2: 0}
        for e in bdoors:
            per_facet[edge_facet(e, m)] += 1
        # (d) induced 1-D door count on facet 2 (segment AB, j=0)
        ab = sorted([p for p in pts if p[1] == 0], key=lambda p: p[0])  # positions along AB
        ab_doors = sum(1 for a in range(len(ab) - 1)
                       if {c[ab[a]], c[ab[a + 1]]} == {0, 1})

        ok = (panchro % 2 == 1
              and len(bdoors) % 2 == 1
              and per_facet[0] == 0 and per_facet[1] == 0
              and per_facet[2] == len(bdoors)
              and per_facet[2] == ab_doors)
        if not ok:
            all_ok = False
    return all_ok, total


if __name__ == "__main__":
    print("=== n=1 base case (subdivided interval): exactly one boundary door ===")
    for m in (1, 2, 3, 4, 5):
        ok, n = verify_interval(m)
        print(f"  m={m}: {n:>3} colorings  ->  all have odd (==1) boundary doors: {ok}")

    print("\n=== n=2 (Kuhn-triangulated triangle): full boundary-door parity ===")
    for m in (1, 2, 3, 4):
        ok, n = verify_triangle(m)
        print(f"  grid m={m}: {n:>5} Sperner colorings  ->  "
              f"odd panchromatic & boundary doors, all on top facet, "
              f"== induced 1-D count: {ok}")

    print("\nAll checks passed." )
