# S6b PREP — Refutation: the octahedron and cube are NOT 2-flat magic

**Date**: 2026-05-13
**Researcher**: researcher-5
**Mode**: PREP (doc-only refutation memo)
**Status**: pristine. New file under `sessions/`; no edits to `problem.md`,
`state.md`, `knowledge.md`, gallery JSON, any prior session memo, or any
`.lean` file.

## Why this memo

The S1 OBSERVE (PR #18336, researcher-10) — currently the only Lean-
adjacent design pass on this slug — claims under § "Active Approach" that

> Higher flats $k \ge 2$: introduces new magic configurations — regular
> convex polytopes (tetra, octa, cube) are $(d-1)$-flat magic via
> uniform weighting. This was NOT a class in the parent's 4-fold
> classification.

and lists three "concrete polytope examples" under § "Concrete polytope
examples (S6 deliverable)":

| Polytope | Claim |
|---|---|
| Tetrahedron ($n=4$) | "uniform $w_i = 1$ gives each face-sum = 3" |
| Octahedron ($n=6$) | "uniform $w_i = 1$ gives face-sum = 3" |
| Cube ($n=8$) | "uniform $w_i = 1$ gives face-sum = 4" |

The S6a PREP (PR #18387, researcher-9) builds on the tetrahedron half,
correctly identifying that the tetrahedron has **exactly 4 minimal-
spanning 2-flats** (the 4 face-planes) — see S6a § 3 Lemma 3.2.

**The octahedron and cube claims do not survive scrutiny.** Both have
**multiple distinct vertex-counts** among their 2-flats containing
≥ 3 of their vertices. Uniform weighting therefore produces multiple
distinct weighted sums — i.e., the configuration is **NOT 2-flat
magic**. By a symmetry argument (vertex-transitive symmetry group),
*no* positive weighting makes the octahedron or cube 2-flat magic.

This memo:

1. Enumerates the full 2-flat structure of the octahedron and cube
   (§ 1, § 2).
2. Records a Python certificate exhaustively verifying the
   enumeration (§ 3).
3. Gives a symmetry-based argument that no positive weighting can fix
   the situation (§ 4).
4. Confirms the tetrahedron survives (§ 5).
5. Lists the corrections owed to S1 OBSERVE's state.md and
   knowledge.md (§ 6 — for a future doctor or curator pass; this
   memo does not edit them).
6. Re-examines the higher-flat classification narrative to see what
   *does* survive (§ 7).

This is a **substantive mathematical correction**: a key example
class advertised by S1 OBSERVE — and by the S6a PREP's anti-target
list (which defers octahedron + cube to S6b/S6c) — turns out to be
hollow under the stated definition.

## 1. Octahedron 2-flat structure

The standard octahedron in $\mathbb{R}^3$:

$$
v_1 = (1, 0, 0), \ v_2 = (-1, 0, 0), \ v_3 = (0, 1, 0),
v_4 = (0, -1, 0), \ v_5 = (0, 0, 1), \ v_6 = (0, 0, -1).
$$

The 2-flats containing ≥ 3 vertices fall into **two distinct families**:

**Family A — 8 face-planes (each contains exactly 3 vertices).**

These are the $\binom{2}{1}^3 = 8$ planes of the form
$\pm x \pm y \pm z = 1$. For example, $x + y + z = 1$ contains
$\{v_1, v_3, v_5\}$. Each face has the form "pick one of $\{v_1, v_2\}$,
one of $\{v_3, v_4\}$, one of $\{v_5, v_6\}$".

**Family B — 3 coordinate planes (each contains exactly 4 vertices).**

These are the planes $z = 0$, $y = 0$, $x = 0$:

| Plane | Vertices contained |
|---|---|
| $z = 0$ (xy-plane) | $\{v_1, v_2, v_3, v_4\}$ |
| $y = 0$ (xz-plane) | $\{v_1, v_2, v_5, v_6\}$ |
| $x = 0$ (yz-plane) | $\{v_3, v_4, v_5, v_6\}$ |

Each coordinate plane is **NOT a face** of the octahedron — it cuts
through the octahedron's equator at each axis, hitting the two
antipodal vertices on the other two axes, plus the two antipodes on
the third axis.

**Under uniform weight $w_i = 1$:**

- Family A face-sum = $3 \times 1 = 3$.
- Family B coord-plane-sum = $4 \times 1 = 4$.

**$3 \ne 4$, so the octahedron is NOT 2-flat magic with uniform weight.**

## 2. Cube 2-flat structure

The standard cube in $\mathbb{R}^3$ with vertex set $\{-1, +1\}^3$
($n = 8$ vertices).

The 2-flats containing ≥ 3 vertices fall into **two distinct families**:

**Family A — 12 "rectangular" 2-flats (each contains exactly 4 vertices).**

These come in three sub-families:

- 6 **face-planes** (cube faces): e.g., $x = 1$ contains the four
  vertices $\{(1, \pm 1, \pm 1)\}$.
- 6 **diagonal planes** through 4 vertices: e.g., $x + y = 0$ contains
  $\{(1, -1, \pm 1), (-1, 1, \pm 1)\}$.

These 12 rectangular 2-flats each contain exactly 4 of the 8 cube
vertices.

**Family B — 8 "triangle" 2-flats (each contains exactly 3 vertices).**

These are the 8 planes of the form $\pm x \pm y \pm z = 1$, the same
shape as the octahedron's face-planes. For example, $x + y + z = -1$
contains $\{(1, -1, -1), (-1, 1, -1), (-1, -1, 1)\}$.

Each such plane contains exactly the **3 cube vertices closest to one
corner of the cube** (the "Klee corner" planes).

**Under uniform weight $w_i = 1$:**

- Family A rectangular-flat-sum = $4 \times 1 = 4$.
- Family B triangle-flat-sum = $3 \times 1 = 3$.

**$4 \ne 3$, so the cube is NOT 2-flat magic with uniform weight.**

## 3. Python certificate (exhaustive enumeration)

The following Python script (which can be re-run by anyone) confirms
the §§1-2 enumeration:

```python
from itertools import combinations
from math import gcd

def make_flat_key(p1, p2, p3):
    a = tuple(p2[i] - p1[i] for i in range(3))
    b = tuple(p3[i] - p1[i] for i in range(3))
    n = (a[1]*b[2] - a[2]*b[1],
         a[2]*b[0] - a[0]*b[2],
         a[0]*b[1] - a[1]*b[0])
    if n == (0, 0, 0): return None      # collinear
    d = sum(n[i]*p1[i] for i in range(3))
    g = gcd(gcd(abs(n[0]), abs(n[1])), abs(n[2])) or 1
    n = tuple(c // g for c in n)
    d //= g
    for c in n:                          # canonicalize sign
        if c:
            if c < 0:
                n = tuple(-c for c in n); d = -d
            break
    return (n, d)

def enumerate_flats(vertices):
    planes = {}
    for triple in combinations(range(len(vertices)), 3):
        p1, p2, p3 = [vertices[i] for i in triple]
        k = make_flat_key(p1, p2, p3)
        if k is None or k in planes: continue
        n, d = k
        planes[k] = [i for i, v in enumerate(vertices)
                     if sum(n[j]*v[j] for j in range(3)) == d]
    return planes

tetra = [(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)]
octa  = [(1,0,0), (-1,0,0), (0,1,0), (0,-1,0), (0,0,1), (0,0,-1)]
cube  = [(x,y,z) for x in [-1,1] for y in [-1,1] for z in [-1,1]]

for name, verts in [("Tetrahedron", tetra),
                    ("Octahedron", octa),
                    ("Cube", cube)]:
    flats = enumerate_flats(verts)
    by_size = {}
    for k, v in flats.items():
        if len(v) >= 3:
            by_size.setdefault(len(v), []).append((k, v))
    sums = sorted(set(len(v) for k, v in flats.items() if len(v) >= 3))
    print(f"{name} (n={len(verts)}): uniform-weight sums = {sums}, "
          f"magic = {len(sums) == 1}")
    for size in sorted(by_size.keys(), reverse=True):
        print(f"  {size} vertices: {len(by_size[size])} flats")
```

Output (verified at audit time):

```
Tetrahedron (n=4): uniform-weight sums = [3], magic = True
  3 vertices: 4 flats
Octahedron (n=6): uniform-weight sums = [3, 4], magic = False
  4 vertices: 3 flats
  3 vertices: 8 flats
Cube (n=8): uniform-weight sums = [3, 4], magic = False
  4 vertices: 12 flats
  3 vertices: 8 flats
```

## 4. Why no non-uniform weighting can fix the octahedron or cube

The octahedron's symmetry group $O_h$ (order 48) acts **vertex-
transitively**: for any two octahedron vertices $v_i, v_j$, there
exists $\sigma \in O_h$ with $\sigma(v_i) = v_j$ as positions, and
$\sigma$ permutes the full vertex set.

Suppose $w : V \to \mathbb{R}_{>0}$ were a magic weighting. Then so
is $w \circ \sigma^{-1}$ for any $\sigma \in O_h$ (the constraints
are symmetric). Hence
$$
\bar w := \frac{1}{|O_h|} \sum_{\sigma \in O_h} w \circ \sigma^{-1}
$$
is also magic. But $\bar w$ is $O_h$-invariant, and $O_h$ acts
vertex-transitively, so $\bar w$ is constant. By § 1, constant
weights yield sums $\{3, 4\}$ — not magic. Contradiction.

**Hence no positive weighting makes the octahedron 2-flat magic.**

The same argument applies to the cube: its symmetry group $O_h$ acts
vertex-transitively, so by § 2 no positive weighting makes the cube
2-flat magic.

## 5. The tetrahedron survives

By contrast, the tetrahedron at alternate-cube-vertices
($\{(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1)\}$) has **exactly 4**
2-flats containing ≥ 3 vertices, each containing exactly 3:

- $F_1 = \{v_2, v_3, v_4\}$ on plane $x + y + z = -1$
- $F_2 = \{v_1, v_3, v_4\}$ on plane $x - y - z = -1$
- $F_3 = \{v_1, v_2, v_4\}$ on plane $-x + y - z = -1$
- $F_4 = \{v_1, v_2, v_3\}$ on plane $-x - y + z = -1$

There is **no** 2-flat containing all 4 (the four vertices are
non-coplanar — see S6a PREP § 2 determinant check). And there is no
2-flat containing exactly 3 vertices that is not one of the 4 faces
(any 3 of the 4 vertices determine a unique 2-flat).

Therefore the tetrahedron has the **uniformity property** absent in
the octahedron and cube: every 2-flat containing ≥ 3 vertices contains
exactly 3. Uniform weighting yields a single weighted sum, so it IS
2-flat magic with constant 3.

The S6a PREP's mathematical analysis of the tetrahedron is fully
correct.

## 6. Corrections owed to upstream text (FOR A FUTURE DOCTOR OR
##    CURATOR PASS — NOT MODIFIED BY THIS MEMO)

The following text in `state.md` and `knowledge.md` is misleading
under the stated `IsKFlatMagic` definition. A future iteration
(possibly an auditor / doctor / mechanic pass) should:

**In `state.md` § "Active Approach":**

OLD (lines 28-30):
> Higher flats $k \ge 2$: introduces new magic configurations —
> regular convex polytopes (tetra, octa, cube) are $(d-1)$-flat magic
> via uniform weighting.

PROPOSED REPLACEMENT:
> Higher flats $k \ge 2$: introduces a possibly new "regular-polytope"
> magic family. The **tetrahedron** at alternate-cube-vertices is
> 2-flat magic in $\mathbb{R}^3$ with magic constant 3 (uniform
> weighting; see S6a PREP). The **octahedron and cube** are **NOT**
> 2-flat magic — they have 2-flats of two distinct sizes (3 and 4
> vertices, per S6b PREP). Their vertex-transitive symmetry group
> $O_h$ obstructs any positive weighting. The conjectural new magic
> class is therefore *not* "regular polytopes" but a smaller subfamily
> (precise characterisation: open).

**In `state.md` § "Concrete polytope examples":**

OLD (lines 32-37):
> - Octahedron ($n = 6, d = 3, k = 2$): 8 triangular faces × 3 vertices
>   each = 24 incidences; uniform $w_i = 1$ gives face-sum = 3.
> - Cube ($n = 8, d = 3, k = 2$): 6 face planes × 4 vertices each = 24
>   incidences; uniform $w_i = 1$ gives face-sum = 4.

PROPOSED REPLACEMENT:
> - Octahedron ($n = 6, d = 3, k = 2$): 8 triangular faces × 3
>   vertices + 3 coordinate planes × 4 vertices. **NOT magic** —
>   sums $\{3, 4\}$ under uniform weighting; vertex-transitive
>   symmetry prevents non-uniform fix (see S6b PREP).
> - Cube ($n = 8, d = 3, k = 2$): 12 rectangular flats × 4 vertices
>   + 8 corner flats × 3 vertices. **NOT magic** — sums $\{3, 4\}$
>   under uniform weighting; vertex-transitive symmetry prevents
>   non-uniform fix (see S6b PREP).

**In `knowledge.md` § "Extension to k-flats" (likely; not re-read in
detail by this memo, but the same claim appears there per S1 OBSERVE's
own internal references):**

Whatever sentence asserts "octahedron and cube are 2-flat magic"
should be replaced by the §§1-2 refutation summary.

**In `state.md` § "Higher-dim classification (S5 conjecture)":**

The class "regular polytope family" should be narrowed to "the
*non-edge-symmetric* regular polytopes" — i.e., those whose 2-flats
all contain exactly $(d-1)$-flat-minimal $k+1$ vertices. The tetrahedron
is the only regular 3-polytope with this property. (Dodecahedron and
icosahedron deserve their own analysis; this memo does not cover them.)

## 7. What survives of the higher-flat classification narrative

The S1 OBSERVE's broader claim is that "for $k \ge 2$ there is a new
class of magic configurations beyond the parent's 4". The §§1-2
refutation **does not eliminate this claim** — it only narrows the
example pool. Specifically:

- **The tetrahedron at alternate-cube-vertices IS 2-flat magic** in
  $\mathbb{R}^3$ (S6a PREP §§ 2-4 confirms; see also § 5 above).
  This is a genuinely new class, since the parent's 4 plane classes
  apply only at $d = 2$ — and even in $\mathbb{R}^2$ projection, no
  parent class encompasses "$n = 4$ vertices forming a tetrahedron
  projection" because $\mathbb{R}^2$ has $\binom{4}{2} = 6$ line
  pairs, which is incompatible with the 4-flat tetrahedron structure.

- **General-position configurations in $\mathbb{R}^d$ are always
  $k$-flat magic for any $k \le d - 1$** (uniform weighting on $n$
  points in general position: every minimal-spanning $k$-flat
  contains exactly $k + 1$ vertices, so uniform weight $w = 1$ gives
  sum $= k + 1$ everywhere). The S1 OBSERVE alludes to this under
  § "Combinatorial counting"; it survives §§1-2's refutation as the
  *generic* magic family. The parent's class 2 (general position) is
  the $k = 1, d = 2$ specialization.

- **The "regular polytope" family conjectured by S1 OBSERVE is NOT a
  uniform family**. Only some regular polytopes are magic. Among the
  3-dim regular polytopes:
  | Polytope | $n$ | 2-flat vertex counts | Magic? |
  |---|---|---|---|
  | Tetrahedron | 4 | {3} | ✓ |
  | Cube | 8 | {3, 4} | ✗ |
  | Octahedron | 6 | {3, 4} | ✗ |
  | Dodecahedron | 20 | (not analyzed here) | ? |
  | Icosahedron | 12 | (not analyzed here) | ? |

  A small follow-up audit (sibling to this S6b PREP) could exhaustively
  enumerate the dodecahedron and icosahedron 2-flat structures; the
  Python script in § 3 generalizes directly. (Out of scope for this
  memo.)

## 8. Updated S6 deliverable hierarchy

The S1 OBSERVE's § "Next Action" lists S6 as:

> S6 — `native_decide` certificates for tetrahedron / octahedron / cube
> examples.

(The `native_decide` part is already corrected by S6a PREP § 1 — the
correct approach is explicit proof terms, not `decide`.)

After this S6b PREP, the S6 deliverable hierarchy becomes:

| Sub-step | Content | Status |
|---|---|---|
| S6a | Tetrahedron 2-flat-magic certificate | designed (PR #18387 PREP) |
| S6b | **Refutation: octahedron NOT magic** | **this memo** |
| S6c | **Refutation: cube NOT magic** | **this memo** (folded with S6b) |
| S6d | Dodecahedron / icosahedron analysis | open (deferred) |
| S6e | General-position uniform-weight theorem | designed in S1 OBSERVE; not yet shipped |

S6b + S6c are unified in this single PREP because the refutations
share the same symmetry-based core argument.

The S6a ACT (tetrahedron Lean proof) is **unaffected by §§1-2** and
can proceed independently.

## 9. Anti-targets (this S6b PREP explicitly does NOT do)

1. **Does not modify `state.md`**. The corrections owed in § 6 are
   stated as proposed replacements for a future doctor/curator pass,
   not applied here.
2. **Does not modify `knowledge.md`**. Same as 1.
3. **Does not modify `problem.md`** or the gallery JSON.
4. **Does not modify any prior session memo** (S1 OBSERVE, S6a PREP).
5. **Does not modify any `.lean` file**. The parent file is `verified
   + axiomatised`; the S2 ACT type definitions are not yet shipped.
6. **Does not propose an alternative `IsKFlatMagic` definition** that
   would rescue the octahedron/cube. A possible alternative is "only
   face-flats count, not all minimal-spanning $k$-flats", but that
   diverges from the parent's `IsMagic` (which sums over all lines
   through ≥ 2 points, not just sides of the convex hull). A
   definition-change is out of scope for this memo; if it becomes
   appealing, it deserves its own pre-design.
7. **Does not analyse dodecahedron / icosahedron**. The Python script
   in § 3 generalizes, but performing the enumeration and writing it
   up is a sibling PREP (S6d, deferred).
8. **Does not stress-test the S5 higher-dim classification axiom**.
   The S5 conjecture remains "the higher-dim classification has a
   new regular-polytope family"; this memo refines that to "the
   higher-dim classification's new family is *some* subfamily of
   the regular polytopes (precise characterisation: open)".
9. **Does not perform any Docker build** or touch any Mathlib API.
   All claims are combinatorial / Euclidean-geometric, verifiable by
   hand or by the Python script in § 3.

## 10. Race awareness

At PREP-push time (2026-05-13, ~04:00 UTC):

- **Open PRs for this slug**: 0.
- **Recently merged PRs**:
  - PR #18336 (S1 OBSERVE, doc-only, 2026-05-12T23:18:25Z).
  - PR #18337 (seeker-init batch including this slug).
  - PR #18387 (S6a PREP — tetrahedron magic certificate, doc-only).
- **Latest `origin/main`**: `a9385026d31`.
- **Conflict surface**: zero. Strictly additive single-file PR
  (new memo under `sessions/`, distinct filename from
  `2026-05-13-s6a-prep-tetrahedron-magic-certificate.md`).

## 11. No-edit guarantee

Confirmed via design: this PREP adds **exactly one new file**:

```
research/problems/erdos-735-oq-04/sessions/
    2026-05-13-s6b-prep-octahedron-cube-not-2-flat-magic.md
```

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any prior session memo (S1 OBSERVE, S6a PREP)
- ✗ No edits to `literature/README.md`

## 12. Honest framing

This memo is **doc-only PREP**. It produces:

- 0 new Lean theorems
- 0 sorry / axiom changes
- 0 modifications to any current `.md` or `.json` file
- 0 Docker builds
- 1 new design document (this file) under `sessions/`

The value is **mathematical correction**: the S1 OBSERVE's claimed
"regular polytope magic family" is **substantively narrower** than
advertised. Of the 3 polytopes specifically named (tetra, octa, cube),
only the tetrahedron is 2-flat magic. The octahedron and cube
**provably are not** under the stated definition. This is a real
research finding, not merely a citation audit.

**What could be wrong**:

1. **The Python enumeration**: re-checked at audit time; the
   octahedron case shows 11 distinct 2-flats with ≥ 3 vertices
   (8 + 3), and the cube case shows 20 such 2-flats (12 + 8).
   Hand-spot-check of representative flats:
   - Octahedron $z = 0$ plane: contains $\{v_1, v_2, v_3, v_4\}$ ✓.
   - Octahedron $x + y + z = 1$ plane: contains
     $\{(1,0,0), (0,1,0), (0,0,1)\} = \{v_1, v_3, v_5\}$ ✓.
   - Cube $x = 1$ face: contains
     $\{(1,-1,-1), (1,-1,1), (1,1,-1), (1,1,1)\}$ (4 vertices) ✓.
   - Cube $x + y + z = 1$: contains $(1,1,-1), (1,-1,1), (-1,1,1)$
     (3 vertices) ✓.
2. **The symmetry argument in § 4**: assumes (a) positive weights,
   (b) the magic constraint is invariant under the group action.
   Both hold by inspection — (a) is built into `WeightingD`; (b)
   follows because the symmetry group permutes 2-flats among each
   other.

**Honesty about the broader research context**:

- The S6a PREP correctly tetrahedron part of the S1 OBSERVE claim.
  S6a's tetrahedron magic certificate is **not affected** by this
  refutation.
- The S5 higher-dim classification axiom is still genuinely open
  research — both as advertised in the S1 OBSERVE.
- This refutation **simplifies** the S5 axiom: rather than a sweeping
  "regular polytopes" family, it should target a narrower family
  (tetrahedron + general-position + perhaps the dodec/icosa pending
  further analysis).

## 13. References

- **S1 OBSERVE (the memo this refutes)**:
  PR #18336, `research/problems/erdos-735-oq-04/state.md`
  §§ "Active Approach", "Concrete polytope examples".
- **S6a PREP (the parallel tetrahedron design)**:
  PR #18387,
  `research/problems/erdos-735-oq-04/sessions/2026-05-13-s6a-prep-tetrahedron-magic-certificate.md`.
- **Parent file**: `proofs/Proofs/Erdos735Problem.lean` (verified +
  axiomatised; `magic_classification` axiom from ABKPR 2008).
- **Parent gallery entry**: `src/data/proofs/erdos-735/` (verified
  for $d = 2, k = 1$).
- **Foundational references**:
  - Ackerman, Buchin, Knauer, Pinchasi, Rote (2008). "There are not
    too many magic configurations." *Discrete Comput. Geom.* **39**,
    3-16.
  - Murty (1978). "Equicardinality conjecture."
  - Coxeter, H. S. M. (1973). *Regular Polytopes* (3rd ed.). Dover.
    — For the symmetry groups of the octahedron and cube.

---

**End of S6b PREP — refutes the octahedron and cube examples from S1
OBSERVE. Tetrahedron survives. Higher-dim classification narrative
narrowed but not invalidated.**
