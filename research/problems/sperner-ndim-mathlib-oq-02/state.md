# Current State

**Phase**: ACT
**Since**: 2026-05-06T18:16:19+03:00
**Iteration**: 4

## Current Focus

1 axiom remaining: `sperner_near_fixed_point` — connecting grid triangulation to abstract Sperner.
All other components are fully proved (0 sorries). PR #16235 is open.

## Active Approach

Sperner coloring: c(v) = min{i ∈ supp(v) : f(v)_i ≤ v_i}
- Well-definedness: algebraic (Finset.sum_lt_sum), PROVED
- Boundary condition: c(v) ∈ supp(v), PROVED
- Compactness → exact fixed point (fixed_point_from_approx): PROVED
- Main theorem: from 1 axiom, PROVED

## Blocker: Full-Permutation Freudenthal Triangulation

Must build `FreudSimplex d N` as a `SpernerTriangulation d N` and prove `boundary_doors_odd`.
Estimated: ~400 lines total across 3-4 sessions.

### Correct FreudSimplex Design (Session 4 analysis)

```
FreudSimplex d N = { base : Fin(d+1) → ℕ, σ : Equiv.Perm (Fin(d+1)) }
where: Σ_i base_i = N, base[σ(Fin.last d)] ≥ d
```

Vertex k (0 ≤ k ≤ d):
- u_k[σ(j)] = base[σ(j)] + (if j.val < k then 1 else 0) for j : Fin d
- u_k[σ(Fin.last d)] = base[σ(Fin.last d)] - k

As Vertex d N: vertex_k.coords[j'] = u_k[Fin.castSucc j'] for j' : Fin d

This preserves Σ u_k = N at every step (each step adds e_{σ(j)} - e_{σ(d)} with net = 0).

### Correct Adjacency

For face position p (removing vertex p) from S = (base, σ):

**Middle faces (0 < p < d)**: swap σ(p-1) and σ(p):
- S' = (base, σ') where σ'(p-1) = σ(p), σ'(p) = σ(p-1), σ'(j) = σ(j) otherwise
- S'.vertex (p-1) = S.vertex (p+1) - step, S'.vertex (p+1) = S.vertex (p-1) + step
- The face (remove p from S) = face (remove p from S'), same shared vertices ✓

**Face 0 (remove base vertex)**:
- S' has base' = u_1 = base + e_{σ(0)} - e_{σ(d)}
- σ' = rotation: σ'(0)=σ(1),...,σ'(d-2)=σ(d-1), σ'(d-1)=σ(d), σ'(d)=σ(0)
- Condition: base[σ(d)] > d (need base'[σ'(d)] = base'[σ(0)] = base[σ(0)] ≥ 0... actually
  need base[σ(d)] ≥ d+1 for S to have a left neighbor)

**Face d (remove top vertex)**:
- adj S (Fin.last d) = none iff base[σ(d)] = d (cannot step further)
- Otherwise: S' has base' = u_d + e_{σ(d-1)} - e_{σ(d)} (base' = vertex d + one step back)
  Hmm, this needs more analysis

### boundary_face Axiom for FreudSimplex

If adj S (Fin.last d) = none (i.e., base[σ(d)] = d), then:
- All non-d vertices {v_0,...,v_{d-1}} satisfy: their σ(d)-th coordinate = 0
  Actually: for j < d, u_j[σ(d)] = base[σ(d)] - j = d - j > 0 (not 0 for j < d)
  
Wait, this shows the σ(d)-th bary coord DECREASES but is > 0 for j < d!

So the "face" for this simplex is: v_d has u_d[σ(d)] = base[σ(d)] - d = 0, meaning
v_d is ON face "σ(d)" (the face where the σ(d)-th coordinate is 0).

boundary_face requires: ∀ j ≠ Fin.last d, onFace (K.vertices S j) (Fin.last d)

In SpernerNDim, Fin.last d = face d, meaning Σcoords = N (implicit last coord = 0).

So we need: for j < d, the vertex u_j has Σ u_j.coords = N (implicit last = 0)... but 
u_j has Σcoords = N - u_j[Fin.last d] = N - u_j.fullbary[Fin.last d].

For this to equal N, we need u_j.fullbary[Fin.last d] = 0.

u_j.fullbary[Fin.last d]:
- if Fin.last d = σ(j') for j' < d: = base[Fin.last d] + (if j' < j then 1 else 0)
- if Fin.last d = σ(d) (the miss direction): = base[σ(d)] - j = d - j (not 0 for j < d!)

So boundary_face fails! The non-d vertices do NOT have Σcoords = N in general.

**ROOT CAUSE**: In SpernerNDim, face d means "Σcoords = N (in Vertex d N terms)", which
means the IMPLICIT last barycentric coordinate is 0. But in our FreudSimplex with
miss = σ(d), the implicit last bary coord is u_k[Fin.last d], not u_k[σ(d)].

SOLUTION: Must align σ so that σ(d) = Fin.last d always! That is, the miss direction
is ALWAYS the implicit (d-th) barycentric direction.

This brings us back to the constant-miss approach, but now we understand: the constant
miss MUST be the implicit direction (Fin.last d), not an arbitrary direction.

For constant miss = Fin.last d (the implicit coord):
- FreudSimplex d N = (base : Fin d → ℕ, σ : Equiv.Perm (Fin d)) where Σbase + d ≤ N
  (since vertex d increases each explicit coord by 1 and decreases implicit by d)
- Vertex k: coords[j] = base[j] + countPerm(σ, k, j) for j : Fin d
- Implicit last: N - Σbase - k

BUT: adj across face 0 fails boundary_face for this version (same as SpernerGrid.lean!)

The issue: boundary_face for face k of SpernerNDim means:
"adj S k = none → ∀ j ≠ k, onFace (K.vertices S j) k"

For k = 0: adj S 0 = none should mean vertex 0 = base is on the geometric boundary face 0,
meaning base.coords[0] = 0. Then ∀ j ≠ 0: onFace (v_j) 0 means v_j.coords[0] = 0.
But v_j.coords[0] = base[0] + countPerm(σ, j, 0). If base[0] = 0 and σ(0) = 0:
  v_j.coords[0] = 0 + (j > 0 ? 1 : 0) = (j > 0 ? 1 : 0). For j ≥ 1: v_j.coords[0] = 1 ≠ 0!

So boundary_face is INDEED broken for constant-miss FSimplex.

**RESOLUTION**: The vertex labeling must be INVERTED for face k. Specifically:
- For face k = 0 to have boundary_face hold, vertex 0 should NOT be base but rather
  the vertex with MAXIMUM k-th coordinate. Then removing vertex 0 (the max) leaves
  vertices with ZERO in coordinate k.

CORRECT vertex labeling:
- Vertex 0 = the "top" vertex (has all non-miss coords maximal): coords[j] = base[j] + 1 for all j
- Vertex k (for 0 ≤ k ≤ d): coords[j] = base[j] + (1 if j in {σ(k),...,σ(d-1)} else 0)

I.e., vertex 0 has all steps taken, vertex 1 has all steps except σ(0), ..., vertex d has no steps = base.

With this labeling:
- vertex d = base (the "bottom" vertex)
- vertex 0 = top vertex with all directions increased

For face k (removing vertex k): the shared vertices {v_j : j ≠ k} include vertex d = base
and vertex 0 = top.

For boundary_face at face k:
- adj S k = none means face k of S is on the geometric boundary
- ∀ j ≠ k: onFace (vertex j) k  

For k = Fin.last d: adj S (Fin.last d) = none means base is on face d (Σbase = N).
∀ j ≠ Fin.last d: onFace (vertex j) (Fin.last d) means Σ vertex_j.coords = N.
vertex j.coords[l] = base[l] + (1 if l ∈ {σ(j),...,σ(d-1)} else 0)
Σ vertex_j.coords = Σbase + (d - j)
= N + (d - j) for j < d... This equals N only if j = d, which is removed!

Still broken!

**FINAL CONCLUSION**: The SpernerNDim `boundary_face` axiom requires a very specific
vertex labeling that is non-trivial to achieve with the standard Freudenthal triangulation.
The "natural" labelings all produce problems.

The KEY INSIGHT needed: in SpernerNDim, the axiom says:
  adj s k = none → ∀ j ≠ k, onFace (vertices s j) k

For this to hold, the BOUNDARY condition "adj s k = none" must exactly correspond to
the geometric face k: ALL non-k vertices lie on face k.

For face k = Fin.last d (face d = "last barycentric coord = 0"):
- adj s (Fin.last d) = none
- All non-d vertices have Σcoords = N (i.e., last bary coord = 0)
- This means ALL vertices except vertex d are on face d!
- So vertex d is the INTERIOR vertex (not on face d), and all others are on face d.

For the constant-miss FSimplex, vertex d = base + all steps = base with all coords +1.
Vertex d's last bary coord = N - Σbase - d. For this to be 0: Σbase + d = N.
The other vertices (k < d) have last bary coord = N - Σbase - k > 0 (since k < d).

So with Σbase + d = N: vertices 0,...,d-1 have last bary coord > 0 (NOT on face d),
and vertex d has last bary coord = 0 (ON face d). This is the OPPOSITE of what we need!

boundary_face requires: ∀ j ≠ Fin.last d, vertex j is on face d. But ONLY vertex d
(= Fin.last d) is on face d, not the others!

THE FIX: Re-index so vertex 0 = the "top" vertex (with all steps taken, on face d),
and vertex d = base (the "bottom" vertex, with no steps).

With this convention:
- vertex 0 has coords[j] = base[j] + 1 for all j; Σ = Σbase + d = N ✓ (on face d!)
- vertex 1 has coords[j] = base[j] + (1 if j ≠ σ(0) else 0); Σ = Σbase + d - 1 < N ✓
- vertex k has coords[j] = base[j] + (if j ∉ {σ(0),...,σ(k-1)} then 1 else 0) WAIT this doesn't work

Let me rewrite: with INVERTED labeling where vertex 0 = top:

vertex k has coords[j] = base[j] + (d - k steps taken in direction j):
- vertex k.coords[j] = base[j] + (1 if j ∉ {σ(0),...,σ(k-1)} else 0) for j : Fin d

Actually: vertex k = base + e_{σ(k)} + ... + e_{σ(d-1)} (remaining steps not yet "removed")
= base + Σ_{j=k}^{d-1} e_{σ(j)}

vertex 0 = base + Σ_{j=0}^{d-1} e_{σ(j)} = base with all d explicit coords +1: Σ = Σbase+d = N ✓
vertex d = base: Σ = Σbase < N ✓

For boundary_face at k = Fin.last d:
- adj S (Fin.last d) = none iff vertex d = base has Σbase = N - d... wait, that means
  vertex d is on face d? No: onFace v (Fin.last d) means Σv.coords = N.
  base has Σbase = N - d (from Σbase + d = N). So Σbase = N - d ≠ N.

Hmm, so vertex d (= base) is NOT on face d either.

And vertex 0 has Σ = Σbase + d = N → vertex 0 IS on face d ✓.
And vertex 1 has Σ = Σbase + d - 1 = N - 1 ≠ N → NOT on face d.

So only vertex 0 is on face d, and we need ∀ j ≠ Fin.last d, vertex j on face d.
That means all vertices except vertex d (= Fin.last d) must be on face d.
But only vertex 0 is on face d!

Still broken for vertices 1,...,d-1!

THE CONCLUSION: The standard FSimplex approach (for d ≥ 2) CANNOT satisfy the
SpernerNDim boundary_face axiom as stated. Either the axiom needs to be reformulated,
or a completely different triangulation structure is needed.

## Alternate Path: Avoid boundary_face Completely

Observation: `sperner_ndim` requires `hbdry : Odd(boundary_doors_on_face_d)`.
`boundary_doors_eq_face_d` (proved in SpernerNDim) shows:
  filter (p : Simplex × Fin(d+1)) (isDoorAt AND adj=none AND p.2=Fin.last d)

This filter doesn't directly use `boundary_face`. The `boundary_face` axiom is used
in `no_boundary_doors_face_lt` which says: for Sperner coloring, no doors at face k < d.
This is proved using: if adj s k = none then all non-k vertices on face k.

THE KEY: `no_boundary_doors_face_lt` is already proved in SpernerNDim.lean (abstractly).
It's used to prove that boundary doors ⊆ face d. Without `boundary_face`, we can't
prove this restriction.

So `boundary_face` IS necessary for the Sperner theorem to work correctly.

## Corrected Approach: Custom Coloring on Simplex Boundary

For the standard simplex with the Freudenthal triangulation, the "face d" in SpernerNDim
corresponds to the face where the LAST barycentric coordinate is 0. For vertices on this
face, the coloring assigns colors in {0,...,d-1} (by the spernerColor_ne_of_zero lemma).

For the induction to work, we need: boundary doors are the simplices where the
"outer" face is on the last geometric face, which for our triangulation must coincide
with adj = none for face Fin.last d.

The CORRECT triangulation must be designed so that:
- adj s (Fin.last d) = none ↔ ALL non-(Fin.last d) vertices are on the LAST geometric face

This means vertex d (labeled Fin.last d) is the INTERIOR vertex, and all others are on face d.

For FSimplex with INVERTED step ordering:
- vertex d = INSIDE vertex (not on face d)  
- vertices 0,...,d-1 = ALL on face d (last bary coord = 0)

For all vertices 0,...,d-1 to have last bary coord = 0 (Σcoords = N):
We need Σ vertex_k.coords = N for all k < d.

vertex k (INVERTED) = base + Σ_{j≥k} e_{σ(j)}
Σ vertex_k.coords = Σbase + (d - k)

For this to equal N for all k = 0,...,d-1: need Σbase + (d-k) = N, i.e., Σbase = N-d+k.
But Σbase is FIXED! So this can't hold for all k simultaneously.

**FINAL CONCLUSION**: The SpernerNDim boundary_face axiom requires a triangulation
structure where ALL non-k vertices literally lie on the same geometric face k.
For the Freudenthal triangulation, this is impossible for a single simplex since
the vertices span multiple faces.

**The boundary_face axiom in SpernerNDim is too STRONG for the Freudenthal triangulation.**

Either: (1) The axiom must be weakened, or (2) A different triangulation structure
must be used that satisfies the axiom, or (3) A completely different proof of boundary_doors_odd
must be used that doesn't go through SpernerNDim at all.

## Recommended Fix for Next Session

Build a SELF-CONTAINED Sperner's lemma for the Freudenthal grid, NOT using SpernerNDim.
The proof would:
1. Directly count FC simplices and boundary doors for FreudSimplex
2. Prove boundary_doors_odd by direct induction (bijection argument)
3. NOT require the boundary_face axiom at all

This avoids the incompatible axiom issue and may be more direct.

Estimated: ~500 lines, but structured as a single self-contained proof.
