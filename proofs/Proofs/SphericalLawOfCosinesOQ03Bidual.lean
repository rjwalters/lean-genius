/-
# Spherical Law of Cosines — OQ-03: Biduality of the polar triangle

Companion to `Proofs.SphericalLawOfCosinesOQ03`.  That file develops the polar
triangle of a spherical triangle `u, v, w` through the edge normals

  `U = v × w`,   `V = w × u`,   `W = u × v`,

and shows (Part VII) that the *inner products* among `U, V, W` realise the
`π − ·` side/angle swap of polar duality.  What it does **not** record is the
defining structural fact of polar duality: that it is an **involution** — the
polar triangle of the polar triangle is the original triangle again.

This file supplies that missing piece, in the same self-contained, radical-free,
division-free `ring`-only cross-product algebra (reusing `V`, `cross`, `triple`,
`dot` from the parent OQ-03 file).

## Contents

* `polar_bidual_u/v/w` — **biduality**: the edge normals of the polar triangle
  recover the original vertices, each scaled by the scalar triple product:

    `(w×u) × (u×v) = [u v w] • u`,
    `(u×v) × (v×w) = [u v w] • v`,
    `(v×w) × (w×u) = [u v w] • w`.

  Equivalently `(T')' = [u v w] · T`: applying the polar construction twice
  returns the original triangle up to the (positive, for a proper triangle)
  factor `[u v w]`.  This is the vector identity `(a×b)×(c×d) = c[a,b,d] − d[a,b,c]`
  specialised to the polar vertices.

* `polar_triple_sq` — the **polar volume** identity: the scalar triple product of
  the polar vertices is the square of the original,

    `[v×w, w×u, u×v] = [u v w]²`.

  (Geometrically `[U V W] = sin²A sin²b sin²c · …`; here it is exactly `[u v w]²`,
  so the polar triangle is degenerate iff the original is.)

All proofs are component-level polynomial identities closed by `ring`, exactly as
`binet_cauchy` / `triple_sq` in the parent file.

Axioms: 0.  Sorries: 0.

NOTE: build-pending — authored under a Docker blackout (host `lake`/Docker
unavailable).  Deliberately UNREGISTERED in `Proofs.lean` until a post-blackout
session verifies it via
`./proofs/scripts/docker-build.sh Proofs.SphericalLawOfCosinesOQ03Bidual`.
Reuses only the parent file's `ring`-provable definitions; no new Mathlib bearers.
-/

import Proofs.SphericalLawOfCosinesOQ03

namespace SphericalLawOfCosinesOQ03

/-- Scalar multiple of a 3-vector (the parent `V` carries no module structure;
this is the minimal scaling needed to state biduality). -/
def smulV (r : ℝ) (a : V) : V := ⟨r * a.x, r * a.y, r * a.z⟩

/-- **Biduality at vertex `u`.**  The cross product of the two polar vertices
`V = w×u` and `W = u×v` recovers `u`, scaled by the triple product:

  `(w×u) × (u×v) = [u v w] • u`. -/
theorem polar_bidual_u (u v w : V) :
    cross (cross w u) (cross u v) = smulV (triple u v w) u := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v; obtain ⟨w1, w2, w3⟩ := w
  simp only [cross, triple, dot, smulV, V.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- **Biduality at vertex `v`.**  `(u×v) × (v×w) = [u v w] • v`. -/
theorem polar_bidual_v (u v w : V) :
    cross (cross u v) (cross v w) = smulV (triple u v w) v := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v; obtain ⟨w1, w2, w3⟩ := w
  simp only [cross, triple, dot, smulV, V.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- **Biduality at vertex `w`.**  `(v×w) × (w×u) = [u v w] • w`. -/
theorem polar_bidual_w (u v w : V) :
    cross (cross v w) (cross w u) = smulV (triple u v w) w := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v; obtain ⟨w1, w2, w3⟩ := w
  simp only [cross, triple, dot, smulV, V.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- **Polar volume.**  The scalar triple product of the polar-triangle vertices
`U = v×w`, `V = w×u`, `W = u×v` is the square of the original triple product:

  `[v×w, w×u, u×v] = [u v w]²`.

So the polar triangle is degenerate (`[U V W] = 0`) exactly when the original is. -/
theorem polar_triple_sq (u v w : V) :
    triple (cross v w) (cross w u) (cross u v) = (triple u v w) ^ 2 := by
  obtain ⟨u1, u2, u3⟩ := u; obtain ⟨v1, v2, v3⟩ := v; obtain ⟨w1, w2, w3⟩ := w
  simp only [triple, dot, cross]
  ring

end SphericalLawOfCosinesOQ03
