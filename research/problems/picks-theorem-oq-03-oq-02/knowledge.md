# Knowledge Base: picks-theorem-oq-03-oq-02

Is the h*-vector (Ehrhart δ-vector) determined by the face lattice of a lattice
polytope?

## Source
Seeker-selected gallery-extracted open question extending **picks-theorem-oq-03**
(parent file `proofs/Proofs/PicksTheoremOQ03.lean`).

---

## Insights

### Session 2026-06-15 (ORIENT) — answer is NO; Reeve tetrahedra witness it (and tie to Pick)

**Mode**: FRESH · **Outcome**: ORIENT (definitive negative answer + durable exact
counterexample; Lean ACT requires Ehrhart theory absent from Mathlib).

**Answer: NO.** The h*-vector is a *lattice-geometric* invariant, not a purely
combinatorial one. Combinatorially identical lattice polytopes (isomorphic face
lattices) can have different h*-vectors. The canonical witness is the family of
**Reeve tetrahedra**

    T_h = conv{ (0,0,0), (1,0,0), (0,1,0), (1,1,h) },   h = 1,2,3,…

Every `T_h` is a tetrahedron with the SAME face lattice (f-vector `(4,6,4,1)`, the
boolean lattice `B_4`), and each has *exactly its 4 vertices* as lattice points
(0 interior, 0 non-vertex boundary at `t=1`, so `L_{T_h}(1)=4` for all `h`). Yet
the Ehrhart polynomials differ:

    L_{T_h}(t) = (h/6) t³ + t² + (2 − h/6) t + 1,
    h*-vector  h*(T_h) = (1, 0, h−1, 0),   Σ = h = normalized volume.

The h*-vectors are pairwise distinct (verified `h=1..6`), so no function of the
face lattice could output them.

**Tie to the parent (Pick's theorem).** Reeve's tetrahedra are *exactly* the
classical obstruction to a 3D Pick theorem: all `T_h` have the same interior- and
boundary-lattice-point counts (just the 4 vertices) but Euclidean volume `h/6`,
so volume is NOT a function of the lattice-point counts in dimension 3. Pick's
2D identity `A = I + B/2 − 1` has no naive 3D analogue — the missing data is
exactly the (non-combinatorial) h*-vector / Ehrhart δ-vector.

**Durable artifact** `verify_hstar_not_combinatorial.py` (stdlib `fractions`,
exact, all PASS): exact barycentric lattice-point counting of `tT_h` for `t=0..4`,
h*-vector via the binomial transform, confirming (A) shared f-vector + shared
`L(1)=4`, and (B) pairwise-distinct h*-vectors `(1,0,h−1,0)`.

**Mathlib status.** No Ehrhart theory upstream (`Ehrhart`, `hStarVector`,
`latticePolytope`+Ehrhart = 0 hits). The 2D parent uses an ad-hoc lattice-polygon
area/`Pick` development, not a general Ehrhart framework.

---

## Next steps

1. **ACT (Lean, Docker-gated, heavy).** A faithful formalization needs an Ehrhart
   layer (lattice-point counting of dilates `tP`, the polynomiality `L_P ∈ ℚ[t]`,
   the h*-transform) which is ABSENT from Mathlib — a multi-file build. A LIGHT,
   self-contained ACT that still answers the question: define `L_{T_h}(t)` for the
   concrete Reeve family by `decide`/closed form, compute `h*(T_h)=(1,0,h−1,0)`,
   and prove `h*(T_1) ≠ h*(T_2)` while exhibiting a face-lattice isomorphism
   `T_1 ≅ T_2` — a finite, build-checkable refutation of "h* is combinatorial".
2. Record the connection in the `picks-theorem-oq-03` cluster: Reeve = the reason
   no 3D Pick identity exists (already implicit; make explicit).

## Dead Ends / Non-starters

- Trying to PROVE "h* is combinatorial" — it is false; Reeve refutes it outright.
- A full general Ehrhart formalization is overkill for the question; the concrete
  Reeve family suffices and is `decide`-friendly.
