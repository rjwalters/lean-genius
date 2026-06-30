# Research State: sperner-simplicial-instance-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-15T03:10:48-07:00
**Iteration**: 5

## Session 5 (2026-06-15, researcher-4)
Built `verify_standard_triangulation.py`: a CONCRETE, self-validated standard
(Freudenthal) triangulation of `Δ^d` for general `d` (order-polytope coords, cells =
`(base, permutation)` chains; pseudomanifold, cell count `m^d`). On genuine 3-D and 4-D
meshes (first time past 2-D) verified: (P) `sperner_parity` `#FC ≡ #doors-on-face-d mod 2`;
(A) the top facet of the `d`-mesh IS the `(d-1)`-mesh (`s ↦ s[:d-1]`); (R) the recursion
step `#doors(face d) == #FC(induced Δ^{d-1})` with restriction always Sperner — together
closing the full induction on actual standard triangulations. Confirmed no general-`n` Lean
instance exists in either file → constructing it is the dominant build cost; the new script
is the reference algorithm. Dual blackout persists (Docker down, Aristotle 404).

## Current Focus
Re-scoped the ACT by connecting two existing **sorry-free** frameworks.
`boundary_doors_odd` (`SpernerSimplicialInstance.lean:173`) is a proven parity-transfer
theorem: it derives `S = S_n` (all boundary doors on the top facet) from the Sperner
condition, then concludes oddness FROM the hypothesis `_hLastFace`. The genuine gap is
`_hLastFace` (top-facet door oddness).

**New this iteration:** `_hLastFace` does NOT need a from-scratch door-counting/mesh
argument. `SpernerNDim.lean:601` already PROVES (0 sorries, 0 axioms) the abstract
parity engine `sperner_parity`:
> `#FC simplices ≡ #(boundary doors on face d)  (mod 2)` for any `SpernerTriangulation d N`.
The doors on the top facet of `Δⁿ` are exactly the FC (panchromatic) cells of the
`Δⁿ⁻¹` coloring induced on that facet. So `_hLastFace[n]` is literally "Odd #FC of the
induced `Δⁿ⁻¹` Sperner coloring", which `sperner_parity[n-1]` reduces to `_hLastFace[n-1]`,
recursing to the `n=1` base. The remaining Lean work is therefore the cross-dimensional
**facet-restriction map** wiring `SpernerSimplicialInstance.Triangulation` to
`SpernerNDim.SpernerTriangulation` — NOT a new parity proof.

## Active Approach
Discharge `_hLastFace` by induction using the already-proven `sperner_parity` as the
per-level engine: top facet of `Δⁿ` is a `Δⁿ⁻¹` (color `n` forbidden on every facet
vertex, so the restriction is automatically Sperner with labels `{0..n-1}`); its
top-facet doors = FC cells of the induced coloring; oddness by IH (`sperner_parity[n-1]`);
base case `n=1` = one door. Verified numerically (`verify_boundary_doors.py`, all pass):
- n=1 base case (one boundary door), n=2 full boundary-door parity (14k+ colorings, m≤4);
- `sperner_parity` congruence (#FC ≡ #face-2 doors mod 2) holds on the concrete 2-D
  Kuhn mesh — confirming the abstract theorem instantiates on the ACT's triangulation;
- dim-3 → dim-2 reduction discharging `_hLastFace[3]` mesh-free: restriction-is-Sperner
  + #(top-facet doors of Δ³) == #FC of induced Δ² coloring == odd (14k+ induced colorings).

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1

## Blockers
- Docker down this session — no Lean build, so the ACT construction is deferred.
- Lean work needs a general standard/Kuhn `Triangulation` instance (file currently
  has only `intervalTriangulation 1` and a single 2-simplex fixture).

## Next Action
ACT (build-gated; Docker down this session). Re-scoped: do NOT re-prove the parity —
REUSE `SpernerNDim.sperner_parity`. Concretely:
1. Supply a general-n standard/Kuhn `Triangulation`/`SpernerTriangulation` instance
   (file currently has only `intervalTriangulation 1` + a single 2-simplex fixture).
2. Build the facet-restriction map: top facet of the dim-n triangulation → a dim-(n-1)
   `SpernerTriangulation`; prove the induced coloring is Sperner (color `n` forbidden on
   every facet vertex — nearly definitional).
3. Identify dim-n top-facet doors with dim-(n-1) FC cells (the door condition "the d
   vertices ≠ apex carry {0..n-1}" = FC of the facet triangle); then `_hLastFace` follows
   from `sperner_parity[n-1]` + IH, base case n=1.
This is smaller than the prior "~200–400 LOC from scratch" estimate because the parity
counting is already proven; the work is the structural facet-restriction wiring between
the two sorry-free files. Aristotle candidate: the door⟺FC identification lemma once the
instances compile.

## S6 (2026-06-15, researcher-6, REGISTER)
Registered the (previously unregistered) `SpernerSimplicialInstanceOQ03.lean` in
`proofs/Proofs.lean` so the deployer machine-checks its two theorems
(`fc_odd_of_facet_bijection`, `exists_fc_of_lower_fc_odd` — the cross-dimensional
inductive step of Sperner's lemma). The file is 0 real sorries (the lone "sorry"
hit is docstring prose). Verified the proofs are sound: `sperner_parity`
(SpernerNDim.lean:601) and `sperner_ndim` (:654) have door-filter statements that
match the file's `hbij` LHS *exactly* under the `d := d+1` instantiation
(`Fin (d+1+1)`, `Fin.last (d+1)`), so the `rw [Nat.odd_iff, hpar, hbij, ...]` and
`apply sperner_ndim; rw [hbij]` chains close. `SpernerNDim` is registered
(Proofs.lean:2798). Open PR #24453 (researcher-4) edits the file content + JSON
but does NOT register it — this is the complementary missing step. Deployer-gated:
a compile failure blocks merge, not main. (Note: sibling OQ01/OQ04 files are also
unregistered but out of this claim's scope.)
