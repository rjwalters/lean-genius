import Proofs.EhrhartPolynomials
import Proofs.PicksTheorem

/-
# Pick's Theorem Derived from Ehrhart Polynomial Existence
# (ehrhart-cube-proven-oq-05, S2 ACT scaffold)

## What This Will Prove

The standalone `picks_theorem` axiom in `PicksTheorem.lean` is
*redundant* given the three Ehrhart axioms already declared in
`EhrhartPolynomials.lean`:

* `ehrhart_theorem`              — existence of a degree-d polynomial
                                    counting lattice points in dilations,
* `ehrhart_leading_coeff_volume` — leading coefficient = volume of P
                                    (per-polytope, pinned by `P.volume`),
* `ehrhart_macdonald_reciprocity`— interior count = (-1)^d L_P(-n).

The target identity is Pick's formula `A = i + b/2 - 1` for any
simple lattice polygon, derived purely from the three Ehrhart axioms
+ the gallery's already-proven conditional `picks_from_ehrhart`
(line 237 of `EhrhartPolynomials.lean`).

## S2 ACT Scope (this file)

This scaffold introduces three theorem stubs corresponding to stages
S3, S4, S5 of the R1 (conditional Pick's theorem via Ehrhart) route:

| Stub                                    | Future Stage | Approx. discharge |
|-----------------------------------------|--------------|------------------|
| `ehrhartPoly_2d_explicit`               | S3 (done)   | discharged     |
| `simpleLatticePolygon_to_latticePolygon`| S4          | ~150 lines     |
| `picks_theorem_derived`                 | S5          | ~80 lines      |

The S3 stub `ehrhartPoly_2d_explicit` is now discharged (0 sorries);
the S4/S5 stubs remain `sorry`, the subject of later iterations.

## Status

- 2 sorries (S4 bridge + S5 close; S3 `ehrhartPoly_2d_explicit` discharged).
- 0 new axioms; 3 inherited Ehrhart axioms from `EhrhartPolynomials`.
- 0 new structures. S3 relies on the `LatticePolygon.volume_eq_area`
  definitional-bridge field (added alongside this discharge).

After all three stubs discharge to `0 sorries`, the deliverable is a
**conditional Pick's theorem**: 3 inherited Ehrhart axioms, no new
axioms — a meaningful axiom-dependency reduction in the gallery.

## References

- S2 PREP blueprint: `research/problems/ehrhart-cube-proven-oq-05/knowledge.md`
  §"Lean Skeleton Sketch for S2".
- AXIOM-FIX (PR #22648, merged 2026-06-09): added the
  `LatticePolytope.volume`, `LatticePolytope.volume_pos`, and
  `LatticePolygon.interior_at_one` fields that the discharges in
  S3-S5 will rely on.
-/

namespace EhrhartCubeProvenOQ05

open EhrhartPolynomials Polynomial

/-- **Q1 / S3 target**: the Ehrhart polynomial of a 2D lattice polygon
has the explicit closed form `A·n² + (b/2)·n + 1`, where `A = P.area`
and `b = P.boundaryPoints`.

The S3 discharge will:
1. Use `ehrhart_leading_coeff_volume` to pin the leading coefficient
   to `P.area` (after identifying `P.volume = P.area` for 2D polygons).
2. Use `ehrhart_constant_term` (already proved) for the constant term `1`.
3. Use `ehrhart_macdonald_reciprocity` at `n = -1` together with
   `P.interior_at_one` to extract the linear coefficient as `b/2`,
   via the 4-line algebraic argument in knowledge.md §"The Q1 Polynomial
   Identity". -/
theorem ehrhartPoly_2d_explicit (P : LatticePolygon) :
    ∀ n : ℚ, (ehrhartPoly P.toLatticePolytope).eval n =
      P.area * n ^ 2 + (P.boundaryPoints : ℚ) / 2 * n + 1 := by
  have hdeg : (ehrhartPoly P.toLatticePolytope).natDegree = 2 :=
    ehrhartPoly_degree P.toLatticePolytope
  -- A degree-2 polynomial expands to coeff0 + coeff1·x + coeff2·x².
  have hexp : ∀ x : ℚ, (ehrhartPoly P.toLatticePolytope).eval x =
      (ehrhartPoly P.toLatticePolytope).coeff 0
        + (ehrhartPoly P.toLatticePolytope).coeff 1 * x
        + (ehrhartPoly P.toLatticePolytope).coeff 2 * x ^ 2 := by
    intro x
    rw [eval_eq_sum_range, hdeg]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  -- Constant term is 1 (origin is the only lattice point of 0·P).
  have hc0 : (ehrhartPoly P.toLatticePolytope).coeff 0 = 1 := by
    have h := ehrhart_constant_term P.toLatticePolytope
    rw [hexp 0] at h
    simpa using h
  -- Leading (degree-2) coefficient = volume = area.
  have hc2 : (ehrhartPoly P.toLatticePolytope).coeff 2 = P.area := by
    have hlead := ehrhart_leading_coeff_volume 2 P.toLatticePolytope
    unfold Polynomial.leadingCoeff at hlead
    rw [hdeg] at hlead
    rw [hlead]; exact P.volume_eq_area
  -- L_P(1) = total lattice points = interior + boundary.
  have heval1 : (ehrhartPoly P.toLatticePolytope).eval 1
      = (P.interiorPoints : ℚ) + (P.boundaryPoints : ℚ) := by
    have h := ehrhartPoly_eval P.toLatticePolytope 1
    rw [P.total_eq] at h
    push_cast at h
    linarith [h]
  -- L_P(-1) = interior count, via Ehrhart–Macdonald reciprocity (d = 2).
  obtain ⟨ic, hic⟩ := ehrhart_macdonald_reciprocity 2 P.toLatticePolytope
  have hic1 : ic 1 = P.interiorPoints := P.interior_at_one ic hic
  have heval_neg1 : (ehrhartPoly P.toLatticePolytope).eval (-1)
      = (P.interiorPoints : ℚ) := by
    have h := hic 1 (by norm_num)
    rw [hic1] at h
    push_cast at h
    norm_num at h
    linarith [h]
  -- Linear coefficient: from L_P(1) and L_P(-1), coeff 1 = b/2.
  have hc1 : (ehrhartPoly P.toLatticePolytope).coeff 1
      = (P.boundaryPoints : ℚ) / 2 := by
    have key1 := hexp 1
    have key2 := hexp (-1)
    rw [heval1] at key1
    rw [heval_neg1] at key2
    norm_num at key1 key2
    linarith [key1, key2]
  intro n
  rw [hexp n, hc0, hc1, hc2]
  ring

/-- **Q2 / S4 target**: every `PicksTheorem.SimpleLatticePolygon`
arises from a `LatticePolygon`. The bridge identifies the two
parallel polygon structures.

`SimpleLatticePolygon` carries `(interior_count, boundary_count, area)`;
`LatticePolygon` carries the same data plus the underlying
`LatticePolytope 2` (lattice point count function, volume, ...).

The S4 discharge will construct the underlying counting function via
the existential supplied by `ehrhart_theorem` and verify the structure
laws (`nonempty`, `count_zero`, `total_eq`, `interior_at_one`) from
the corresponding Ehrhart axioms. -/
noncomputable def simpleLatticePolygon_to_latticePolygon
    (P : PicksTheorem.SimpleLatticePolygon) : LatticePolygon :=
  sorry

/-- **Q2 close / S5 target**: Pick's formula `A = i + b/2 - 1` for
any simple lattice polygon, derived from the three Ehrhart axioms.

The S5 discharge will:
1. Apply `simpleLatticePolygon_to_latticePolygon` to obtain the
   companion `LatticePolygon`.
2. Apply `ehrhartPoly_2d_explicit` at `n = 1` to obtain
   `L_P(1) = A + b/2 + 1`.
3. Combine with `LatticePolygon.total_eq` (`L_P(1) = i + b`) and the
   conditional `picks_from_ehrhart` (line 237 of `EhrhartPolynomials.lean`)
   to conclude `A = i + b/2 - 1`. -/
theorem picks_theorem_derived (P : PicksTheorem.SimpleLatticePolygon) :
    P.area = (P.interior_count : ℚ) + (P.boundary_count : ℚ) / 2 - 1 := by
  sorry

end EhrhartCubeProvenOQ05
