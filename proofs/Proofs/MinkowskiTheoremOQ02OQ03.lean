/-
# Simultaneous Dirichlet Approximation via Minkowski (OQ-03): S2 ACT seed

## What This Establishes (this revision)

This file is the n-dimensional generalisation of
`Proofs/MinkowskiTheoremOQ02OQ01.lean` (Dirichlet's approximation theorem
via Minkowski, 1D axiom-free). It targets OQ-03 of the parent
`minkowski-theorem-oq-02` slug: prove the **simultaneous Dirichlet
approximation theorem** for `n` real numbers `α : Fin n → ℝ`,

> For every `α : Fin n → ℝ` and `Q ≥ 1`, there exist integers
> `q ≥ 1`, `p : Fin n → ℤ` with `q ≤ Qⁿ` and
> `|α i · q − p i| ≤ 1/Q` for every `i`.

The construction follows Cassels (1957, Theorem I.II.A): take the
parallelepiped

```
dirichletSetN n α Q :=
  {v : Fin (n+1) → ℝ | |v 0| < Qⁿ + 1 ∧
                       ∀ i : Fin n, |α i · v 0 − v i.succ| < 1/Q}
```

apply Minkowski's lattice-point theorem to it (its volume is
`2^(n+1) · (Qⁿ + 1) / Qⁿ > 2^(n+1)`, exceeding the
`(2 : ENNReal)^(n+1)` threshold for the integer lattice in
`Fin (n+1) → ℝ`), extract a non-trivial lattice point, and read off
`q := v 0`, `p i := v i.succ`.

The parent state.md decomposes this into 5 ACT sessions:

| Session | Deliverable | Status |
|---|---|---|
| S2 | `dirichletSetN` def + `dirichletSetN_symmetric` | **this file (merged)** |
| S3 | `dirichletSetN_measurable` (open-set) | **this file (this revision)** |
| S4 | `dirichletSetN_convex` (linear-preimage of `Ioo`) | **this file (this revision)** |
| S5 | `dirichletSetN_volume` (shear-map computation) | future |
| S6 | `simultaneous_dirichlet_from_minkowski` (assembly) | future |

The S2 revision shipped the definition + the central symmetry lemma
(verbatim n-dim generalisation of the parent OQ-01's
`dirichletSet_symmetric`). This S3 + S4 revision adds two more
Minkowski-hypothesis discharges: measurability (S3) and convexity
(S4), both verbatim n-dim generalisations of the parent's
`dirichletSet_measurable` and `dirichletSet_convex`. The S5 / S6
ACTs remain pre-staged via S5 PREP
(`sessions/2026-05-12-s5-prep-shear-volume-generalization.md`,
merged) and S6 PREP
(`sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`, merged).

## Status

- `dirichletSetN`: definition in place.
- `dirichletSetN_symmetric`: sorry-free, axiom-free (S2).
- `dirichletSetN_measurable`: sorry-free, axiom-free (S3, this
  revision; ~12 LOC of proof, n-dim generalisation of the parent's
  `dirichletSet_measurable`).
- `dirichletSetN_convex`: sorry-free, axiom-free (S4, this revision;
  ~12 LOC of proof, n-dim generalisation of the parent's
  `dirichletSet_convex`).
- `axiomCount`: 0.
- `sorryCount`: 0.

## References

- Parent OQ-01 (1D axiom-free Dirichlet): `Proofs/MinkowskiTheoremOQ02OQ01.lean`,
  `dirichletSet` (line 41) and `dirichletSet_symmetric` (line 48).
- Parent OQ (1D with axioms): `Proofs/MinkowskiTheoremOQ02.lean`.
- Cassels, *An Introduction to the Geometry of Numbers*, Springer 1957,
  Theorem I.II.A.
- Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785,
  Springer 1980, Theorem I.1A.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Proofs.MinkowskiFundamentalTheorem

namespace MinkowskiTheoremOQ02OQ03

open OrderDual

-- ============================================================
-- PART 1: The n-dim Dirichlet Parallelepiped (Cassels 1957)
-- ============================================================

/-- The n-dim simultaneous-Dirichlet set after Cassels (1957, Thm I.II.A).

For `α : Fin n → ℝ` and `Q : ℕ`, this is the parallelepiped

    {v : Fin (n+1) → ℝ | |v 0| < Qⁿ + 1 ∧
                         ∀ i : Fin n, |α i · v 0 − v i.succ| < 1/Q}

with `v 0` reserved as the *common-denominator* coordinate (so
`q := v 0` after Minkowski extracts an integer point) and
`v i.succ` carrying the i-th *approximation residual*. At `n = 1`
this specialises to the parent OQ-01's `dirichletSet` modulo
indexing (`Fin 2 → ℝ` with `v 0`, `v 1`). -/
def dirichletSetN (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {v | |v 0| < ((Q : ℝ) ^ n) + 1 ∧
       ∀ i : Fin n, |α i * v 0 - v i.succ| < 1 / (Q : ℝ)}

-- ============================================================
-- PART 2: Central Symmetry (S2 ACT — this revision)
-- ============================================================

/-- **Central symmetry.** `dirichletSetN n α Q` is symmetric about
the origin: if `v` lies in the set, so does `-v`. This is one of the
three hypotheses of Minkowski's lattice-point theorem (the other two —
measurability and convexity — are handled in S3 / S4).

The proof is the verbatim n-dim generalisation of the parent OQ-01's
`dirichletSet_symmetric` (`Proofs/MinkowskiTheoremOQ02OQ01.lean:48-54`)
with the second conjunct quantified by `∀ i : Fin n` instead of being
the single `i = 1` case. -/
theorem dirichletSetN_symmetric (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    ∀ v ∈ dirichletSetN n α Q, -v ∈ dirichletSetN n α Q := by
  intro v ⟨hv0, hvi⟩
  refine ⟨?_, ?_⟩
  · simp only [Pi.neg_apply, abs_neg]; exact hv0
  · intro i
    simp only [Pi.neg_apply]
    rw [show α i * -v 0 - -v i.succ = -(α i * v 0 - v i.succ) by ring, abs_neg]
    exact hvi i

-- ============================================================
-- PART 3: Measurability (S3 ACT — this revision)
-- ============================================================

/-- **Measurability.** `dirichletSetN n α Q` is Lebesgue-measurable.
It is an *open* set in `Fin (n+1) → ℝ` (with the product topology),
which the Borel σ-algebra inherits from the topology, so
`IsOpen.measurableSet` discharges measurability.

Proof structure mirrors the parent OQ-01's `dirichletSet_measurable`
(`Proofs/MinkowskiTheoremOQ02OQ01.lean:60-71`) with the single
`v 1` strict-inequality clause generalised to a `⋂ i : Fin n,
{v | |α i · v 0 − v i.succ| < 1/Q}` indexed intersection. Each
factor is the preimage of `Set.Ioo` under a continuous linear
functional in `v`; `isOpen_iInter_of_finite` discharges the
`Fin n`-indexed intersection. -/
theorem dirichletSetN_measurable (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    MeasurableSet (dirichletSetN n α Q) := by
  apply IsOpen.measurableSet
  have heq : dirichletSetN n α Q =
      (fun v : Fin (n + 1) → ℝ => v 0) ⁻¹'
        Set.Ioo (-((Q : ℝ) ^ n + 1)) ((Q : ℝ) ^ n + 1) ∩
      ⋂ i : Fin n,
        (fun v : Fin (n + 1) → ℝ => α i * v 0 - v i.succ) ⁻¹'
          Set.Ioo (-(1 / (Q : ℝ))) (1 / (Q : ℝ)) := by
    ext v
    simp [dirichletSetN, Set.mem_Ioo, abs_lt, Set.mem_iInter]
  rw [heq]
  refine (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (isOpen_iInter_of_finite ?_)
  intro i
  exact isOpen_Ioo.preimage
    ((continuous_const.mul (continuous_apply 0)).sub (continuous_apply i.succ))

-- ============================================================
-- PART 4: Convexity (S4 ACT — this revision)
-- ============================================================

/-- **Convexity.** `dirichletSetN n α Q` is convex. Each conjunct
is the preimage of an open interval `Set.Ioo` under a linear
functional in `v`, and intersections of convex sets are convex
(`Convex.inter` for the binary common-denominator step;
`convex_iInter` for the `Fin n`-indexed approximation residuals).

Proof structure mirrors the parent OQ-01's `dirichletSet_convex`
(`Proofs/MinkowskiTheoremOQ02OQ01.lean:75-86`) with the single
linear-functional `α • π₀ − π₁` clause generalised to a `⋂ i,
α i • π₀ − π_{i.succ}` indexed intersection. -/
theorem dirichletSetN_convex (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    Convex ℝ (dirichletSetN n α Q) := by
  have heq : dirichletSetN n α Q =
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
        Set.Ioo (-((Q : ℝ) ^ n + 1)) ((Q : ℝ) ^ n + 1) ∩
      ⋂ i : Fin n,
        (α i • LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) 0 -
          LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) i.succ) ⁻¹'
          Set.Ioo (-(1 / (Q : ℝ))) (1 / (Q : ℝ)) := by
    ext v
    simp [dirichletSetN, Set.mem_Ioo, abs_lt, LinearMap.proj_apply, Set.mem_iInter]
  rw [heq]
  refine ((convex_Ioo _ _).linear_preimage _).inter ?_
  exact convex_iInter (fun i => (convex_Ioo _ _).linear_preimage _)

-- ============================================================
-- PART 5: Shear matrix (S5-a ACT — this revision)
-- ============================================================

/-- The n-dim shear matrix used to compute `volume (dirichletSetN n α Q)`.

For `α : Fin n → ℝ`, `shearM α : Matrix (Fin (n+1)) (Fin (n+1)) ℝ`
is the lower-triangular matrix whose nonzero entries are

* `(shearM α) 0 0 = 1`,
* `(shearM α) k.succ 0 = α k` for `k : Fin n` (column 0 below the diagonal),
* `(shearM α) i.succ i.succ = -1` for `i : Fin n` (diagonal at positions > 0).

This generalises the 2×2 shear `!![1, 0; α, -1]` used by the parent
OQ-01 (`Proofs/MinkowskiTheoremOQ02OQ01.lean:101`) to `Fin (n+1)`.

Following the volume route: the linear map `(shearM α).toLin'` carries
`dirichletSetN n α Q` bijectively onto the open box
`(-(Qⁿ+1), Qⁿ+1) × (-1/Q, 1/Q)ⁿ` and has `|det| = 1`, so the volumes
agree. The det = (-1)ⁿ identity proved here is the first of three
ingredients for `dirichletSetN_volume` (S5 ACT). -/
def shearM (n : ℕ) (α : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j =>
    if j = 0 then Fin.cases (1 : ℝ) α i
    else if i = j then (-1 : ℝ) else 0

/-- **Lower triangularity.** Every entry of `shearM α` strictly above
the diagonal is zero. Stated as `BlockTriangular toDual` so the Mathlib
bearer `Matrix.det_of_lowerTriangular` fires directly. -/
theorem shearM_lowerTriangular (n : ℕ) (α : Fin n → ℝ) :
    (shearM n α).BlockTriangular (toDual : Fin (n + 1) → (Fin (n + 1))ᵒᵈ) := by
  intro i j hij
  rw [toDual_lt_toDual] at hij
  simp only [shearM, Matrix.of_apply]
  by_cases hj0 : j = 0
  · exact absurd hij (hj0 ▸ Fin.not_lt_zero i)
  · by_cases hij_eq : i = j
    · exact absurd hij (hij_eq ▸ lt_irrefl _)
    · simp [hj0, hij_eq]

/-- **Determinant of the shear matrix.** `(shearM α).det = (-1)^n`.

Proof: `det_of_lowerTriangular` (via `shearM_lowerTriangular`) collapses
the determinant to `∏ i : Fin (n+1), (shearM α) i i`. The diagonal
splits via `Fin.prod_univ_succ` into `(shearM α) 0 0 = 1` times
`∏ k : Fin n, (shearM α) k.succ k.succ = ∏ k : Fin n, (-1) = (-1)^n`. -/
theorem shearM_det (n : ℕ) (α : Fin n → ℝ) :
    (shearM n α).det = (-1 : ℝ) ^ n := by
  rw [Matrix.det_of_lowerTriangular (shearM n α) (shearM_lowerTriangular n α)]
  rw [Fin.prod_univ_succ]
  have h00 : (shearM n α) 0 0 = 1 := by
    simp [shearM, Matrix.of_apply]
  have hkk : ∀ k : Fin n, (shearM n α) k.succ k.succ = -1 := fun k => by
    simp [shearM, Matrix.of_apply, Fin.succ_ne_zero]
  rw [h00, one_mul]
  simp_rw [hkk]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

-- ============================================================
-- PART 6: Shear linear map components (S5-b ACT — this revision)
-- ============================================================

/-- **Shear preserves first coordinate.** The linear map `(shearM n α).toLin'`
acts as the identity on the `j = 0` coordinate: only the diagonal entry
`(shearM α) 0 0 = 1` contributes to the row-0 mulVec sum, because every
other entry in row 0 vanishes (column 0 hits the upper-triangular zero
slot via `Fin.cases_zero`, and the off-diagonal off-column-0 entries are
ruled out by `0 ≠ k.succ`). -/
theorem shearM_toLin'_apply_zero (n : ℕ) (α : Fin n → ℝ)
    (v : Fin (n + 1) → ℝ) :
    ((shearM n α).toLin' v) 0 = v 0 := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [shearM, Matrix.of_apply]
  · intro j _ hjne
    simp [shearM, Matrix.of_apply, hjne, Ne.symm hjne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Shear acts on residual coordinates.** For `i : Fin n`, the row-`i.succ`
shear formula reads `T v (i.succ) = α i · v 0 − v (i.succ)`. Two non-zero
terms in the row-`i.succ` mulVec sum: column 0 (the lower-triangular block,
`(shearM α) (i.succ) 0 = α i` via `Fin.cases_succ`) and column `i.succ`
(the negative diagonal, `(shearM α) (i.succ) (i.succ) = -1`). All other
columns contribute 0 because `i.succ ≠ k.succ` for `k ≠ i` (by
`Fin.succ_injective`). -/
theorem shearM_toLin'_apply_succ (n : ℕ) (α : Fin n → ℝ)
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    ((shearM n α).toLin' v) i.succ = α i * v 0 - v i.succ := by
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, shearM, Matrix.of_apply, Fin.cases_succ]
  rw [Finset.sum_eq_single i]
  · simp [Fin.succ_ne_zero]; ring
  · intro j _ hjne
    have hsuccne : i.succ ≠ j.succ := fun h => hjne (Fin.succ_injective _ h).symm
    simp [Fin.succ_ne_zero, hsuccne]
  · intro hk
    exact absurd (Finset.mem_univ i) hk

/-- The axis-aligned open box image of `dirichletSetN n α Q` under the
shear `(shearM n α).toLin'`: an `Fin (n+1)`-indexed `Set.pi` of
intervals, with `(−(Qⁿ+1), Qⁿ+1)` on coordinate 0 and `(−1/Q, 1/Q)` on
each `k.succ`. -/
def dirichletBoxN (n : ℕ) (Q : ℕ) : Set (Fin (n + 1) → ℝ) :=
  Set.pi Set.univ fun j : Fin (n + 1) =>
    Set.Ioo (Fin.cases (-((Q : ℝ) ^ n + 1)) (fun _ : Fin n => -(1 / (Q : ℝ))) j)
            (Fin.cases ((Q : ℝ) ^ n + 1) (fun _ : Fin n => 1 / (Q : ℝ)) j)

/-- **Preimage identity.** The Cassels parallelepiped is the preimage of
`dirichletBoxN` under the linear shear `(shearM n α).toLin'`. Combined
with `shearM_det = (-1)^n` (so `|det shearM| = 1`) and
`Real.map_matrix_volume_pi_eq_smul_volume_pi`, this is the bridge from
the parallelepiped's volume to the box's volume (the next S5-c ACT). -/
theorem dirichletSetN_eq_shearM_preimage (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    dirichletSetN n α Q = (shearM n α).toLin' ⁻¹' dirichletBoxN n Q := by
  ext v
  simp only [dirichletSetN, dirichletBoxN, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · rintro ⟨h0, hi⟩ j
    refine j.cases ?_ ?_
    · simp only [Fin.cases_zero, Set.mem_Ioo]
      rw [shearM_toLin'_apply_zero]; exact abs_lt.mp h0
    · intro k
      simp only [Fin.cases_succ, Set.mem_Ioo]
      rw [shearM_toLin'_apply_succ]; exact abs_lt.mp (hi k)
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0
      simp only [Fin.cases_zero, Set.mem_Ioo] at h0
      rw [shearM_toLin'_apply_zero] at h0
      exact abs_lt.mpr h0
    · intro k
      have hk := h k.succ
      simp only [Fin.cases_succ, Set.mem_Ioo] at hk
      rw [shearM_toLin'_apply_succ] at hk
      exact abs_lt.mpr hk

-- ============================================================
-- PART 7: Integer-coordinate extraction (S6α ACT — this revision)
-- ============================================================

open MinkowskiProved in
/-- **Integer coordinates for `stdLattice m`.** Any point in the standard
integer lattice `ℤᵐ ⊆ ℝᵐ` has integer coordinates, packaged as a function
`Fin m → ℤ`.

This is the n-dim generalisation of the parent OQ-02's
`stdLattice2_coords` (`Proofs/MinkowskiTheoremOQ02.lean:147`, stated for
`m = 2`). The proof pattern is the same: membership in the ℤ-span of the
standard basis gives integer coefficients via
`Submodule.mem_span_range_iff_exists_fun`; rewriting `zsmul` as
`ℤ-cast`-scaled `ℝ`-smul via `Int.cast_smul_eq_zsmul` (v4.26.0 modern
form, replacing the older `zsmul_eq_smul_cast`); and coordinate-wise
extraction collapses the sum via `Finset.sum_ite_eq'`.

Specialised at `m := n + 1` in the upcoming
`simultaneous_dirichlet_from_minkowski` (S6 ACT) to read off
`q := c 0` (common-denominator coordinate, after Minkowski extracts a
lattice point) and `p i := c i.succ` (the i-th approximation residual). -/
lemma stdLatticeN_coords {m : ℕ} [NeZero m] (x : stdLattice m) :
    ∃ c : Fin m → ℤ, ∀ i : Fin m, (x : Fin m → ℝ) i = (c i : ℝ) := by
  have hmem : (x : Fin m → ℝ) ∈
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin m))) := x.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc_real : (x : Fin m → ℝ) = ∑ i : Fin m, (c i : ℝ) • Pi.basisFun ℝ (Fin m) i := by
    rw [← hc]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    exact (Int.cast_smul_eq_zsmul (R := ℝ) (c i) (Pi.basisFun ℝ (Fin m) i)).symm
  refine ⟨c, fun i ↦ ?_⟩
  rw [hc_real]
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply,
             Pi.single_apply, smul_ite, smul_zero, smul_eq_mul, mul_one,
             Finset.sum_ite_eq', Finset.mem_univ, if_true]

end MinkowskiTheoremOQ02OQ03
