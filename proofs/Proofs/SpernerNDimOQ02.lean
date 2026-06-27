import Proofs.SpernerNDim
import Proofs.SpernerGrid

/-
# sperner-ndim-oq-02: BaryPoint ≃ Vertex coordinate bridge

The abstract Sperner framework `SpernerNDim` indexes grid points by
`SpernerNDim.Vertex d N` — *Kuhn coordinates*: a function `Fin d → ℕ` with
`∑ ≤ N`, where the last (omitted) barycentric coordinate is the slack `N - ∑`.
The concrete Freudenthal grid in `SpernerGrid` uses *full barycentric
coordinates* `SpernerGrid.BaryPoint d N` — a function `Fin (d+1) → ℕ` with
`∑ = N`.

These two coordinate systems are canonically isomorphic:

* drop the last barycentric coordinate to obtain a Kuhn vertex
  (`toVertex`), and
* append the slack `N - ∑` as the last coordinate to recover the
  barycentric point (`toBary`).

This file establishes that `Equiv` (`baryEquivVertex`) together with the
matching `onFace` correspondence (`onFace_toVertex`). It is the foundational
bridge of "Option C" for `sperner-ndim-oq-02`: it lets the complete (0-sorry)
`SpernerNDim` framework be reused over `BaryPoint` without re-deriving it. See
`research/problems/sperner-ndim-oq-02/` for the full plan.

No new axioms or sorries are introduced.
-/

open Finset BigOperators

namespace SpernerNDimOQ02

variable {d N : ℕ}

/-- Forward map: drop the last barycentric coordinate.
    A barycentric point `(b₀, …, b_d)` with `∑ = N` maps to the Kuhn vertex
    `(b₀, …, b_{d-1})`, whose coordinate sum is `N - b_d ≤ N`. -/
def toVertex (b : SpernerGrid.BaryPoint d N) : SpernerNDim.Vertex d N where
  coords := fun i => b.coords i.castSucc
  valid := by
    have hsum : ∑ i : Fin (d + 1), b.coords i = N := b.sum_eq
    rw [Fin.sum_univ_castSucc] at hsum
    have : ∑ i : Fin d, b.coords i.castSucc ≤ N := by omega
    exact this

/-- Backward map: append the slack `N - ∑` as the last barycentric coordinate.
    A Kuhn vertex `(x₀, …, x_{d-1})` with `∑ ≤ N` maps to the barycentric point
    `(x₀, …, x_{d-1}, N - ∑)`, whose coordinate sum is exactly `N`. -/
def toBary (v : SpernerNDim.Vertex d N) : SpernerGrid.BaryPoint d N where
  coords := Fin.snoc v.coords (N - ∑ i, v.coords i)
  sum_eq := by
    have hv : ∑ i, v.coords i ≤ N := v.valid
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    omega

@[simp]
theorem toVertex_coords (b : SpernerGrid.BaryPoint d N) (i : Fin d) :
    (toVertex b).coords i = b.coords i.castSucc := rfl

@[simp]
theorem toBary_coords_castSucc (v : SpernerNDim.Vertex d N) (i : Fin d) :
    (toBary v).coords i.castSucc = v.coords i := by
  simp [toBary]

@[simp]
theorem toBary_coords_last (v : SpernerNDim.Vertex d N) :
    (toBary v).coords (Fin.last d) = N - ∑ i, v.coords i := by
  simp [toBary]

/-- `toBary` is a left inverse of `toVertex` (round-trip on barycentric points).
    Recovering the dropped last coordinate from `∑ = N` reconstructs `b`. -/
theorem toBary_toVertex (b : SpernerGrid.BaryPoint d N) :
    toBary (toVertex b) = b := by
  apply SpernerGrid.BaryPoint.ext
  funext i
  cases i using Fin.lastCases with
  | last =>
    have hsum : ∑ i : Fin (d + 1), b.coords i = N := b.sum_eq
    rw [Fin.sum_univ_castSucc] at hsum
    simp only [toBary_coords_last, toVertex_coords]
    omega
  | cast j => simp

/-- `toBary` is a right inverse of `toVertex` (round-trip on Kuhn vertices).
    Dropping the appended slack coordinate reconstructs `v`. -/
theorem toVertex_toBary (v : SpernerNDim.Vertex d N) :
    toVertex (toBary v) = v := by
  apply SpernerNDim.Vertex.ext
  funext i
  simp

/-- **The coordinate bridge.** Barycentric lattice points on the `d`-simplex
    are in canonical bijection with Kuhn vertices, via dropping/appending the
    last barycentric coordinate. -/
def baryEquivVertex (d N : ℕ) : SpernerGrid.BaryPoint d N ≃ SpernerNDim.Vertex d N where
  toFun := toVertex
  invFun := toBary
  left_inv := toBary_toVertex
  right_inv := toVertex_toBary

@[simp] theorem baryEquivVertex_apply (b : SpernerGrid.BaryPoint d N) :
    baryEquivVertex d N b = toVertex b := rfl

@[simp] theorem baryEquivVertex_symm_apply (v : SpernerNDim.Vertex d N) :
    (baryEquivVertex d N).symm v = toBary v := rfl

/-- **Face correspondence.** A barycentric point lies on face `k` of the
    `d`-simplex exactly when its image Kuhn vertex does. For `k < d` both
    conditions say "the `k`-th coordinate is `0`"; for `k = d` (the last face)
    the barycentric condition `b_d = 0` matches the Kuhn condition `∑ = N`. -/
theorem onFace_toVertex (b : SpernerGrid.BaryPoint d N) (k : Fin (d + 1)) :
    SpernerNDim.onFace (toVertex b) k ↔ b.onFace k := by
  unfold SpernerNDim.onFace SpernerGrid.BaryPoint.onFace
  split
  · -- k < d : both sides are "the k-th coordinate is 0"
    rename_i h
    have hcast : (⟨(k : ℕ), h⟩ : Fin d).castSucc = k := by
      apply Fin.ext
      simp
    simp only [toVertex_coords, hcast]
  · -- k = last d : ∑ = N  ↔  b_d = 0
    rename_i h
    simp_rw [toVertex_coords]
    have hsum : ∑ i : Fin (d + 1), b.coords i = N := b.sum_eq
    rw [Fin.sum_univ_castSucc] at hsum
    have hk : k = Fin.last d := by
      apply Fin.ext
      have hlt := k.isLt
      simp only [Fin.val_last]
      omega
    rw [hk]
    omega

/-- The bridge transports Sperner colorings: a coloring of the barycentric grid
    is Sperner iff the corresponding coloring of Kuhn vertices is. -/
theorem isSperner_iff (c : SpernerNDim.Vertex d N → Fin (d + 1)) :
    SpernerNDim.IsSperner c ↔
      SpernerGrid.IsSperner (fun b => c (toVertex b)) := by
  constructor
  · intro hc b k hbk
    exact hc (toVertex b) k ((onFace_toVertex b k).mpr hbk)
  · intro hc v k hvk
    have hb : (toBary v).onFace k := by
      have hov : SpernerNDim.onFace (toVertex (toBary v)) k := by
        rw [toVertex_toBary]; exact hvk
      exact (onFace_toVertex (toBary v) k).mp hov
    have h2 := hc (toBary v) k hb
    simp only [toVertex_toBary] at h2
    exact h2

end SpernerNDimOQ02
