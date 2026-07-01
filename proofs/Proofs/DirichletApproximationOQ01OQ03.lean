/-
# Dirichlet Approximation — OQ-01-OQ-03: Simultaneous Diophantine Approximation

**Open Question (third open question of OQ-01).** The parent `DirichletApproximation`
proves the *single-real* one-shot pigeonhole bound: for each `Q` there is one
fraction `p/q` with `1 ≤ q ≤ Q` and `|qα − p| < 1/Q`. Its OQ-01 upgrade recasts this
as the classical coprime integer-pair statement and asks, as its third open question,
whether the reformulation

> *"Does it extend to the simultaneous approximation theorem — one denominator
> approximating several reals at once?"*

This file answers that question by proving **Dirichlet's simultaneous approximation
theorem** in full generality over an arbitrary finite family of reals.

## Statement

For real numbers `α : Fin n → ℝ` and any `N ≥ 1`, there is a single denominator
`q` with `1 ≤ q ≤ Nⁿ` and integers `p : Fin n → ℤ` such that, *simultaneously* for
every coordinate `i`,
```
|q · αᵢ − pᵢ| < 1 / N .
```
Equivalently, one denominator `q ≤ Nⁿ` makes all `n` of the numbers `q·αᵢ` lie
within `1/N` of an integer at once. The `n = 1` case recovers the parent one-shot
bound (with `Q = N`).

## Proof

Pure pigeonhole in the `n`-dimensional unit cube. Chop `[0,1)ⁿ` into `Nⁿ` boxes of
side `1/N`. The `Nⁿ + 1` cube points
```
(frac(m·α₀), …, frac(m·α_{n-1})),   m = 0, 1, …, Nⁿ,
```
cannot all lie in distinct boxes, so two of them — say for `m = i > j` — share a box.
Their difference has every coordinate within `1/N`, and taking `q = i − j`,
`pᵢ = ⌊i·αᵢ⌋ − ⌊j·αᵢ⌋` gives the claim, since
`q·αᵢ − pᵢ = frac(i·αᵢ) − frac(j·αᵢ)`.

The "same box ⟹ close" step is isolated as `abs_sub_lt_one_of_floor_eq`: two reals
with equal integer part differ by less than one. This is the multi-dimensional
analogue of the parent's `interval_bound`.

## References

* Mathlib: `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean`
* G.H. Hardy & E.M. Wright, *An Introduction to the Theory of Numbers*, Thm 200
  (simultaneous approximation).
* J.W.S. Cassels, *An Introduction to Diophantine Approximation*, Ch. I §5.
-/
import Mathlib

namespace DirichletApproximationOQ01OQ03

/-- Two reals with the same integer part differ by less than one. This is the
"same box ⟹ close" step of the pigeonhole argument. -/
private lemma abs_sub_lt_one_of_floor_eq {a b : ℝ} (h : ⌊a⌋ = ⌊b⌋) :
    |a - b| < 1 := by
  have ha := Int.fract_nonneg a
  have ha' := Int.fract_lt_one a
  have hb := Int.fract_nonneg b
  have hb' := Int.fract_lt_one b
  have hrw : a - b = Int.fract a - Int.fract b := by
    simp only [Int.fract]; rw [h]; ring
  rw [hrw, abs_lt]
  constructor <;> linarith

/-- The pigeonhole map: index `m ↦ (i ↦ ⌊N · frac(m·αᵢ)⌋)`, sending each of the
`Nⁿ + 1` cube points to one of the `Nⁿ` boxes `(Fin n → Fin N)`. -/
private noncomputable def boxMap {n : ℕ} (α : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
    Fin (N ^ n + 1) → (Fin n → Fin N) := fun m i =>
  ⟨Int.toNat ⌊(N : ℝ) * Int.fract ((m : ℕ) * α i)⌋, by
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have h0 : 0 ≤ (N : ℝ) * Int.fract ((m : ℕ) * α i) :=
      mul_nonneg hN'.le (Int.fract_nonneg _)
    have h1 : (N : ℝ) * Int.fract ((m : ℕ) * α i) < N := by
      have hlt := Int.fract_lt_one ((m : ℕ) * α i)
      nlinarith [Int.fract_nonneg ((m : ℕ) * α i)]
    rw [Int.toNat_lt (Int.floor_nonneg.mpr h0)]
    exact_mod_cast Int.floor_lt.mpr h1⟩

/-- Core step: given a pigeonhole collision with `j < i` (as naturals), extract a
simultaneous approximation with denominator `q = i − j`. -/
private lemma exists_of_gt {n : ℕ} (α : Fin n → ℝ) (N : ℕ) (hN : 0 < N)
    {i j : Fin (N ^ n + 1)} (hgt : (j : ℕ) < (i : ℕ))
    (hfij : boxMap α N hN i = boxMap α N hN j) :
    ∃ (q : ℕ) (p : Fin n → ℤ), 1 ≤ q ∧ q ≤ N ^ n ∧
      ∀ k, |(q : ℝ) * α k - (p k : ℝ)| < 1 / (N : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hji : (j : ℕ) ≤ (i : ℕ) := le_of_lt hgt
  set q : ℕ := (i : ℕ) - (j : ℕ) with hq_def
  refine ⟨q, fun k => ⌊(i : ℕ) * α k⌋ - ⌊(j : ℕ) * α k⌋, ?_, ?_, ?_⟩
  · -- 1 ≤ q
    omega
  · -- q ≤ Nⁿ
    have hi := i.isLt
    omega
  · -- simultaneous bound
    intro k
    -- q·αₖ − pₖ = frac(i·αₖ) − frac(j·αₖ)
    have hkey : (q : ℝ) * α k - ((⌊(i : ℕ) * α k⌋ - ⌊(j : ℕ) * α k⌋ : ℤ) : ℝ)
        = Int.fract ((i : ℕ) * α k) - Int.fract ((j : ℕ) * α k) := by
      simp only [Int.fract, hq_def]
      rw [Nat.cast_sub hji]
      push_cast
      ring
    rw [hkey]
    -- Extract the per-coordinate floor equality from the box collision.
    have hval := congr_fun hfij k
    have hvv : (⌊(N : ℝ) * Int.fract ((i : ℕ) * α k)⌋).toNat
        = (⌊(N : ℝ) * Int.fract ((j : ℕ) * α k)⌋).toNat := by
      have := congr_arg Fin.val hval
      simpa [boxMap] using this
    have hnn_i : 0 ≤ ⌊(N : ℝ) * Int.fract ((i : ℕ) * α k)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hN'.le (Int.fract_nonneg _))
    have hnn_j : 0 ≤ ⌊(N : ℝ) * Int.fract ((j : ℕ) * α k)⌋ :=
      Int.floor_nonneg.mpr (mul_nonneg hN'.le (Int.fract_nonneg _))
    have hfloor : ⌊(N : ℝ) * Int.fract ((i : ℕ) * α k)⌋
        = ⌊(N : ℝ) * Int.fract ((j : ℕ) * α k)⌋ := by omega
    -- Same box ⟹ the scaled fracs are within one of each other.
    have hlt1 : |(N : ℝ) * Int.fract ((i : ℕ) * α k)
        - (N : ℝ) * Int.fract ((j : ℕ) * α k)| < 1 :=
      abs_sub_lt_one_of_floor_eq hfloor
    rw [show (N : ℝ) * Int.fract ((i : ℕ) * α k) - (N : ℝ) * Int.fract ((j : ℕ) * α k)
        = (N : ℝ) * (Int.fract ((i : ℕ) * α k) - Int.fract ((j : ℕ) * α k)) from by ring,
      abs_mul, abs_of_pos hN'] at hlt1
    rw [mul_comm] at hlt1
    exact (lt_div_iff₀ hN').mpr hlt1

/-- **Dirichlet's Simultaneous Approximation Theorem.** For any finite family of
reals `α : Fin n → ℝ` and any `N ≥ 1`, there is a single denominator `q` with
`1 ≤ q ≤ Nⁿ` and integers `p : Fin n → ℤ` such that
`|q · αᵢ − pᵢ| < 1 / N` holds simultaneously for every coordinate `i`.

Proved by the pigeonhole principle in the `n`-dimensional unit cube: the `Nⁿ + 1`
points `(frac(m·αᵢ))ᵢ` for `m = 0, …, Nⁿ` cannot all lie in distinct side-`1/N`
boxes, so two coincide and their difference is the sought approximation. -/
theorem simultaneous_dirichlet {n : ℕ} (α : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ (q : ℕ) (p : Fin n → ℤ), 1 ≤ q ∧ q ≤ N ^ n ∧
      ∀ k, |(q : ℝ) * α k - (p k : ℝ)| < 1 / (N : ℝ) := by
  -- Pigeonhole: Nⁿ + 1 points, Nⁿ boxes.
  have hcard : Fintype.card (Fin n → Fin N) < Fintype.card (Fin (N ^ n + 1)) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hfij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (boxMap α N hN) hcard
  -- Order the colliding indices; both orderings reduce to `exists_of_gt`.
  rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
  · exact exists_of_gt α N hN h hfij.symm
  · exact exists_of_gt α N hN h hfij

/-- The `n = 1` specialization recovers the shape of the parent one-shot bound:
for a single real `α` and `N ≥ 1` there are integers `p, q` with `1 ≤ q ≤ N` and
`|q·α − p| < 1/N`. -/
theorem dirichlet_one_real (α : ℝ) (N : ℕ) (hN : 0 < N) :
    ∃ (q : ℕ) (p : ℤ), 1 ≤ q ∧ q ≤ N ∧ |(q : ℝ) * α - (p : ℝ)| < 1 / (N : ℝ) := by
  obtain ⟨q, p, hq1, hqle, hbound⟩ :=
    simultaneous_dirichlet (fun _ : Fin 1 => α) N hN
  refine ⟨q, p 0, hq1, ?_, hbound 0⟩
  simpa using hqle

end DirichletApproximationOQ01OQ03
