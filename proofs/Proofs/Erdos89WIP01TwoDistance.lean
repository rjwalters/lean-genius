/-
# Erdős 89 (distinct distances) — the polynomial-method two-distance bound

**Research entry: erdos-89-wip-01, session 2026-09-29.**

Erdős's distinct-distances function `g(n) = minDistinctDistances n` currently
has exact values `g(2) = g(3) = 1`, `g(4) = g(5) = 2` and the general floor
`g(n) ≥ 2` for `n ≥ 4` (from `no_four_equidistant`), with the uniform ceiling
`g(n) ≤ ⌊n/2⌋` (regular `n`-gon). No lower bound beyond `2` existed in-repo:
the blocked route asks for the *sharp* planar two-distance-set theorem
(≤ 5 points), which needs case analysis well beyond current infrastructure.

This file supplies the **polynomial (linear-algebra) method** at its naive
strength — materially new machinery for this problem, and enough for the
first `≥ 3` bound:

* `two_distance_card_le_ten`: a planar set whose pairwise distances take at
  most two positive values has **at most 10 points**. Proof: to each point
  `p` attach `F_p(x) = (‖x − p‖² − a²)·(‖x − p‖² − b²)`. These functions
  live in the 10-dimensional span of
  `{Q², Q·x₀, Q·x₁, Q, x₀², x₀x₁, x₁², x₀, x₁, 1}` (where `Q = x₀² + x₁²`),
  and they are linearly independent because `F_p(q) = 0` for distinct points
  `p, q` of the set while `F_p(p) = a²b² ≠ 0` — a diagonal evaluation kills
  every coefficient. Hence #points ≤ dim = 10.
* `card_le_ten_of_numDistinctDistances_le_two`: the same bound phrased
  against the gallery's `numDistinctDistances`.
* **`three_le_minDistinctDistances`**: `g(n) ≥ 3` for all `n ≥ 11` — the
  first lower bound beyond the `no_four_equidistant` floor, giving with the
  `n`-gon ceiling the bracket `3 ≤ g(n) ≤ ⌊n/2⌋` (`n ≥ 11`), pinned at
  `g(11) ∈ [3, 5]` (`minDistinctDistances_eleven_mem_Icc`).

What this does NOT give: the sharp two-distance maximum is 5 (Kelly), and
the Larman–Rogers–Seidel rank bound gives 6; either would improve the
threshold `11` to `7` (via LRS) resp. `6` (sharp), yielding `g(7) = 3` resp.
`g(6) = 3`. Both need genuinely finer arguments than the diagonal-evaluation
scheme below and stay on the blocked-route ledger.

## References

* P. Erdős, *On sets of distances of n points*, Amer. Math. Monthly 53
  (1946), 248–250.
* D. G. Larman, C. A. Rogers, J. J. Seidel, *On two-distance sets in
  Euclidean space*, Bull. LMS 9 (1977), 261–267. (The rank method; the
  10 = dim bound below is its naive planar instance.)
* L. M. Kelly, *Elementary problem E 735*, Amer. Math. Monthly 54 (1947).
  (The sharp planar maximum 5.)

0 axioms, 0 sorries.
-/
import Mathlib
import Proofs.Erdos89Problem
import Proofs.Erdos89WIP01
import Proofs.Erdos89WIP01Ngon

namespace Erdos89

open Finset

/-! ### Section 1. Coordinate expansion of the squared distance -/

/-- The squared norm of a difference in the plane, in coordinates. -/
theorem norm_sub_sq_coords (x p : EuclideanSpace ℝ (Fin 2)) :
    ‖x - p‖ ^ 2 = (x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two, sq_abs]

/-! ### Section 2. The per-point polynomial and its 10-dimensional home -/

/-- The Larman–Rogers–Seidel polynomial of a point `p` at distance values
`a, b`: it vanishes at every `x` whose distance to `p` is `a` or `b`, and
takes the value `a²b²` at `x = p`. -/
noncomputable def twoDistPoly (p : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    EuclideanSpace ℝ (Fin 2) → ℝ :=
  fun x => (Erdos89.dist x p ^ 2 - a ^ 2) * (Erdos89.dist x p ^ 2 - b ^ 2)

/-- The ten monomial functions spanning the space every `twoDistPoly`
lives in: with `Q = x₀² + x₁²`, they are
`Q², Q·x₀, Q·x₁, Q, x₀², x₀·x₁, x₁², x₀, x₁, 1`. -/
noncomputable def twoDistBasis : Fin 10 → (EuclideanSpace ℝ (Fin 2) → ℝ) :=
  ![fun x => (x 0 ^ 2 + x 1 ^ 2) ^ 2,
    fun x => (x 0 ^ 2 + x 1 ^ 2) * x 0,
    fun x => (x 0 ^ 2 + x 1 ^ 2) * x 1,
    fun x => x 0 ^ 2 + x 1 ^ 2,
    fun x => x 0 ^ 2,
    fun x => x 0 * x 1,
    fun x => x 1 ^ 2,
    fun x => x 0,
    fun x => x 1,
    fun _ => 1]

/-- The coefficients expressing `twoDistPoly p a b` over `twoDistBasis`
(with `C = p₀² + p₁²`, `u = C − a²`, `v = C − b²`). -/
noncomputable def twoDistCoeff (p : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    Fin 10 → ℝ :=
  ![1,
    -4 * p 0,
    -4 * p 1,
    (p 0 ^ 2 + p 1 ^ 2 - a ^ 2) + (p 0 ^ 2 + p 1 ^ 2 - b ^ 2),
    4 * p 0 ^ 2,
    8 * p 0 * p 1,
    4 * p 1 ^ 2,
    -2 * p 0 * ((p 0 ^ 2 + p 1 ^ 2 - a ^ 2) + (p 0 ^ 2 + p 1 ^ 2 - b ^ 2)),
    -2 * p 1 * ((p 0 ^ 2 + p 1 ^ 2 - a ^ 2) + (p 0 ^ 2 + p 1 ^ 2 - b ^ 2)),
    (p 0 ^ 2 + p 1 ^ 2 - a ^ 2) * (p 0 ^ 2 + p 1 ^ 2 - b ^ 2)]

/-- **Expansion.** Every `twoDistPoly` is the explicit linear combination of
the ten monomials — pure polynomial identity after the coordinate expansion
of the squared distance. -/
theorem twoDistPoly_eq_sum (p : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    twoDistPoly p a b = ∑ i, twoDistCoeff p a b i • twoDistBasis i := by
  funext x
  have hx : Erdos89.dist x p ^ 2 = (x 0 - p 0) ^ 2 + (x 1 - p 1) ^ 2 :=
    norm_sub_sq_coords x p
  simp only [twoDistPoly, hx, twoDistCoeff, twoDistBasis, Fin.sum_univ_succ,
    Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul]
  ring

/-- Membership: every `twoDistPoly` lies in the span of the ten monomials
(their range as a function on `Fin 10`). -/
theorem twoDistPoly_mem_span (p : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    twoDistPoly p a b ∈
      Submodule.span ℝ (Set.range twoDistBasis) := by
  rw [twoDistPoly_eq_sum]
  refine Submodule.sum_smul_mem _ _ fun i _ => Submodule.subset_span ?_
  exact Set.mem_range_self i

/-! ### Section 3. The card bound by diagonal evaluation -/

/-- **A planar two-distance set has at most 10 points.** If all pairwise
distances of `S` take one of two positive values `a, b`, then the family
`{twoDistPoly p a b : p ∈ S}` is linearly independent (evaluate a vanishing
combination at each point: off-diagonal terms vanish, the diagonal term is
`a²b² ≠ 0`) inside a 10-dimensional space. -/
theorem two_distance_card_le_ten (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      Erdos89.dist p q = a ∨ Erdos89.dist p q = b) :
    S.card ≤ 10 := by
  classical
  set V := Submodule.span ℝ (Set.range twoDistBasis) with hV
  haveI : Module.Finite ℝ V :=
    Module.Finite.span_of_finite ℝ (Set.finite_range twoDistBasis)
  -- linear independence of the raw function family
  have hindep : LinearIndependent ℝ
      (fun i : ↥S => twoDistPoly (↑i) a b) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hev := congrFun hc (↑j : EuclideanSpace ℝ (Fin 2))
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul] at hev
    rw [Finset.sum_eq_single j] at hev
    · -- diagonal: c j · a²b² = 0
      have hself : twoDistPoly (↑j) a b ↑j = a ^ 2 * b ^ 2 := by
        simp only [twoDistPoly, Erdos89.dist, sub_self, norm_zero]
        ring
      rw [hself] at hev
      have hne : a ^ 2 * b ^ 2 ≠ 0 := by positivity
      exact (mul_eq_zero.mp hev).resolve_right hne
    · -- off-diagonal: F_i vanishes at x_j
      intro i _ hij
      have hne : (↑j : EuclideanSpace ℝ (Fin 2)) ≠ ↑i :=
        fun hEq => hij (Subtype.ext hEq.symm)
      rcases h ↑j j.2 ↑i i.2 hne with hd | hd
      · simp [twoDistPoly, hd]
      · simp [twoDistPoly, hd]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  -- push the family into the span and count
  have hindepV : LinearIndependent ℝ
      (fun i : ↥S => (⟨twoDistPoly (↑i) a b, twoDistPoly_mem_span _ a b⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hindep
  have hcard : Fintype.card ↥S ≤ Module.finrank ℝ V :=
    hindepV.fintype_card_le_finrank
  have hrank : Module.finrank ℝ V ≤ 10 := by
    have h1 : (Set.range twoDistBasis).finrank ℝ ≤ Fintype.card (Fin 10) :=
      finrank_range_le_card twoDistBasis
    rw [Fintype.card_fin] at h1
    exact h1
  have := hcard.trans hrank
  simpa [Fintype.card_coe] using this

/-- The same bound against the gallery's distance-count: a planar set
determining at most two distinct distances has at most 10 points. -/
theorem card_le_ten_of_numDistinctDistances_le_two
    (S : Finset (EuclideanSpace ℝ (Fin 2)))
    (h2 : numDistinctDistances S ≤ 2) : S.card ≤ 10 := by
  classical
  by_cases hsmall : S.card ≤ 10
  · exact hsmall
  rw [not_le] at hsmall
  exfalso
  have h1 : 1 ≤ numDistinctDistances S :=
    one_le_numDistinctDistances_of_two_le_card S (by omega)
  -- every off-diagonal pair's distance lies in `distinctDistances S`
  have hmemD : ∀ p ∈ S, ∀ q ∈ S, p ≠ q →
      Erdos89.dist p q ∈ distinctDistances S := by
    intro p hp q hq hpq
    rw [distinctDistances_eq_image, Finset.mem_image]
    exact ⟨(p, q), Finset.mem_offDiag.mpr ⟨hp, hq, hpq⟩, rfl⟩
  -- elements of `distinctDistances S` are positive
  have hpos : ∀ r ∈ distinctDistances S, 0 < r := by
    intro r hr
    unfold distinctDistances at hr
    exact (Finset.mem_filter.mp hr).2
  unfold numDistinctDistances at h1 h2
  rcases Nat.lt_or_ge (distinctDistances S).card 2 with hlt | hge
  · -- exactly one distance value
    obtain ⟨r, hD⟩ := Finset.card_eq_one.mp
      (show (distinctDistances S).card = 1 by omega)
    have hrmem : r ∈ distinctDistances S := by rw [hD]; exact Finset.mem_singleton_self r
    have hrpos := hpos r hrmem
    have hbound := two_distance_card_le_ten S r r hrpos hrpos
      (fun p hp q hq hpq => by
        have := hmemD p hp q hq hpq
        rw [hD, Finset.mem_singleton] at this
        exact Or.inl this)
    omega
  · -- exactly two distance values
    obtain ⟨r, s, _hrs, hD⟩ := Finset.card_eq_two.mp (le_antisymm h2 hge)
    have hrmem : r ∈ distinctDistances S := by rw [hD]; simp
    have hsmem : s ∈ distinctDistances S := by rw [hD]; simp
    have hbound := two_distance_card_le_ten S r s (hpos r hrmem) (hpos s hsmem)
      (fun p hp q hq hpq => by
        have := hmemD p hp q hq hpq
        rw [hD, Finset.mem_insert, Finset.mem_singleton] at this
        exact this)
    omega

/-! ### Section 4. The first `≥ 3` lower bound for Erdős's function -/

/-- Eleven or more planar points always determine at least three distinct
distances. -/
theorem three_le_numDistinctDistances_of_card
    (S : Finset (EuclideanSpace ℝ (Fin 2))) (h : 11 ≤ S.card) :
    3 ≤ numDistinctDistances S := by
  by_contra hcon
  rw [not_le] at hcon
  have := card_le_ten_of_numDistinctDistances_le_two S (by omega)
  omega

/-- **`g(n) ≥ 3` for `n ≥ 11`** — the first lower bound beyond the
`no_four_equidistant` floor `g(n) ≥ 2`. -/
theorem three_le_minDistinctDistances {n : ℕ} (hn : 11 ≤ n) :
    3 ≤ minDistinctDistances n := by
  obtain ⟨S₀, hS₀⟩ := exists_card_eq n
  have hne : {numDistinctDistances S |
      (S : Finset (EuclideanSpace ℝ (Fin 2))) (_ : S.card = n)}.Nonempty :=
    ⟨numDistinctDistances S₀, S₀, hS₀, rfl⟩
  obtain ⟨S, hScard, hSeq⟩ := Nat.sInf_mem hne
  show 3 ≤ minDistinctDistances n
  unfold minDistinctDistances
  rw [← hSeq]
  exact three_le_numDistinctDistances_of_card S (by rw [hScard]; exact hn)

/-- The two-sided bracket `3 ≤ g(n) ≤ ⌊n/2⌋` for `n ≥ 11`: the polynomial
lower bound meets the regular-`n`-gon ceiling. -/
theorem minDistinctDistances_bracket {n : ℕ} (hn : 11 ≤ n) :
    3 ≤ minDistinctDistances n ∧ minDistinctDistances n ≤ n / 2 :=
  ⟨three_le_minDistinctDistances hn, minDistinctDistances_le_half n⟩

/-- The new frontier value: `g(11) ∈ [3, 5]`. -/
theorem minDistinctDistances_eleven_mem_Icc :
    minDistinctDistances 11 ∈ Set.Icc 3 5 :=
  ⟨three_le_minDistinctDistances (by norm_num),
    by simpa using minDistinctDistances_le_half 11⟩

end Erdos89
