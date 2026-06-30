/-
# The Real Roots of the Chebyshev Polynomials Tₙ

Building on the degree/leading-coefficient pair `natDegree (T ℤ n) = n`,
`leadingCoeff (T ℤ n) = 2^(n-1)` (parent entry `de-moivre-oq-02-oq-03-oq-02`),
this file answers that entry's second open question: it locates *all* the real
roots of the first-kind Chebyshev polynomial `Tₙ` and shows there are exactly
`n` of them, all simple, all in `[-1, 1]`.

For `n ≥ 1` the **Chebyshev nodes**
`xₖ = cos((2k+1)·π / (2n))`,  `k = 0, …, n-1`
are `n` distinct numbers in `(-1, 1)`, each a root of `Tₙ`; and because `Tₙ`
has degree exactly `n` (re-derived here over `ℝ`), these are *all* of its roots.
Concretely we prove the multiset identity

* `(T ℝ n).roots = (Finset.image (fun k : Fin n => cos ((2k+1)π/(2n))) univ).val`,

from which we read off: `Multiset.card (T ℝ n).roots = n`, the roots are
`Nodup` (all simple), and every root lies in `[-1, 1]`.  This is the first
concrete step toward Mathlib's open "compute zeroes and extrema" Chebyshev TODO
and the location half of the classical minimax theorem.

## Strategy

* **Degree over any domain.** The same two-step induction as the parent, but
  stated for an arbitrary integral domain `R` with `(2 : R) ≠ 0`, strictly
  generalizing the parent's `ℤ`-only statement; instantiating at `ℝ` gives
  `natDegree (T ℝ n) = n` and `T ℝ n ≠ 0` for `n ≥ 1`.
* **The nodes are roots.** Mathlib's `T_real_cos : (T ℝ n).eval (cos θ) = cos (n·θ)`
  turns `eval (Tₙ) (cos θ)` into `cos (n·θ)`; at `θ = (2k+1)π/(2n)` we get
  `cos((2k+1)π/2) = 0`.
* **The nodes are distinct.** The angles `(2k+1)π/(2n)` lie in `[0, π]` and are
  injective in `k`; since `cos` is injective on `[0, π]` (`injOn_cos`), the
  cosines are distinct.
* **They are all the roots.** `n` distinct roots of a degree-`n` polynomial over
  a field exhaust the root multiset (`roots_eq_of_natDegree_le_card_of_ne_zero`).

No axioms beyond Lean/Mathlib's foundations; `0` sorries.
-/
import Mathlib

open Polynomial Polynomial.Chebyshev Real Set

namespace DeMoivreOQ02OQ03OQ02OQ02

/-! ## Degree and leading coefficient over an arbitrary integral domain -/

/-- **Degree and leading coefficient of `Tₙ` over any integral domain.**  When
`(2 : R) ≠ 0`, the `n`-th first-kind Chebyshev polynomial over `R` has degree `n`
and leading coefficient `2 ^ (n-1)`.  This strictly generalizes the parent entry's
`ℤ`-only statement (the proof is identical: a single two-step induction). -/
theorem T_natDegree_leadingCoeff {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (n : ℕ) :
    (T R (n : ℤ)).natDegree = n ∧ (T R (n : ℤ)).leadingCoeff = 2 ^ (n - 1) := by
  have hC2 : (C (2 : R)) = (2 : R[X]) := map_ofNat (C : R →+* R[X]) 2
  have hCX_deg : (2 * X : R[X]).natDegree = 1 := by
    rw [← hC2, natDegree_C_mul h2, natDegree_X]
  have hCX_lead : (2 * X : R[X]).leadingCoeff = 2 := by
    rw [← hC2, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X, mul_one]
  have hCX_ne : (2 * X : R[X]) ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [hCX_deg, natDegree_zero] at this
    exact one_ne_zero this
  induction n using Nat.twoStepInduction with
  | zero => constructor <;> simp
  | one => constructor <;> simp [T_one]
  | more n ih0 ih1 =>
      obtain ⟨hd0, hl0⟩ := ih0
      obtain ⟨hd1, hl1⟩ := ih1
      have hrec : T R ((n + 2 : ℕ) : ℤ)
          = 2 * X * T R ((n + 1 : ℕ) : ℤ) - T R ((n : ℕ) : ℤ) := by
        have h := T_add_two R (n : ℤ)
        push_cast
        push_cast at h
        linear_combination h
      have hTn1_ne : T R ((n + 1 : ℕ) : ℤ) ≠ 0 := by
        intro h0
        rw [h0, leadingCoeff_zero] at hl1
        have : (2 : R) ^ (n + 1 - 1) ≠ 0 := pow_ne_zero _ h2
        exact this hl1.symm
      have hdA : (2 * X * T R ((n + 1 : ℕ) : ℤ)).natDegree = n + 2 := by
        rw [natDegree_mul hCX_ne hTn1_ne, hCX_deg, hd1]; omega
      have hlA : (2 * X * T R ((n + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ (n + 1) := by
        rw [leadingCoeff_mul, hCX_lead, hl1]
        have : n + 1 - 1 = n := by omega
        rw [this]; ring
      have hdeg_lt : (T R ((n : ℕ) : ℤ)).natDegree
          < (2 * X * T R ((n + 1 : ℕ) : ℤ)).natDegree := by
        rw [hdA, hd0]; omega
      constructor
      · rw [hrec, natDegree_sub_eq_left_of_natDegree_lt hdeg_lt, hdA]
      · rw [hrec]
        have hsub : (2 * X * T R ((n + 1 : ℕ) : ℤ) - T R ((n : ℕ) : ℤ)).leadingCoeff
            = (2 * X * T R ((n + 1 : ℕ) : ℤ)).leadingCoeff := by
          rw [sub_eq_add_neg, leadingCoeff_add_of_degree_lt']
          rw [degree_neg]
          exact degree_lt_degree hdeg_lt
        rw [hsub, hlA, show n + 2 - 1 = n + 1 from by omega]

/-- **Degree of `Tₙ` over `ℝ`.** `natDegree (T ℝ n) = n`. -/
theorem T_real_natDegree (n : ℕ) : (T ℝ (n : ℤ)).natDegree = n :=
  (T_natDegree_leadingCoeff (by norm_num : (2 : ℝ) ≠ 0) n).1

/-- For `n ≥ 1`, `Tₙ` is a nonzero polynomial over `ℝ` (it has degree `n ≥ 1`). -/
theorem T_real_ne_zero {n : ℕ} (hn : 1 ≤ n) : T ℝ (n : ℤ) ≠ 0 := by
  intro h
  have hd := T_real_natDegree n
  rw [h, natDegree_zero] at hd
  omega

/-! ## The Chebyshev nodes are roots -/

/-- **The Chebyshev nodes are roots of `Tₙ`.**  For `n ≥ 1` and any `k`, the
node `cos((2k+1)π/(2n))` is a root of `Tₙ`, because
`eval (Tₙ) (cos θ) = cos (n·θ)` and `cos((2k+1)π/2) = 0`. -/
theorem T_eval_node_eq_zero {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    (T ℝ (n : ℤ)).eval (cos ((2 * (k : ℝ) + 1) * π / (2 * n))) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [T_real_cos, Real.cos_eq_zero_iff]
  refine ⟨(k : ℤ), ?_⟩
  push_cast
  field_simp
  try ring

/-! ## The Chebyshev nodes are distinct -/

/-- **The Chebyshev nodes are distinct.**  For `n ≥ 1` the map
`k ↦ cos((2k+1)π/(2n))` is injective on `Fin n`: the angles lie in `[0, π]`,
are injective in `k`, and `cos` is injective on `[0, π]`. -/
theorem node_injective {n : ℕ} (hn : 1 ≤ n) :
    Function.Injective
      (fun k : Fin n => cos ((2 * (k.val : ℝ) + 1) * π / (2 * n))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ : (0 : ℝ) < π := pi_pos
  have h2n : (0 : ℝ) < 2 * n := by positivity
  -- each angle lies in `[0, π]`
  have mem : ∀ k : Fin n,
      (2 * (k.val : ℝ) + 1) * π / (2 * n) ∈ Set.Icc (0 : ℝ) π := by
    intro k
    have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt k.isLt
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ h2n]
    have h1 : (2 * (k.val : ℝ) + 1) ≤ 2 * n := by linarith
    calc (2 * (k.val : ℝ) + 1) * π ≤ (2 * n) * π :=
            mul_le_mul_of_nonneg_right h1 hπ.le
      _ = π * (2 * n) := by ring
  intro i j hij
  have hg : (2 * (i.val : ℝ) + 1) * π / (2 * n)
      = (2 * (j.val : ℝ) + 1) * π / (2 * n) :=
    injOn_cos (mem i) (mem j) hij
  -- `field_simp` clears the common positive factor `π / (2n)`, leaving `2i+1 = 2j+1`
  have hπ0 : π ≠ 0 := pi_ne_zero
  have h2n' : (2 * (n : ℝ)) ≠ 0 := ne_of_gt h2n
  field_simp at hg
  have : (i.val : ℝ) = (j.val : ℝ) := by linarith
  exact Fin.ext (by exact_mod_cast this)

/-! ## Main theorem: the complete root set -/

/-- **The real roots of `Tₙ`.**  For `n ≥ 1`, the root multiset of the first-kind
Chebyshev polynomial `Tₙ` over `ℝ` is exactly the set of `n` Chebyshev nodes
`cos((2k+1)π/(2n))`, `k = 0, …, n-1`.  (Equality of `(T ℝ n).roots` with the
underlying multiset of the image `Finset`.) -/
theorem T_roots_eq {n : ℕ} (hn : 1 ≤ n) :
    (T ℝ (n : ℤ)).roots
      = (Finset.image (fun k : Fin n => cos ((2 * (k.val : ℝ) + 1) * π / (2 * n)))
          Finset.univ).val := by
  refine roots_eq_of_natDegree_le_card_of_ne_zero ?_ ?_ (T_real_ne_zero hn)
  · intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨k, rfl⟩ := hx
    exact T_eval_node_eq_zero hn k.val
  · rw [T_real_natDegree,
      Finset.card_image_of_injective _ (node_injective hn),
      Finset.card_univ, Fintype.card_fin]

/-- **`Tₙ` has exactly `n` real roots (with multiplicity).** -/
theorem T_card_roots {n : ℕ} (hn : 1 ≤ n) :
    Multiset.card (T ℝ (n : ℤ)).roots = n := by
  rw [T_roots_eq hn]
  show (Finset.image (fun k : Fin n => cos ((2 * (k.val : ℝ) + 1) * π / (2 * n)))
        Finset.univ).card = n
  rw [Finset.card_image_of_injective _ (node_injective hn),
    Finset.card_univ, Fintype.card_fin]

/-- **All roots of `Tₙ` are simple.** The root multiset has no repeats. -/
theorem T_roots_nodup {n : ℕ} (hn : 1 ≤ n) : (T ℝ (n : ℤ)).roots.Nodup := by
  rw [T_roots_eq hn]
  exact (Finset.image _ _).nodup

/-- **Every real root of `Tₙ` lies in `[-1, 1]`.**  Each root is a cosine. -/
theorem T_roots_mem_Icc {n : ℕ} (hn : 1 ≤ n) :
    ∀ x ∈ (T ℝ (n : ℤ)).roots, x ∈ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  rw [T_roots_eq hn, ← Finset.mem_def, Finset.mem_image] at hx
  obtain ⟨k, -, rfl⟩ := hx
  exact ⟨neg_one_le_cos _, cos_le_one _⟩

end DeMoivreOQ02OQ03OQ02OQ02
