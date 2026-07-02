import Mathlib

/-
# F₂₀ as an explicit permutation group on 5 points

This file gives the concrete permutation representation of the Frobenius group
F₂₀ = C₅ ⋊ C₄ inside the symmetric group S₅ = `Equiv.Perm (Fin 5)`,
extending `inverse-galois-f20` (which computes `|Gal(X⁵-2/ℚ)| = 20` abstractly).

The Galois group of `X⁵-2` acts on its five roots `α·ζ₅ᵏ`.  Labelling the roots
by `Fin 5` via the exponent `k`, the group is realised as the affine group
`AGL(1, 𝔽₅) = {x ↦ a·x + b : a ∈ 𝔽₅ˣ, b ∈ 𝔽₅}` acting on `𝔽₅ = Fin 5`:

* `σ : x ↦ x + 1`  — the translation, a **5-cycle** `(0 1 2 3 4)`
  (multiplication of the roots by `ζ₅`);
* `τ : x ↦ 2·x`    — multiplication by the primitive root `2 mod 5`,
  a **4-cycle** `(1 2 4 3)`.

Conjugation gives the defining **normalizing relation** `τ σ τ⁻¹ = σ²`, so
`⟨σ⟩ ≅ C₅` is normal and `⟨τ⟩ ≅ C₄` acts on it by the primitive automorphism
`x ↦ 2x`.  We prove:

* `orderOf σ = 5` and `orderOf τ = 4`;
* `τ * σ * τ⁻¹ = σ ^ 2` (the semidirect-product relation);
* the subgroup `F20 = ⟨σ, τ⟩` has `Nat.card = 20` **exactly**
  (lower bound from the coprime element orders 4, 5; upper bound from the
  semidirect commutation `τ^n σ^m = σ^(2ⁿ m) τ^n`);
* the action of `F20` on the five roots is transitive.

Everything is verified with `decide` on the explicit permutations plus an
elementary commutation calculation — no axioms, no `sorry`.
-/

namespace InverseGaloisF20OQ02

open Equiv (Perm)

/-- The translation `x ↦ x + 1` on `Fin 5`, a 5-cycle `(0 1 2 3 4)`.
    (Multiplication of the roots of `X⁵-2` by the primitive 5th root of unity.) -/
def σ : Perm (Fin 5) := ⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide, by decide⟩

/-- Multiplication by `2` on `Fin 5 = 𝔽₅`, a 4-cycle `(1 2 4 3)`.
    (The primitive Frobenius automorphism of the 5th cyclotomic field.) -/
def τ : Perm (Fin 5) := ⟨![0, 2, 4, 1, 3], ![0, 3, 1, 4, 2], by decide, by decide⟩

/-! ### Elementary relations, verified by `decide` on the explicit permutations. -/

theorem sigma_pow_five : σ ^ 5 = 1 := by unfold σ; decide

theorem sigma_ne_one : σ ≠ 1 := by unfold σ; decide

theorem tau_sq_ne_one : τ ^ (2 ^ 1) ≠ 1 := by unfold τ; decide

theorem tau_pow_four : τ ^ (2 ^ (1 + 1)) = 1 := by unfold τ; decide

/-- The defining relation of the Frobenius group `F₂₀ = C₅ ⋊ C₄`:
    conjugating the 5-cycle by the 4-cycle squares it (`2` is the multiplier). -/
theorem rel : τ * σ * τ⁻¹ = σ ^ 2 := by unfold σ τ; decide

/-! ### Orders of the two generators. -/

/-- `σ` is a 5-cycle: it has order `5`. -/
theorem orderOf_sigma : orderOf σ = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime sigma_pow_five sigma_ne_one

/-- `τ` is a 4-cycle: it has order `4 = 2²`. -/
theorem orderOf_tau : orderOf τ = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have h := orderOf_eq_prime_pow (x := τ) (p := 2) (n := 1) tau_sq_ne_one tau_pow_four
  simpa using h

/-! ### The semidirect-product commutation law. -/

/-- Base commutation: `τ σ = σ² τ` (equivalent form of the defining relation). -/
theorem tau_sigma_pow (m : ℕ) : τ * σ ^ m = σ ^ (2 * m) * τ := by
  have hbase : τ * σ = σ ^ 2 * τ := by
    calc τ * σ = (τ * σ * τ⁻¹) * τ := by group
      _ = σ ^ 2 * τ := by rw [rel]
  induction m with
  | zero => simp
  | succ k ih =>
    calc τ * σ ^ (k + 1)
        = (τ * σ ^ k) * σ := by rw [pow_succ, ← mul_assoc]
      _ = σ ^ (2 * k) * τ * σ := by rw [ih]
      _ = σ ^ (2 * k) * (τ * σ) := by rw [mul_assoc]
      _ = σ ^ (2 * k) * (σ ^ 2 * τ) := by rw [hbase]
      _ = σ ^ (2 * k) * σ ^ 2 * τ := by rw [mul_assoc]
      _ = σ ^ (2 * k + 2) * τ := by rw [← pow_add]
      _ = σ ^ (2 * (k + 1)) * τ := by rw [show 2 * (k + 1) = 2 * k + 2 from by ring]

/-- Full commutation: moving `τⁿ` past `σᵐ` multiplies the exponent by `2ⁿ`.
    This is exactly the multiplication rule of the semidirect product. -/
theorem tau_pow_sigma_pow (n m : ℕ) : τ ^ n * σ ^ m = σ ^ (2 ^ n * m) * τ ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc τ ^ (k + 1) * σ ^ m
        = τ * (τ ^ k * σ ^ m) := by rw [pow_succ', mul_assoc]
      _ = τ * (σ ^ (2 ^ k * m) * τ ^ k) := by rw [ih]
      _ = (τ * σ ^ (2 ^ k * m)) * τ ^ k := by rw [← mul_assoc]
      _ = (σ ^ (2 * (2 ^ k * m)) * τ) * τ ^ k := by rw [tau_sigma_pow]
      _ = σ ^ (2 * (2 ^ k * m)) * (τ * τ ^ k) := by rw [mul_assoc]
      _ = σ ^ (2 ^ (k + 1) * m) * τ ^ (k + 1) := by
            rw [← pow_succ', show 2 * (2 ^ k * m) = 2 ^ (k + 1) * m from by rw [pow_succ]; ring]

/-! ### The group `F20 = ⟨σ, τ⟩` and its order. -/

/-- `F₂₀` realised as the explicit set of affine maps `σⁱ τʲ` on the five roots. -/
def F20 : Subgroup (Perm (Fin 5)) where
  carrier := {g | ∃ i j : ℕ, g = σ ^ i * τ ^ j}
  one_mem' := ⟨0, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    refine ⟨i + 2 ^ j * k, j + l, ?_⟩
    have h : σ ^ i * τ ^ j * (σ ^ k * τ ^ l) = σ ^ i * (τ ^ j * σ ^ k) * τ ^ l := by group
    rw [h, tau_pow_sigma_pow, pow_add, pow_add]
    group
  inv_mem' := by
    rintro a ⟨i, j, rfl⟩
    refine ⟨2 ^ (3 * j) * (4 * i), 3 * j, ?_⟩
    have hσinv : σ⁻¹ = σ ^ 4 :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact sigma_pow_five)
    have hτinv : τ⁻¹ = τ ^ 3 :=
      inv_eq_of_mul_eq_one_right (by
        rw [← pow_succ']; have := tau_pow_four; simpa using this)
    rw [mul_inv_rev, ← inv_pow, ← inv_pow, hτinv, hσinv, ← pow_mul, ← pow_mul,
        tau_pow_sigma_pow]

theorem sigma_mem : σ ∈ F20 := ⟨1, 0, by simp⟩

theorem tau_mem : τ ∈ F20 := ⟨0, 1, by simp⟩

/-- `F20` is precisely the subgroup generated by the 5-cycle and the 4-cycle. -/
theorem closure_eq : Subgroup.closure ({σ, τ} : Set (Perm (Fin 5))) = F20 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact sigma_mem
    · exact tau_mem
  · intro g hg
    obtain ⟨i, j, rfl⟩ := hg
    have hσc : σ ∈ Subgroup.closure ({σ, τ} : Set (Perm (Fin 5))) :=
      Subgroup.subset_closure (by simp)
    have hτc : τ ∈ Subgroup.closure ({σ, τ} : Set (Perm (Fin 5))) :=
      Subgroup.subset_closure (by simp)
    exact mul_mem (pow_mem hσc i) (pow_mem hτc j)

/-- **Main result.** The Frobenius group `F₂₀ = ⟨σ, τ⟩` acting on the five roots
    of `X⁵-2` has order exactly `20`. -/
theorem card_F20 : Nat.card F20 = 20 := by
  -- Upper bound: every element is `σⁱ τʲ` with `i < 5`, `j < 4`.
  have hle : Nat.card F20 ≤ 20 := by
    have hsurj : Function.Surjective
        (fun p : Fin 5 × Fin 4 =>
          (⟨σ ^ (p.1 : ℕ) * τ ^ (p.2 : ℕ), ⟨(p.1 : ℕ), (p.2 : ℕ), rfl⟩⟩ : F20)) := by
      rintro ⟨g, i, j, rfl⟩
      refine ⟨(⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 4, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      apply Subtype.ext
      have e1 : σ ^ (i % 5) = σ ^ i := by rw [← orderOf_sigma]; exact pow_mod_orderOf σ i
      have e2 : τ ^ (j % 4) = τ ^ j := by rw [← orderOf_tau]; exact pow_mod_orderOf τ j
      simp only [Fin.val_mk]
      rw [e1, e2]
    calc Nat.card F20 ≤ Nat.card (Fin 5 × Fin 4) := Nat.card_le_card_of_surjective _ hsurj
      _ = 20 := by rw [Nat.card_eq_fintype_card]; decide
  -- Lower bound: `5` and `4` are coprime element orders, so `20 ∣ |F20|`.
  have h5 : (5 : ℕ) ∣ Nat.card F20 := by
    have := Subgroup.orderOf_dvd_natCard F20 sigma_mem; rwa [orderOf_sigma] at this
  have h4 : (4 : ℕ) ∣ Nat.card F20 := by
    have := Subgroup.orderOf_dvd_natCard F20 tau_mem; rwa [orderOf_tau] at this
  have h20 : (20 : ℕ) ∣ Nat.card F20 := by
    have hco : Nat.Coprime 5 4 := by decide
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd hco h5 h4
    simpa using this
  exact le_antisymm hle (Nat.le_of_dvd Nat.card_pos h20)

/-- The order of the generated group equals `20`, phrased via `Subgroup.closure`. -/
theorem card_closure_eq_20 :
    Nat.card (Subgroup.closure ({σ, τ} : Set (Perm (Fin 5)))) = 20 := by
  rw [closure_eq]; exact card_F20

/-! ### Transitivity of the action on the five roots. -/

/-- The action of `F20` on the five roots is transitive: the translation `σ`
    already moves `0` to every label. -/
theorem acts_transitively : ∀ x : Fin 5, ∃ g ∈ F20, g 0 = x := by
  intro x
  refine ⟨σ ^ (x : ℕ), ⟨(x : ℕ), 0, by simp⟩, ?_⟩
  unfold σ
  fin_cases x <;> decide

end InverseGaloisF20OQ02
