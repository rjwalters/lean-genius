/-
# Pell Equation OQ-01-OQ-04-OQ-02-OQ-01: the fundamental regulator is the minimal
  positive regulator, and it measures subgroup index

The parent `pell-equation-oq-01-oq-04-oq-02` (`PellEquationOQ01OQ04OQ02`) turned the
linear scaling law `R(aⁿ) = n · R(a)` of the Pell regulator into a *faithfulness /
order* statement: for `‖a‖ > 1` the map `n ↦ aⁿ` is injective and `a` has infinite
order, so `⟨a⟩ ≅ (ℤ, <)` as an ordered group.

This file pins down the **arithmetic** of the regulator against Mathlib's fundamental
solution `Pell.IsFundamental`. Write `R₀ = R(a₁)` for the regulator of a fundamental
solution `a₁`. We prove three things.

* **Positivity** (`pellRegulator_fundamental_pos`): a fundamental solution has
  `‖a₁‖ > 1`, hence `R₀ > 0`. The fundamental solution sits strictly to the right of
  the identity on the regulator ruler.

* **Quantization** (`exists_regulator_eq_zsmul`): *every* solution `b` has regulator an
  integer multiple of `R₀`, `R(b) = n · R₀`. This is exactly the structure theorem
  `b = ±a₁ⁿ` (Mathlib `IsFundamental.eq_zpow_or_neg_zpow`) read through the regulator,
  using that `R` is invariant under negation (`pellRegulator_neg`, since
  `log(-t) = log t`). The regulator spectrum is the lattice `R₀ · ℤ`.

* **Minimality** (`pellRegulator_fundamental_le`): `R₀` is the *least positive*
  regulator. Any solution with `R(b) > 0` has `R(b) ≥ R₀`, because `R(b) = n · R₀` with
  `R₀ > 0` forces `n ≥ 1`.

Combining quantization with the group structure, the **index** of the cyclic subgroup
`⟨a₁ᵏ⟩` inside `⟨a₁⟩` is exactly `k`, and this equals the regulator ratio:

* `relindex_zpowers_pow` : `[⟨a₁⟩ : ⟨a₁ᵏ⟩] = k`, obtained by transporting the index
  computation across the injective power homomorphism `zpowersHom : ℤ →* ⟨a₁⟩`
  (`Subgroup.relIndex_map_map_of_injective`) to `Int.index_zmultiples`.
* `relindex_eq_regulator_ratio` : `[⟨a₁⟩ : ⟨a₁ᵏ⟩] = R(a₁ᵏ) / R₀`.

The new mathematical content is the bridge between the *real-analytic* regulator
(a length on the line `ℝ`) and the *combinatorial* subgroup index (a count): the
regulator is the unique normalization for which `R₀` is the minimal positive value and
`R(b)/R₀` counts the index of `⟨b⟩`.

`0` axioms.
-/
import Mathlib
import Proofs.PellEquationOQ01OQ04OQ02

namespace PellEquationOQ01OQ04OQ02OQ01

open Pell PellEquationOQ01OQ04OQ02

variable {d : ℤ}

-- ============================================================
-- SECTION I: the fundamental solution has norm > 1, hence R₀ > 0
-- ============================================================

/-- **A fundamental solution lies strictly beyond `1`.** Mathlib's `IsFundamental`
predicate bundles `1 < a.x` and `0 < a.y`; since `√d ≥ 0`, the real embedding
`‖a‖ = x + y√d` exceeds `1` (indeed it is `≥ 2`). -/
theorem pellNorm_fundamental_gt_one {a : Solution₁ d} (h : IsFundamental a) :
    1 < pellNorm d a.x a.y := by
  have hx2 : (2 : ℤ) ≤ a.x := by have := h.1; omega
  have hx : (2 : ℝ) ≤ (a.x : ℝ) := by exact_mod_cast hx2
  have hy : (0 : ℝ) ≤ (a.y : ℝ) := by exact_mod_cast h.2.1.le
  have hprod : (0 : ℝ) ≤ (a.y : ℝ) * Real.sqrt (d : ℝ) :=
    mul_nonneg hy (Real.sqrt_nonneg _)
  unfold pellNorm
  linarith

/-- **The fundamental regulator is positive:** `R₀ = R(a₁) > 0`. -/
theorem pellRegulator_fundamental_pos {a : Solution₁ d} (h : IsFundamental a) :
    0 < pellRegulator d a :=
  pellRegulator_pos d a (pellNorm_fundamental_gt_one h)

-- ============================================================
-- SECTION II: the regulator is invariant under negation
-- ============================================================

/-- **The regulator ignores the sign `±1`:** `R(-b) = R(b)`. The norm of `-b` is the
negative of the norm of `b`, and `Real.log (-t) = Real.log t`. This is what lets the
`±a₁ⁿ` structure theorem collapse to a single integer multiple of `R₀`. -/
theorem pellRegulator_neg (d : ℤ) (b : Solution₁ d) :
    pellRegulator d (-b) = pellRegulator d b := by
  have hx : ((-b).x : ℝ) = -(b.x : ℝ) := by rw [Solution₁.x_neg]; push_cast; ring
  have hy : ((-b).y : ℝ) = -(b.y : ℝ) := by rw [Solution₁.y_neg]; push_cast; ring
  unfold pellRegulator pellNorm
  rw [hx, hy,
    show -(b.x : ℝ) + -(b.y : ℝ) * Real.sqrt (d : ℝ)
        = -((b.x : ℝ) + (b.y : ℝ) * Real.sqrt (d : ℝ)) from by ring,
    Real.log_neg_eq_log]

-- ============================================================
-- SECTION III: quantization and minimality of the regulator
-- ============================================================

/-- **Quantization of the regulator spectrum.** For a fundamental solution `a₁`, every
solution `b` has `R(b) = n · R₀` for some `n : ℤ`. Mathlib's
`IsFundamental.eq_zpow_or_neg_zpow` writes `b = ±a₁ⁿ`; the regulator of `a₁ⁿ` is
`n · R₀` (parent `pellRegulator_zpow`) and negation does not change it
(`pellRegulator_neg`). Hence the spectrum of the regulator is the lattice `R₀ · ℤ`. -/
theorem exists_regulator_eq_zsmul {a₁ : Solution₁ d} (h : IsFundamental a₁)
    (b : Solution₁ d) :
    ∃ n : ℤ, pellRegulator d b = (n : ℝ) * pellRegulator d a₁ := by
  obtain ⟨n, hn | hn⟩ := h.eq_zpow_or_neg_zpow b
  · exact ⟨n, by rw [hn, pellRegulator_zpow d h.d_pos.le]⟩
  · exact ⟨n, by rw [hn, pellRegulator_neg, pellRegulator_zpow d h.d_pos.le]⟩

/-- **Minimality: `R₀` is the least positive regulator.** If a solution `b` has
positive regulator, then `R(b) ≥ R₀`. Indeed `R(b) = n · R₀` with `R₀ > 0`, so
`R(b) > 0` forces `n ≥ 1` and `R(b) = n · R₀ ≥ R₀`. -/
theorem pellRegulator_fundamental_le {a₁ : Solution₁ d} (h : IsFundamental a₁)
    {b : Solution₁ d} (hb : 0 < pellRegulator d b) :
    pellRegulator d a₁ ≤ pellRegulator d b := by
  obtain ⟨n, hn⟩ := exists_regulator_eq_zsmul h b
  have hR0 : 0 < pellRegulator d a₁ := pellRegulator_fundamental_pos h
  rw [hn] at hb ⊢
  have hnpos : (0 : ℤ) < n := by
    by_contra hc
    push_neg at hc
    have : (n : ℝ) ≤ 0 := by exact_mod_cast hc
    nlinarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
  nlinarith

-- ============================================================
-- SECTION IV: the regulator counts subgroup index
-- ============================================================

/-- **Index helper.** In `Multiplicative ℤ` the cyclic subgroup generated by
`Multiplicative.ofAdd k` has index `k.natAbs`. This is `Int.index_zmultiples`
transported across the order isomorphism `AddSubgroup.toSubgroup`. -/
theorem index_zpowers_ofAdd (k : ℤ) :
    (Subgroup.zpowers (Multiplicative.ofAdd k)).index = k.natAbs := by
  have heq : Subgroup.zpowers (Multiplicative.ofAdd k)
      = (AddSubgroup.zmultiples k).toSubgroup := by
    ext g
    rw [Subgroup.mem_zpowers_iff, Multiplicative.mem_toSubgroup,
      AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by rw [← ofAdd_zsmul, toAdd_ofAdd]⟩
    · rintro ⟨m, hm⟩
      exact ⟨m, by rw [← ofAdd_zsmul, hm, ofAdd_toAdd]⟩
  rw [heq, AddSubgroup.index_toSubgroup, Int.index_zmultiples]

/-- **The index of `⟨a₁ᵏ⟩` in `⟨a₁⟩` is `k`.** The power homomorphism
`zpowersHom : Multiplicative ℤ →* Solution₁ d`, `n ↦ a₁ⁿ`, is injective because `a₁`
has infinite order. It carries `⊤` to `⟨a₁⟩` and `⟨ofAdd k⟩` to `⟨a₁ᵏ⟩`, so by
`Subgroup.relIndex_map_map_of_injective` the relative index equals
`[⊤ : ⟨ofAdd k⟩]⁻¹ = (⟨ofAdd k⟩).index = k`. -/
theorem relindex_zpowers_pow {a₁ : Solution₁ d} (h : IsFundamental a₁) (k : ℕ) :
    (Subgroup.zpowers (a₁ ^ k)).relIndex (Subgroup.zpowers a₁) = k := by
  set f : Multiplicative ℤ →* Solution₁ d := zpowersHom (Solution₁ d) a₁ with hf
  have hnotfin : ¬ IsOfFinOrder a₁ :=
    not_isOfFinOrder d h.d_pos.le a₁ (pellNorm_fundamental_gt_one h)
  have hinj : Function.Injective f := by
    rw [hf]
    intro x y hxy
    simp only [zpowersHom_apply] at hxy
    have hh : x.toAdd = y.toAdd := (injective_zpow_iff_not_isOfFinOrder.mpr hnotfin) hxy
    exact Multiplicative.toAdd.injective hh
  have h1 : Subgroup.zpowers a₁ = Subgroup.map f ⊤ := by
    rw [← MonoidHom.range_eq_map, hf, Subgroup.range_zpowersHom]
  have h2 : Subgroup.zpowers (a₁ ^ k)
      = Subgroup.map f (Subgroup.zpowers (Multiplicative.ofAdd (k : ℤ))) := by
    rw [MonoidHom.map_zpowers]
    congr 1
    rw [hf, zpowersHom_apply, toAdd_ofAdd, zpow_natCast]
  rw [h1, h2, Subgroup.relIndex_map_map_of_injective _ _ hinj,
    Subgroup.relIndex_top_right, index_zpowers_ofAdd, Int.natAbs_natCast]

/-- **The subgroup index equals the regulator ratio.** Combining
`relindex_zpowers_pow` with the linear scaling `R(a₁ᵏ) = k · R₀`:
`[⟨a₁⟩ : ⟨a₁ᵏ⟩] = k = R(a₁ᵏ) / R₀`. The integer-valued combinatorial index is read
off the real-analytic regulator. -/
theorem relindex_eq_regulator_ratio {a₁ : Solution₁ d} (h : IsFundamental a₁) (k : ℕ) :
    (((Subgroup.zpowers (a₁ ^ k)).relIndex (Subgroup.zpowers a₁) : ℕ) : ℝ)
      = pellRegulator d (a₁ ^ k) / pellRegulator d a₁ := by
  have hR0 : pellRegulator d a₁ ≠ 0 := (pellRegulator_fundamental_pos h).ne'
  have hreg : pellRegulator d (a₁ ^ k) = (k : ℝ) * pellRegulator d a₁ := by
    rw [← zpow_natCast a₁ k, pellRegulator_zpow d h.d_pos.le]
    push_cast; ring
  rw [relindex_zpowers_pow h k, hreg]
  field_simp

end PellEquationOQ01OQ04OQ02OQ01
