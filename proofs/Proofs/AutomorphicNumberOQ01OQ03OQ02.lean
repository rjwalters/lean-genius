import Mathlib
import Proofs.AutomorphicNumberOQ01

/-
# Automorphic numbers OQ-01 → OQ-03 → OQ-02: convergence of the idempotent towers in ℤ₁₀

## What this proves

The parent `AutomorphicNumberOQ01OQ03` proves that the four `k`-digit automorphic
residues `n² ≡ n (mod 10ᵏ)` — the idempotents of `ZMod (10ᵏ)` — form coherent **towers**:
each `k`-digit automorphic number extends uniquely to a `(k+1)`-digit one
(`5 → 25 → 625 → 90625 → …`, `6 → 76 → 376 → 9376 → …`).  It remarks, but does not
formalize, that these towers "converge to the two non-trivial idempotents of the
`10`-adic integers `ℤ₁₀ ≅ ℤ₂ × ℤ₅`."  This file supplies that missing convergence layer.

We model the `10`-adic integers as `TenAdic := ℤ_[2] × ℤ_[5]` (legitimate since
`10 = 2·5` and, by CRT, `ZMod (10ᵏ) ≅ ZMod (2ᵏ) × ZMod (5ᵏ)`).

## Main results

* `TenAdic.idem_iff` — the idempotents of `ℤ₂ × ℤ₅` are **exactly four**:
  `(0,0), (1,0), (0,1), (1,1)`.  (`ℤ_[p]` is a domain, so each factor is `0` or `1`.)
* `e5`, `e6` — the two non-trivial idempotents `(1,0)`, `(0,1)`; they are an
  **orthogonal complementary pair**: `e5 + e6 = 1`, `e5 * e6 = 0`, both `≠ 0, 1`.
* `reductions_determine` — a `10`-adic integer is determined by its tower of
  reductions `toZModPow k`.  This is the **inverse-limit (uniqueness) form of
  convergence**: a coherent idempotent tower has at most one `10`-adic limit.
* `red10`, `red10_e5_idem`, `red10_e5_ne` — the `k`-digit reduction
  `ρₖ : ℤ₁₀ →+* ZMod (10ᵏ)` sends `e5` to a genuine **automorphic residue** (idempotent),
  and for `k ≥ 1` it is one of the *non-trivial* two.
* `tendsto_e5`, `tendsto_e6` — the **genuine metric convergence**: any integer sequence
  of `k`-digit automorphic numbers for the `5`-tower (resp. `6`-tower) converges, in the
  `10`-adic metric of `ℤ₂ × ℤ₅`, to `e5` (resp. `e6`).

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace AutomorphicNumberOQ01OQ03OQ02

open PadicInt Filter

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The `10`-adic integers, modelled as `ℤ₂ × ℤ₅` (legitimate since `10 = 2·5`). -/
abbrev TenAdic : Type := ℤ_[2] × ℤ_[5]

/-! ## Idempotents of `ℤ_[p]` and of `ℤ₁₀ = ℤ₂ × ℤ₅` -/

/-- In a `p`-adic integer ring (an integral domain), the only idempotents are `0` and `1`. -/
theorem padicInt_idem_eq_zero_or_one {p : ℕ} [Fact p.Prime] {e : ℤ_[p]} (h : e * e = e) :
    e = 0 ∨ e = 1 := by
  have hz : e * (e - 1) = 0 := by ring_nf; linear_combination h
  rcases mul_eq_zero.mp hz with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- **The idempotents of `ℤ₁₀ = ℤ₂ × ℤ₅` are exactly the four pairs `(0,0), (1,0),
(0,1), (1,1)`.**  Componentwise, an idempotent of a product is a pair of idempotents,
and each `p`-adic factor admits only `0` and `1`. -/
theorem TenAdic.idem_iff {e : TenAdic} :
    e * e = e ↔ e = (0, 0) ∨ e = (1, 0) ∨ e = (0, 1) ∨ e = (1, 1) := by
  constructor
  · intro h
    have h1 : e.1 * e.1 = e.1 := (Prod.ext_iff.mp h).1
    have h2 : e.2 * e.2 = e.2 := (Prod.ext_iff.mp h).2
    rcases padicInt_idem_eq_zero_or_one h1 with a | a <;>
      rcases padicInt_idem_eq_zero_or_one h2 with b | b
    · exact Or.inl (Prod.ext a b)
    · exact Or.inr (Or.inr (Or.inl (Prod.ext a b)))
    · exact Or.inr (Or.inl (Prod.ext a b))
    · exact Or.inr (Or.inr (Or.inr (Prod.ext a b)))
  · rintro (rfl | rfl | rfl | rfl) <;> ext <;> simp

/-! ## The two non-trivial idempotents (the automorphic towers' limits) -/

/-- The non-trivial idempotent `(1, 0)` — the `10`-adic limit of the `5`-tower
`5, 25, 625, 90625, …` (residues `≡ 1 (mod 2ᵏ)`, `≡ 0 (mod 5ᵏ)`). -/
noncomputable def e5 : TenAdic := (1, 0)

/-- The non-trivial idempotent `(0, 1)` — the `10`-adic limit of the `6`-tower
`6, 76, 376, 9376, …` (residues `≡ 0 (mod 2ᵏ)`, `≡ 1 (mod 5ᵏ)`). -/
noncomputable def e6 : TenAdic := (0, 1)

theorem e5_idem : e5 * e5 = e5 := by ext <;> simp [e5]
theorem e6_idem : e6 * e6 = e6 := by ext <;> simp [e6]

/-- The two non-trivial idempotents are **orthogonal and complementary**:
`e5 + e6 = 1` and `e5 * e6 = 0`. -/
theorem e5_add_e6 : e5 + e6 = 1 := by ext <;> simp [e5, e6]
theorem e5_mul_e6 : e5 * e6 = 0 := by ext <;> simp [e5, e6]

theorem e5_ne_zero : e5 ≠ 0 := by
  intro h; have h1 := congrArg Prod.fst h; simp [e5] at h1
theorem e5_ne_one : e5 ≠ 1 := by
  intro h; have h1 := congrArg Prod.snd h; simp [e5] at h1

/-! ## Inverse-limit convergence: reductions determine the limit -/

/-- **Uniqueness form of convergence.**  A `10`-adic integer `x = (x₂, x₅)` is completely
determined by its tower of reductions `toZModPow k` in each factor.  Hence a coherent
tower of `k`-digit residues has *at most one* `10`-adic limit: the idempotent towers
converge to a unique point of `ℤ₂ × ℤ₅`. -/
theorem reductions_determine {x y : TenAdic}
    (h2 : ∀ k, toZModPow k x.1 = toZModPow k y.1)
    (h5 : ∀ k, toZModPow k x.2 = toZModPow k y.2) : x = y :=
  Prod.ext (ext_of_toZModPow.mp h2) (ext_of_toZModPow.mp h5)

/-! ## Bridge to the `k`-digit automorphic residues in `ZMod (10ᵏ)` -/

theorem coprime_two_five_pow (k : ℕ) : Nat.Coprime (2 ^ k) (5 ^ k) := by
  have h : Nat.Coprime 2 5 := by decide
  exact Nat.Coprime.pow k k h

theorem ten_pow_eq (k : ℕ) : (10 : ℕ) ^ k = 2 ^ k * 5 ^ k := by
  rw [show (10 : ℕ) = 2 * 5 from by norm_num, mul_pow]

/-- CRT identification `ZMod (10ᵏ) ≃+* ZMod (2ᵏ) × ZMod (5ᵏ)`. -/
noncomputable def crt (k : ℕ) : ZMod (10 ^ k) ≃+* ZMod (2 ^ k) × ZMod (5 ^ k) :=
  (ZMod.ringEquivCongr (ten_pow_eq k)).trans (ZMod.chineseRemainder (coprime_two_five_pow k))

/-- The `k`-digit reduction of a `10`-adic integer into its two CRT components. -/
noncomputable def digit (k : ℕ) : TenAdic →+* ZMod (2 ^ k) × ZMod (5 ^ k) :=
  (toZModPow k).prodMap (toZModPow k)

/-- The `k`-digit reduction `ρₖ : ℤ₁₀ →+* ZMod (10ᵏ)`. -/
noncomputable def red10 (k : ℕ) : TenAdic →+* ZMod (10 ^ k) :=
  (crt k).symm.toRingHom.comp (digit k)

theorem digit_e5 (k : ℕ) : digit k e5 = (1, 0) := by
  simp [digit, e5, RingHom.prodMap]

/-- `ρₖ` sends the non-trivial idempotent `e5` to a **genuine automorphic residue**:
its image is idempotent in `ZMod (10ᵏ)`. -/
theorem red10_e5_idem (k : ℕ) : (red10 k e5) * (red10 k e5) = red10 k e5 := by
  rw [← map_mul, e5_idem]

/-- For `k ≥ 1`, the image `ρₖ e5` is one of the two **non-trivial** automorphic residues
(neither `0` nor `1`), matching the `5`-tower `5, 25, 625, 90625, …`. -/
theorem red10_e5_ne (k : ℕ) (hk : 0 < k) :
    red10 k e5 ≠ 0 ∧ red10 k e5 ≠ 1 := by
  have h2 : Fact (1 < 2 ^ k) := ⟨by calc 1 < 2 ^ 1 := by norm_num
                                        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk⟩
  have h5 : Fact (1 < 5 ^ k) := ⟨by calc 1 < 5 ^ 1 := by norm_num
                                        _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk⟩
  have key : crt k (red10 k e5) = (1, 0) := by
    simp only [red10, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply, digit_e5]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, map_zero] at key
    have h0 := congrArg Prod.fst key
    simp only [Prod.fst_zero] at h0
    exact zero_ne_one h0
  · rw [h, map_one] at key
    have h1 := congrArg Prod.snd key
    simp only [Prod.snd_one] at h1
    exact one_ne_zero h1

/-! ## Genuine metric convergence in the `10`-adic metric of `ℤ₂ × ℤ₅` -/

private theorem tendsto_inv_pow (b : ℝ) (hb : 1 < b) :
    Tendsto (fun k : ℕ => b ^ (-(k : ℤ))) atTop (nhds 0) := by
  have hbpos : (0 : ℝ) < b := by linarith
  have hb0 : (0 : ℝ) ≤ b⁻¹ := by positivity
  have hb1 : b⁻¹ < 1 := by rw [inv_lt_one₀ hbpos]; exact hb
  have : Tendsto (fun k : ℕ => b⁻¹ ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1
  refine this.congr (fun k => ?_)
  rw [zpow_neg, zpow_natCast, inv_pow]

/-- Component convergence: an integer sequence with `pⁿ ∣ (f n - a)` converges to `a` in `ℤ_[p]`. -/
private theorem tendsto_padic_of_dvd {p : ℕ} [hp : Fact p.Prime] (a : ℤ) (f : ℕ → ℤ)
    (hf : ∀ k, (p ^ k : ℤ) ∣ (f k - a)) :
    Tendsto (fun k => ((f k : ℤ) : ℤ_[p])) atTop (nhds ((a : ℤ) : ℤ_[p])) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun (k : ℕ) => (p : ℝ) ^ (-(k : ℤ)))
    (fun (k : ℕ) => norm_nonneg (((f k : ℤ) : ℤ_[p]) - ((a : ℤ) : ℤ_[p]))) (fun (k : ℕ) => ?_) ?_
  · have hcast : ((f k : ℤ) : ℤ_[p]) - ((a : ℤ) : ℤ_[p]) = (((f k - a : ℤ)) : ℤ_[p]) := by
      push_cast; ring
    rw [hcast]
    exact norm_int_le_pow_iff_dvd.mpr (hf k)
  · have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    exact tendsto_inv_pow (p : ℝ) hp1

/-- **Metric convergence of the `5`-tower.**  Any integer sequence `f` of `k`-digit
automorphic numbers for the `5`-tower (`f k ≡ 1 mod 2ᵏ`, `f k ≡ 0 mod 5ᵏ`) converges,
in the `10`-adic metric of `ℤ₂ × ℤ₅`, to the non-trivial idempotent `e5 = (1, 0)`. -/
theorem tendsto_e5 (f : ℕ → ℤ)
    (h2 : ∀ k, (2 ^ k : ℤ) ∣ (f k - 1))
    (h5 : ∀ k, (5 ^ k : ℤ) ∣ f k) :
    Tendsto (fun k => (((f k : ℤ) : ℤ_[2]), ((f k : ℤ) : ℤ_[5]))) atTop (nhds e5) := by
  have c2 : Tendsto (fun k => ((f k : ℤ) : ℤ_[2])) atTop (nhds ((1 : ℤ) : ℤ_[2])) :=
    tendsto_padic_of_dvd 1 f h2
  have c5 : Tendsto (fun k => ((f k : ℤ) : ℤ_[5])) atTop (nhds ((0 : ℤ) : ℤ_[5])) := by
    apply tendsto_padic_of_dvd 0 f
    intro k; simpa using h5 k
  have := c2.prodMk_nhds c5
  simpa [e5] using this

/-- **Metric convergence of the `6`-tower.**  Any integer sequence `f` of `k`-digit
automorphic numbers for the `6`-tower (`f k ≡ 0 mod 2ᵏ`, `f k ≡ 1 mod 5ᵏ`) converges,
in the `10`-adic metric, to the non-trivial idempotent `e6 = (0, 1)`. -/
theorem tendsto_e6 (f : ℕ → ℤ)
    (h2 : ∀ k, (2 ^ k : ℤ) ∣ f k)
    (h5 : ∀ k, (5 ^ k : ℤ) ∣ (f k - 1)) :
    Tendsto (fun k => (((f k : ℤ) : ℤ_[2]), ((f k : ℤ) : ℤ_[5]))) atTop (nhds e6) := by
  have c2 : Tendsto (fun k => ((f k : ℤ) : ℤ_[2])) atTop (nhds ((0 : ℤ) : ℤ_[2])) := by
    apply tendsto_padic_of_dvd 0 f
    intro k; simpa using h2 k
  have c5 : Tendsto (fun k => ((f k : ℤ) : ℤ_[5])) atTop (nhds ((1 : ℤ) : ℤ_[5])) :=
    tendsto_padic_of_dvd 1 f h5
  have := c2.prodMk_nhds c5
  simpa [e6] using this

end AutomorphicNumberOQ01OQ03OQ02
