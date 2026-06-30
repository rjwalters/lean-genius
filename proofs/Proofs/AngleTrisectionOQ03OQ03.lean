import Mathlib

/-
# Angle Trisection OQ-03 / OQ-03: Origami Constructibility and 3-Smooth Degrees

## The Open Question (OQ-03 of the constructibility-complexity thread)

The parent characterizes compass-and-straightedge constructibility by a power-of-2 condition on
the minimal-polynomial degree: `IsConstructible α d ↔ d > 0 ∧ ∃ k, d = 2^k`. Its third open
direction asks to generalize to **higher-dimensional / origami constructions, which use cubic
extensions and so need a different divisibility criterion**.

## What this file proves

Origami (Huzita–Hatori) constructions can solve cubic equations — they can trisect angles and
double the cube — so the admissible degrees are the **3-smooth** numbers `2^a · 3^b`. We mirror
the parent's development for this criterion:

* `ThreeSmooth d` (`= ∃ a b, d = 2^a·3^b`) and `IsOrigamiConstructible α d`;
* `threeSmooth_iff_primeFactors`: `d` is 3-smooth ⟺ every prime factor of `d` is `2` or `3`
  — giving a `Decidable` instance for origami constructibility;
* `constructible_imp_origami`: compass ⊆ origami (a power of 2 is 3-smooth);
* **the separation** `origami_trisects_but_compass_cannot`: degree `3` is origami-constructible
  but **not** compass-constructible — the exact sense in which origami trisects the angle and
  doubles the cube where straightedge-and-compass fails;
* `not_origami_of_five_dvd`: a degree divisible by `5` (e.g. the regular 11-gon, degree `5`) is
  **not** origami-constructible — origami is still limited.

Tags: geometry, constructibility, origami, angle-trisection, number-theory, decidability

**Note.** The parent's `IsConstructible α d ↔ d > 0 ∧ ∃ k, d = 2^k` degree criterion is
reproduced here as the local `CompassConstructibleDegree d` rather than imported, because the
parent's import chain is currently bit-rotted; the criterion (the power-of-2 condition) is
unchanged.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace AngleTrisectionOQ03OQ03

/-- The compass-and-straightedge **degree criterion** (the parent's characterization of
    `IsConstructible`): a degree `d` is constructible iff it is a positive power of two. -/
def CompassConstructibleDegree (d : ℕ) : Prop := 0 < d ∧ ∃ k : ℕ, d = 2 ^ k

/-- A degree is **3-smooth** (origami-admissible) when it has the form `2^a · 3^b`. -/
def ThreeSmooth (d : ℕ) : Prop := ∃ a b : ℕ, d = 2 ^ a * 3 ^ b

/-- **Origami (Huzita–Hatori) constructibility.** The minimal-polynomial degree is a positive
    3-smooth number `2^a·3^b`. Like compass constructibility, it depends only on the degree. -/
def IsOrigamiConstructible (α : ℝ) (d : ℕ) : Prop := 0 < d ∧ ThreeSmooth d

/-! ## Basic structure of 3-smooth numbers -/

theorem threeSmooth_one : ThreeSmooth 1 := ⟨0, 0, by norm_num⟩

theorem threeSmooth_two : ThreeSmooth 2 := ⟨1, 0, by norm_num⟩

theorem threeSmooth_three : ThreeSmooth 3 := ⟨0, 1, by norm_num⟩

/-- 3-smooth numbers are closed under multiplication. -/
theorem threeSmooth_mul {m n : ℕ} (hm : ThreeSmooth m) (hn : ThreeSmooth n) :
    ThreeSmooth (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a + c, b + d, by rw [pow_add, pow_add]; ring⟩

/-- Every power of two is 3-smooth (take `b = 0`). -/
theorem threeSmooth_of_pow_two {d : ℕ} (h : ∃ k, d = 2 ^ k) : ThreeSmooth d := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨k, 0, by norm_num⟩

/-! ## The prime-factor characterization and decidability -/

/-- Forward direction: a prime factor of a 3-smooth number is `2` or `3`. -/
theorem prime_factor_eq_two_or_three {d : ℕ} (h : ThreeSmooth d)
    {p : ℕ} (hp : p ∈ d.primeFactors) : p = 2 ∨ p = 3 := by
  obtain ⟨a, b, rfl⟩ := h
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  rcases (hpp.dvd_mul.mp hpd) with h2 | h3
  · exact Or.inl ((Nat.prime_two.eq_one_or_self_of_dvd p
      (hpp.dvd_of_dvd_pow h2)).resolve_left hpp.ne_one)
  · exact Or.inr ((Nat.prime_three.eq_one_or_self_of_dvd p
      (hpp.dvd_of_dvd_pow h3)).resolve_left hpp.ne_one)

/-- Backward direction: if every prime factor of `d > 0` is `2` or `3`, then `d` is 3-smooth. -/
theorem threeSmooth_of_primeFactors : ∀ d : ℕ, 0 < d →
    (∀ p ∈ d.primeFactors, p = 2 ∨ p = 3) → ThreeSmooth d := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hp
    have hd1 : 1 ≤ d := hd
    rcases eq_or_lt_of_le hd1 with h1 | h1
    · exact h1 ▸ threeSmooth_one
    · -- d > 1: peel off a prime factor
      obtain ⟨p, hpp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpd, hd.ne'⟩
      have hp23 := hp p hpmem
      have hp2 : 2 ≤ p := hpp.two_le
      have hdp_pos : 0 < d / p := Nat.div_pos (Nat.le_of_dvd hd hpd) (by omega)
      have hdp_lt : d / p < d := Nat.div_lt_self (by omega) (by omega)
      have hsub : ∀ q ∈ (d / p).primeFactors, q = 2 ∨ q = 3 := by
        intro q hq
        obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
        exact hp q (Nat.mem_primeFactors.mpr
          ⟨hqp, hqd.trans (Nat.div_dvd_of_dvd hpd), hd.ne'⟩)
      obtain ⟨a, b, hab⟩ := ih (d / p) hdp_lt hdp_pos hsub
      have hd_eq : d = p * (d / p) := (Nat.mul_div_cancel' hpd).symm
      rcases hp23 with rfl | rfl
      · exact ⟨a + 1, b, by rw [hd_eq, hab, pow_succ]; ring⟩
      · exact ⟨a, b + 1, by rw [hd_eq, hab, pow_succ]; ring⟩

/-- **The prime-factor characterization of 3-smooth degrees**: `d > 0` is 3-smooth iff every
    prime factor of `d` is `2` or `3`. The origami analogue of the parent's
    `pow_two_iff_all_prime_factors_two`. -/
theorem threeSmooth_iff_primeFactors {d : ℕ} (hd : 0 < d) :
    ThreeSmooth d ↔ ∀ p ∈ d.primeFactors, p = 2 ∨ p = 3 :=
  ⟨fun h _ hp => prime_factor_eq_two_or_three h hp, threeSmooth_of_primeFactors d hd⟩

/-- Origami constructibility is **decidable** (it reduces to a finite check on prime factors). -/
instance decidable_isOrigamiConstructible (α : ℝ) (d : ℕ) :
    Decidable (IsOrigamiConstructible α d) := by
  by_cases hd : 0 < d
  · exact decidable_of_iff (∀ p ∈ d.primeFactors, p = 2 ∨ p = 3)
      ⟨fun h => ⟨hd, (threeSmooth_iff_primeFactors hd).mpr h⟩,
       fun h => (threeSmooth_iff_primeFactors hd).mp h.2⟩
  · exact isFalse (fun h => hd h.1)

/-! ## Compass ⊆ Origami -/

/-- **Compass constructibility implies origami constructibility.** Every straightedge-and-compass
    constructible degree (a power of 2) is 3-smooth, so origami can do everything compass can. -/
theorem constructible_imp_origami {α : ℝ} {d : ℕ} (h : CompassConstructibleDegree d) :
    IsOrigamiConstructible α d :=
  ⟨h.1, threeSmooth_of_pow_two h.2⟩

/-! ## The separation: origami trisects, compass does not -/

/-- `3` is not a power of two, so degree-3 numbers are not compass-constructible. -/
theorem not_compass_three : ¬ CompassConstructibleDegree 3 := by
  rintro ⟨_, k, hk⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0] at hk; norm_num at hk
  · have : (2 : ℕ) ∣ 3 := by rw [hk]; exact dvd_pow_self 2 hk0.ne'
    norm_num at this

/-- **Origami trisects the angle (and doubles the cube) where compass cannot.**
    The degree `3` extension `ℚ(cos 20°) / ℚ` (angle trisection) — equally `ℚ(∛2) / ℚ`
    (cube doubling) — is origami-constructible but **not** compass-constructible. -/
theorem origami_trisects_but_compass_cannot (α : ℝ) :
    IsOrigamiConstructible α 3 ∧ ¬ CompassConstructibleDegree 3 :=
  ⟨⟨by norm_num, threeSmooth_three⟩, not_compass_three⟩

/-! ## Origami is still limited -/

/-- A 3-smooth number is not divisible by `5`. -/
theorem not_five_dvd_threeSmooth {d : ℕ} (h : ThreeSmooth d) : ¬ (5 ∣ d) := by
  obtain ⟨a, b, rfl⟩ := h
  intro h5
  rcases ((show Nat.Prime 5 by norm_num).dvd_mul.mp h5) with h2 | h3
  · exact absurd ((show Nat.Prime 5 by norm_num).dvd_of_dvd_pow h2) (by norm_num)
  · exact absurd ((show Nat.Prime 5 by norm_num).dvd_of_dvd_pow h3) (by norm_num)

/-- **Origami is not all-powerful.** A degree divisible by `5` — for instance the regular
    11-gon, whose `ℚ(cos 2π/11)/ℚ` has degree `5` — is not origami-constructible. -/
theorem not_origami_of_five_dvd {α : ℝ} {d : ℕ} (h5 : 5 ∣ d) :
    ¬ IsOrigamiConstructible α d :=
  fun h => not_five_dvd_threeSmooth h.2 h5

/-- The regular 11-gon (degree `5`) is not origami-constructible. -/
theorem not_origami_eleven_gon (α : ℝ) : ¬ IsOrigamiConstructible α 5 :=
  not_origami_of_five_dvd (dvd_refl 5)

end AngleTrisectionOQ03OQ03

/-
## Summary

Generalizing the parent's compass criterion (`degree = 2^k`) to **origami**:

- `ThreeSmooth d` (`= 2^a·3^b`), `IsOrigamiConstructible α d`.
- `threeSmooth_iff_primeFactors`: 3-smooth ⟺ all prime factors ∈ {2,3} — the origami analogue
  of the power-of-2 prime-factor criterion, yielding a `Decidable` instance.
- `constructible_imp_origami`: compass ⊆ origami.
- `origami_trisects_but_compass_cannot`: degree 3 is origami- but not compass-constructible —
  trisection and cube-doubling become possible.
- `not_origami_of_five_dvd` / `not_origami_eleven_gon`: origami still cannot reach degree-5
  constructions (the regular 11-gon).

Self-contained: the parent's power-of-2 degree criterion is reproduced as
`CompassConstructibleDegree` (the parent's import chain is currently bit-rotted).

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
