import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-
# Non-Cyclic 2-Torsion Bound for (ZMod n)ˣ

Proves: For n ≥ 3, ¬IsCyclic (ZMod n)ˣ → |{x ∈ (ZMod n)ˣ | x² = 1}| ≥ 3.

This is the final sorry in the Gauss-Wilson theorem formalization.

## Proof Strategy
1. From ¬IsCyclic and ZMod.isCyclic_units_iff, n is not {0,1,2,4,p^k,2p^k}.
2. Case A: n has no odd prime factor → n = 2^k with k ≥ 3. Construct 2^(k-1)+1.
3. Case B: n has odd prime factor p. Extract p-part: n = p^v · m with gcd(p^v, m) = 1.
   Since n ≠ p^v (ruled out), m ≥ 2. Since n ≠ 2p^v (ruled out), m ≥ 3.
   Both p^v ≥ 3 and m ≥ 3, so use CRT to get (1, -1) as third square root.
4. Lift ZMod n element to (ZMod n)ˣ via x² = 1 → x is a unit.
-/

namespace GaussWilsonNonCyclic

open Nat Finset ZMod

-- ============================================================================
-- Section 1: Lifting x² = 1 from ZMod n to (ZMod n)ˣ
-- ============================================================================

/-- If x² = 1 in ZMod n, then x is a unit (with inverse x itself). -/
def unitOfSqEqOne {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) : (ZMod n)ˣ :=
  ⟨x, x, by rw [← sq]; exact hx, by rw [← sq]; exact hx⟩

@[simp]
theorem unitOfSqEqOne_val {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) :
    (unitOfSqEqOne x hx : ZMod n) = x := rfl

theorem unitOfSqEqOne_sq {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) :
    (unitOfSqEqOne x hx) ^ 2 = 1 := by
  ext; simp [Units.val_pow_eq_pow_val, hx]

theorem unitOfSqEqOne_ne_one {n : ℕ} [NeZero n] {x : ZMod n} (hx : x ^ 2 = 1)
    (hne : x ≠ 1) : unitOfSqEqOne x hx ≠ 1 := by
  intro h; exact hne (congr_arg Units.val h)

theorem unitOfSqEqOne_ne_neg_one {n : ℕ} [NeZero n] {x : ZMod n} (hx : x ^ 2 = 1)
    (hne : x ≠ -1) : unitOfSqEqOne x hx ≠ -1 := by
  intro h
  have : (unitOfSqEqOne x hx : ZMod n) = ((-1 : (ZMod n)ˣ) : ZMod n) := congr_arg Units.val h
  simp at this; exact hne this

-- ============================================================================
-- Section 2: Utility Lemmas
-- ============================================================================

private lemma neg_one_ne_one_zmod' {n : ℕ} (hn : n ≥ 3) : (-1 : ZMod n) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro heq
  have : (n : ℤ) ∣ (-2 : ℤ) := by
    rw [show (-2 : ℤ) = -1 - 1 from by ring]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast; linarith [heq]
  have : n ≤ 2 := by
    have := Int.natAbs_le.mp (Int.le_of_dvd (by norm_num) (dvd_abs.mpr this))
    omega
  omega

private lemma neg_one_ne_one_units' {n : ℕ} (hn : n ≥ 3) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h
  exact neg_one_ne_one_zmod' hn (by
    have := congr_arg Units.val h; simp at this; exact this.symm)

-- ============================================================================
-- Section 3: CRT third square root construction
-- ============================================================================

/-- For coprime a, b ≥ 3, there exists x : ZMod (a*b) with x² = 1, x ≠ ±1. -/
theorem exists_third_sqrt_coprime {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : a ≥ 3) (hb : b ≥ 3) :
    ∃ x : ZMod (a * b), x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 := by
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  haveI : NeZero (a * b) := ⟨by positivity⟩
  let φ := ZMod.chineseRemainder hab
  use φ.symm (1, -1)
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_one φ.symm, ← map_pow]; congr 1; ext <;> simp [sq]
  · intro h
    have : (1 : ZMod a × ZMod b) = ((1, -1) : ZMod a × ZMod b) := by
      rw [← map_one φ, ← h, φ.apply_symm_apply]
    simp at this; exact neg_one_ne_one_zmod' hb this.symm
  · intro h
    have : (-1 : ZMod a × ZMod b) = ((1, -1) : ZMod a × ZMod b) := by
      rw [← map_neg, ← map_one φ, ← h, φ.apply_symm_apply]
    simp [Prod.ext_iff, Prod.neg_def] at this
    exact neg_one_ne_one_zmod' ha this.1

-- ============================================================================
-- Section 4: Power of 2 third square root construction
-- ============================================================================

private theorem pow2_sq_sub_one_dvd (k : ℕ) (hk : k ≥ 3) :
    2 ^ k ∣ ((2 ^ (k - 1) + 1) ^ 2 - 1) := by
  have h1 : (2 ^ (k - 1) + 1) ^ 2 - 1 =
      (2 ^ (k - 1) + 1 - 1) * (2 ^ (k - 1) + 1 + 1) := by omega
  rw [h1]; simp only [add_tsub_cancel_right]
  have h2 : 2 ^ (k - 1) + 2 = 2 * (2 ^ (k - 2) + 1) := by
    rw [show k - 1 = (k - 2) + 1 from by omega, pow_succ]; ring
  rw [h2, show 2 ^ (k - 1) * (2 * (2 ^ (k - 2) + 1)) =
    2 ^ (k - 1) * 2 * (2 ^ (k - 2) + 1) from by ring,
    show 2 ^ (k - 1) * 2 = 2 ^ k from by
      rw [show k = (k - 1) + 1 from by omega, pow_succ]]
  exact dvd_mul_right _ _

private theorem pow2_cast_sq_eq_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ^ 2 = 1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨by positivity⟩
  have hdvd := pow2_sq_sub_one_dvd k hk
  have : ((2 ^ (k - 1) + 1) ^ 2 - 1 + 1 : ℕ) = (2 ^ (k - 1) + 1) ^ 2 := by omega
  calc ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ^ 2
      = ((((2 ^ (k - 1) + 1) ^ 2 : ℕ) : ZMod (2 ^ k))) := by push_cast; ring
    _ = ((((2 ^ (k - 1) + 1) ^ 2 - 1 + 1 : ℕ) : ZMod (2 ^ k))) := by rw [this]
    _ = ((((2 ^ (k - 1) + 1) ^ 2 - 1 : ℕ) : ZMod (2 ^ k)) + 1) := by push_cast; ring
    _ = (0 + 1) := by rw [ZMod.natCast_zmod_eq_zero_iff_dvd.mpr hdvd]
    _ = 1 := by ring

private theorem pow2_cast_ne_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ≠ 1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨by positivity⟩
  intro h
  have hlt : 2 ^ (k - 1) + 1 < 2 ^ k := by
    calc 2 ^ (k - 1) + 1 < 2 ^ (k - 1) + 2 ^ (k - 1) := by omega
      _ = 2 ^ k := by rw [show k = (k - 1) + 1 from by omega, pow_succ]; ring
  have := congr_arg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_one (by positivity)] at this
  omega

private theorem pow2_cast_ne_neg_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ≠ -1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨by positivity⟩
  intro h
  have hlt : 2 ^ (k - 1) + 1 < 2 ^ k := by
    calc 2 ^ (k - 1) + 1 < 2 ^ (k - 1) + 2 ^ (k - 1) := by omega
      _ = 2 ^ k := by rw [show k = (k - 1) + 1 from by omega, pow_succ]; ring
  have := congr_arg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, ZMod.val_neg_one'] at this
  have : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [show k = (k - 1) + 1 from by omega, pow_succ]
  omega

theorem exists_third_sqrt_pow2 (k : ℕ) (hk : k ≥ 3) :
    ∃ x : ZMod (2 ^ k), x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 :=
  ⟨_, pow2_cast_sq_eq_one k hk, pow2_cast_ne_one k hk, pow2_cast_ne_neg_one k hk⟩

-- ============================================================================
-- Section 5: Number theory - structure of non-cyclic n
-- ============================================================================

/-- For n ≥ 3 with no odd prime factors, n is a power of 2 with exponent ≥ 3. -/
private lemma is_pow2_of_no_odd_prime_factor {n : ℕ} (hn : n ≥ 3) (hn4 : n ≠ 4)
    (h_no_odd : ∀ p, Nat.Prime p → p ≠ 2 → ¬(p ∣ n)) :
    ∃ k, n = 2 ^ k ∧ k ≥ 3 := by
  -- Every prime factor of n is 2
  have h_all2 : ∀ p, Nat.Prime p → p ∣ n → p = 2 := by
    intro p hp hpn
    by_contra hne
    exact h_no_odd p hp hne hpn
  -- n = 2^(n.factorization 2) since all prime factors are 2
  -- Use: n = ∏ p in n.factorization.support, p ^ n.factorization p
  -- and n.factorization.support ⊆ {2}
  have hn_pos : 0 < n := by omega
  have hsup : n.factorization.support ⊆ {2} := by
    intro p hp
    rw [Finsupp.mem_support_iff, ne_eq] at hp
    have := Nat.prime_of_mem_primeFactors (Nat.mem_primeFactors.mpr ⟨hp, hn_pos.ne'⟩)
    simp [h_all2 p this (Nat.dvd_of_mem_primeFactors
      (Nat.mem_primeFactors.mpr ⟨hp, hn_pos.ne'⟩))]
  use n.factorization 2
  constructor
  · -- n = 2^(factorization 2)
    rw [← Nat.factorization_prod_pow_eq_self hn_pos.ne']
    rw [show n.factorization.prod (· ^ ·) =
      ∏ p ∈ n.factorization.support, p ^ n.factorization p from rfl]
    have : n.factorization.support = {2} ∨ n.factorization.support = ∅ := by
      rcases Finset.subset_singleton_iff.mp hsup with h | h
      · right; exact h
      · left; exact h
    rcases this with hsup_eq | hsup_empty
    · rw [hsup_eq]; simp
    · -- support is empty means n = 1, contradiction
      exfalso
      have : n = 1 := by
        rw [← Nat.factorization_prod_pow_eq_self hn_pos.ne']
        rw [show n.factorization.prod (· ^ ·) =
          ∏ p ∈ n.factorization.support, p ^ n.factorization p from rfl]
        rw [hsup_empty]; simp
      omega
  · -- k ≥ 3
    by_contra hlt; push_neg at hlt
    -- n = 2^k with k ≤ 2: n ∈ {1, 2, 4}
    interval_cases (n.factorization 2) <;> simp_all <;> omega

/-- The p-part and coprime complement of n, where p is an odd prime dividing n.
    Uses Nat.ordProj and ordCompl from Mathlib.factorization. -/

/-- For n ≥ 3 with an odd prime factor, and n not of the form p^k or 2*p^k,
    n has a coprime factorization into two parts both ≥ 3. -/
private lemma coprime_split_of_odd_factor {n : ℕ} (hn : n ≥ 3)
    {p : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hp_dvd : p ∣ n)
    (hform : ∀ q m, Nat.Prime q → Odd q → 1 ≤ m → n ≠ q ^ m ∧ n ≠ 2 * q ^ m) :
    ∃ a b, n = a * b ∧ Nat.Coprime a b ∧ a ≥ 3 ∧ b ≥ 3 := by
  -- Extract the p-part: a = p^(factorization p), b = n / a
  -- They are coprime by Nat.coprime_ordCompl
  set v := n.factorization p
  set a := p ^ v  -- the p-part (ordProj)
  set b := n / a  -- the coprime complement (ordCompl)
  have hn_pos : 0 < n := by omega
  -- v ≥ 1 since p | n
  have hv_pos : v ≥ 1 := by
    simp only [v]
    rw [Nat.one_le_iff_ne_zero]
    intro h
    rw [Nat.factorization_eq_zero_iff_not_dvd hp hn_pos.ne'] at h
    exact h hp_dvd
  -- a ≥ p ≥ 3
  have ha_ge : a ≥ 3 := by
    have : a ≥ p := le_self_pow₀ hv_pos.ne'
    have : p ≥ 3 := by
      have := hp.two_le; rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp_odd
      · obtain ⟨k, hk⟩ := h; omega
    omega
  -- n = a * b
  have hab_eq : n = a * b := by
    simp only [a, b]
    exact (Nat.ordProj_mul_ordCompl_eq_self hn_pos.ne' p).symm
  -- coprime
  have hab_cop : Nat.Coprime a b := by
    simp only [a, b]
    exact (Nat.coprime_ordCompl hp hn_pos.ne').symm
  -- b ≥ 3: b ≠ 1 (else n = p^v, contradicted) and b ≠ 2 (else n = 2*p^v, contradicted)
  have hb_ne1 : b ≠ 1 := by
    intro hb1
    have : n = a := by rw [hab_eq, hb1, mul_one]
    -- n = p^v, contradicting hform
    have hp_odd' : Odd p := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp_odd
      · exact h
    exact (hform p v hp hp_odd' hv_pos).1 (this ▸ rfl)
  have hb_ne2 : b ≠ 2 := by
    intro hb2
    -- n = a * 2 = 2 * p^v
    have : n = 2 * a := by rw [hab_eq, hb2]; ring
    have hp_odd' : Odd p := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp_odd
      · exact h
    exact (hform p v hp hp_odd' hv_pos).2 this
  -- b ≥ 1 since n ≥ 3 and a ≥ 3
  have hb_pos : b ≥ 1 := by
    by_contra h; push_neg at h
    simp at h; rw [h] at hab_eq; simp at hab_eq; omega
  have hb_ge : b ≥ 3 := by omega
  exact ⟨a, b, hab_eq, hab_cop, ha_ge, hb_ge⟩

-- ============================================================================
-- Section 6: Main construction - third square root of unity
-- ============================================================================

/-- If n ≥ 3 and ¬IsCyclic (ZMod n)ˣ, there exists x : ZMod n with x² = 1, x ≠ ±1. -/
theorem exists_third_sqrt_of_not_cyclic {n : ℕ} (hn : n ≥ 3)
    [hne : NeZero n] (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    ∃ x : ZMod n, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 := by
  -- Extract structural info from ¬IsCyclic
  rw [ZMod.isCyclic_units_iff] at hncyc
  push_neg at hncyc
  obtain ⟨_, _, _, hn4, hform⟩ := hncyc
  -- Case split: does n have an odd prime factor?
  by_cases h_has_odd : ∃ p, Nat.Prime p ∧ p ≠ 2 ∧ p ∣ n
  · -- Case B: n has an odd prime factor
    obtain ⟨p, hp, hp2, hpn⟩ := h_has_odd
    obtain ⟨a, b, hab_eq, hab_cop, ha, hb⟩ :=
      coprime_split_of_odd_factor hn hp hp2 hpn hform
    rw [hab_eq]
    exact exists_third_sqrt_coprime hab_cop ha hb
  · -- Case A: n has no odd prime factor → n is a power of 2
    push_neg at h_has_odd
    have h_no_odd : ∀ p, Nat.Prime p → p ≠ 2 → ¬(p ∣ n) := fun p hp hp2 => h_has_odd p hp hp2
    obtain ⟨k, hk_eq, hk_ge⟩ := is_pow2_of_no_odd_prime_factor hn hn4 h_no_odd
    rw [hk_eq]
    exact exists_third_sqrt_pow2 k hk_ge

-- ============================================================================
-- Section 7: Main Result
-- ============================================================================

/-- For (ZMod n)ˣ with n ≥ 3, ¬IsCyclic → |{x | x² = 1}| ≥ 3.

    This eliminates the last sorry in the Gauss-Wilson theorem. -/
theorem card_sq_eq_one_ge_three {n : ℕ} (hn : n ≥ 3) [hne : NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    3 ≤ (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
  -- Get a third square root of unity
  obtain ⟨x, hx_sq, hx_ne1, hx_neN1⟩ := exists_third_sqrt_of_not_cyclic hn hncyc
  -- Lift to a unit
  let u := unitOfSqEqOne x hx_sq
  have hu_sq : u ^ 2 = 1 := unitOfSqEqOne_sq x hx_sq
  have hu_ne1 : u ≠ 1 := unitOfSqEqOne_ne_one hx_sq hx_ne1
  have hu_neN1 : u ≠ -1 := unitOfSqEqOne_ne_neg_one hx_sq hx_neN1
  -- The three elements {1, -1, u} are all in S and are distinct
  have h1_mem : (1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hN1_mem : (-1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hu_mem : u ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, hu_sq]
  have hne_1_N1 : (1 : (ZMod n)ˣ) ≠ -1 := (neg_one_ne_one_units' hn).symm
  -- {1, -1, u} ⊆ S
  have hsub : {1, -1, u} ⊆ Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1) := by
    intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact h1_mem
    · exact hN1_mem
    · exact hu_mem
  have hcard3 : ({1, -1, u} : Finset (ZMod n)ˣ).card = 3 := by
    rw [Finset.card_insert_of_not_mem (by
      simp [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨hne_1_N1, hu_ne1⟩)]
    rw [Finset.card_insert_of_not_mem (by simp; exact hu_neN1)]
    rw [Finset.card_singleton]
  linarith [Finset.card_le_card hsub]

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Results

### Sorry-free (target)
1. `unitOfSqEqOne`: lift x² = 1 from ZMod n to (ZMod n)ˣ
2. `exists_third_sqrt_coprime`: CRT construction for coprime a, b ≥ 3
3. `exists_third_sqrt_pow2`: power-of-2 construction for 2^k, k ≥ 3
4. `is_pow2_of_no_odd_prime_factor`: structural lemma for pure powers of 2
5. `coprime_split_of_odd_factor`: structural lemma for odd prime factors
6. `exists_third_sqrt_of_not_cyclic`: main construction combining all cases
7. `card_sq_eq_one_ge_three`: THE theorem eliminating the Gauss-Wilson sorry

### Key Mathlib dependencies
- `ZMod.isCyclic_units_iff`: characterization of cyclic (ZMod n)ˣ
- `ZMod.chineseRemainder`: ring isomorphism for CRT
- `Nat.ordProj_mul_ordCompl_eq_self`: p-part × coprime complement = n
- `Nat.coprime_ordCompl`: p-part is coprime to complement
- `Nat.factorization_prod_pow_eq_self`: factorization reconstruction
-/

#check @card_sq_eq_one_ge_three
#check @exists_third_sqrt_of_not_cyclic

end GaussWilsonNonCyclic
