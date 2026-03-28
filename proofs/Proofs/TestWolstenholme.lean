import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

-- Wilson's theorem: (p-1)! ≡ -1 (mod p)
-- In ZMod p: product of nonzero elements = -1
#check ZMod.prod_univ_prime
-- Fermat's little theorem
#check ZMod.pow_card_sub_one_eq_one
#check ZMod.units_pow_card_sub_one_eq_one
-- Sum of powers
#check Finset.sum_pow_eq_pow_sum
-- ZMod field instance
#check ZMod.instField
-- Finite field power sum: for 1 ≤ k < p-1, ∑_{x ∈ (ℤ/pℤ)*} x^k = 0.
-- Proof: the map x ↦ g*x is a bijection on units (for any unit g),
-- so ∑ x^k = ∑ (gx)^k = g^k · ∑ x^k. Since g^k ≠ 1 for a primitive
-- root g with 0 < k < ord(g), we get (1 - g^k) · ∑ x^k = 0, hence ∑ x^k = 0.
example (p : ℕ) (hp : Fact (Nat.Prime p)) (k : ℕ) (hk : 1 ≤ k) (hkp : k < p - 1) :
    ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ k = 0 := by
  -- Pick a generator g of (ZMod p)ˣ (which is cyclic since p is prime)
  haveI : IsCyclic (ZMod p)ˣ := inferInstance
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := (ZMod p)ˣ)
  -- g^k ≠ 1 since 0 < k < p-1 = |group| and g is a generator
  have hgk_ne : (g : ZMod p) ^ k ≠ 1 := by
    intro heq
    -- If g^k = 1 as a ZMod p element, then g^k = 1 as a unit
    have hunit : g ^ k = 1 := by
      ext; simpa using heq
    -- orderOf g = p - 1 (generator of group of order p - 1)
    have hord : orderOf g = Fintype.card (ZMod p)ˣ := by
      rw [orderOf_eq_card_of_forall_mem_zpowers (fun x => hg x)]
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out] at hord
    -- k < p - 1 = orderOf g, but g^k = 1 contradicts minimality of order
    have := orderOf_dvd_of_pow_eq_one hunit
    omega
  -- The sum is invariant under multiplication by g:
  -- ∑ x^k = ∑ (g·x)^k = g^k · ∑ x^k
  have hinv : (g : ZMod p) ^ k * ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ k =
      ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_nbij (· * g)
    · intro a _; exact Finset.mem_univ _
    · intro a₁ a₂ _ _ h; exact mul_right_cancel h
    · intro b _; exact ⟨b * g⁻¹, Finset.mem_univ _, by group⟩
    · intro a _
      simp only [Units.val_mul, mul_pow]
  -- From g^k · S = S and g^k ≠ 1, conclude S = 0
  -- Rearrange: (g^k - 1) · S = 0, and g^k - 1 is a unit, so S = 0
  have hsub : ((g : ZMod p) ^ k - 1) * ∑ x : (ZMod p)ˣ, (x : ZMod p) ^ k = 0 := by
    rw [sub_mul, one_mul, hinv, sub_self]
  rcases mul_eq_zero.mp hsub with h | h
  · exfalso; exact hgk_ne (sub_eq_zero.mp h)
  · exact h
