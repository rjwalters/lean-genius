/-
  Aristotle targets for Erdős Problem #44
  Routine supporting lemmas for automated proof search.
  See Erdos44Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, cardinality, bounds, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  All sorries proved by researcher-3 (2026-03-22).
-/
import Mathlib

open Finset BigOperators

namespace Erdos44Aristotle

/-
  ## Erdős-Turán Sidon Construction

  For prime p, the set A_p = {2p·i + (i²%p) + 1 : i ∈ range p} is Sidon.
  The following lemmas prove the key properties.
-/

/-- The Erdős-Turán map is strictly monotone: values lie in disjoint
    intervals [2pi+1, 2pi+p] for each i. -/
private lemma erdosTuran_strictMono (p : ℕ) (hp : 1 ≤ p) :
    StrictMono (fun i : ℕ => 2 * p * i + i * i % p + 1) := by
  intro a b hab
  show 2 * p * a + a * a % p + 1 < 2 * p * b + b * b % p + 1
  have hra : a * a % p < p := Nat.mod_lt _ (by omega)
  calc 2 * p * a + a * a % p + 1
      ≤ 2 * p * a + p := by omega
    _ < 2 * p * a + 2 * p := by omega
    _ = 2 * p * (a + 1) := by ring
    _ ≤ 2 * p * b := by nlinarith
    _ ≤ 2 * p * b + b * b % p + 1 := by omega

/-- The Erdős-Turán map i ↦ 2p·i + (i²%p) + 1 is injective on {0,...,p-1}:
    values lie in disjoint intervals [2pi, 2pi+p) for distinct i. -/
theorem erdosTuran_injOn (p : ℕ) (hp : 1 ≤ p) :
    Set.InjOn (fun i => 2 * p * i + i * i % p + 1) (↑(Finset.range p)) :=
  (erdosTuran_strictMono p hp).injective.injOn

/-- The Erdős-Turán construction has exactly p elements. -/
theorem erdosTuran_card (p : ℕ) (hp : 1 ≤ p) :
    ((Finset.range p).image (fun i => 2 * p * i + i * i % p + 1)).card = p := by
  rw [Finset.card_image_of_injective _ (erdosTuran_strictMono p hp).injective]
  exact Finset.card_range p

/-- All elements of the Erdős-Turán construction are ≥ 1. -/
theorem erdosTuran_pos (p i : ℕ) : 1 ≤ 2 * p * i + i * i % p + 1 := by
  omega

/-- All elements of the Erdős-Turán construction are ≤ 2p². -/
theorem erdosTuran_le (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < p) :
    2 * p * i + i * i % p + 1 ≤ 2 * p * p := by
  have h1 : i * i % p + 1 ≤ p := by
    have := Nat.mod_lt (i * i) (show 0 < p by omega)
    omega
  have h2 : 2 * p * (i + 1) ≤ 2 * p * p := by nlinarith
  nlinarith

/-- Key step 1: from sum equality, extract index sum equality.
    2p(a+b) + R₁ = 2p(c+d) + R₂ with R₁, R₂ < 2p implies a+b = c+d. -/
theorem sum_eq_of_sum_eq {p a b c d : ℕ}
    (hp : 1 ≤ p) (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (heq : 2 * p * a + a * a % p + 1 + (2 * p * b + b * b % p + 1) =
           2 * p * c + c * c % p + 1 + (2 * p * d + d * d % p + 1)) :
    a + b = c + d := by
  by_contra hne
  have hra : a * a % p < p := Nat.mod_lt _ (by omega)
  have hrb : b * b % p < p := Nat.mod_lt _ (by omega)
  have hrc : c * c % p < p := Nat.mod_lt _ (by omega)
  have hrd : d * d % p < p := Nat.mod_lt _ (by omega)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have key := Nat.mul_le_mul_left (2 * p) (show a + b + 1 ≤ c + d from h)
    have e1 : 2 * p * (a + b + 1) = 2 * p * a + 2 * p * b + 2 * p := by ring
    have e2 : 2 * p * (c + d) = 2 * p * c + 2 * p * d := by ring
    have bound : 2 * p * a + 2 * p * b + 2 * p ≤ 2 * p * c + 2 * p * d := by linarith
    have heq_core : 2 * p * a + a * a % p + (2 * p * b + b * b % p) =
                    2 * p * c + c * c % p + (2 * p * d + d * d % p) := by omega
    omega
  · have key := Nat.mul_le_mul_left (2 * p) (show c + d + 1 ≤ a + b from h)
    have e1 : 2 * p * (c + d + 1) = 2 * p * c + 2 * p * d + 2 * p := by ring
    have e2 : 2 * p * (a + b) = 2 * p * a + 2 * p * b := by ring
    have bound : 2 * p * c + 2 * p * d + 2 * p ≤ 2 * p * a + 2 * p * b := by linarith
    have heq_core : 2 * p * a + a * a % p + (2 * p * b + b * b % p) =
                    2 * p * c + c * c % p + (2 * p * d + d * d % p) := by omega
    omega

/-- Key step 2: when index sums match, remainders match. -/
theorem rem_eq_of_sum_eq {p a b c d : ℕ}
    (hp : 1 ≤ p) (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (heq : 2 * p * a + a * a % p + 1 + (2 * p * b + b * b % p + 1) =
           2 * p * c + c * c % p + 1 + (2 * p * d + d * d % p + 1))
    (hab_cd : a + b = c + d) :
    a * a % p + b * b % p = c * c % p + d * d % p := by
  have h1 : 2 * p * (a + b) = 2 * p * (c + d) := by rw [hab_cd]
  nlinarith [mul_add (2 * p) a b, mul_add (2 * p) c d]

/-- Key step 3: from remainder equality and index sum equality, derive divisibility.
    a² + b² ≡ c² + d² (mod p) and a+b = c+d implies p | (ab - cd). -/
theorem dvd_prod_diff {p a b c d : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (hab : a + b = c + d)
    (hrem : a * a % p + b * b % p = c * c % p + d * d % p) :
    (p : ℤ) ∣ ((a : ℤ) * b - c * d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- Step 1: a² + b² ≡ c² + d² (mod p) in ZMod
  have mod_sq (n : ℕ) : ((n * n % p : ℕ) : ZMod p) = (n : ZMod p) ^ 2 := by
    rw [sq, ← Nat.cast_mul]
    conv_rhs => rw [show (n * n : ℕ) = p * (n * n / p) + n * n % p
                     from (Nat.div_add_mod _ _).symm]
    push_cast
    simp [CharP.cast_eq_zero (ZMod p) p]
  have hrem_z := congr_arg (Nat.cast (R := ZMod p)) hrem
  push_cast at hrem_z
  rw [mod_sq a, mod_sq b, mod_sq c, mod_sq d] at hrem_z
  -- hrem_z : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2
  -- Step 2: a + b = c + d in ZMod
  have hsum_z : (a : ZMod p) + (b : ZMod p) = (c : ZMod p) + (d : ZMod p) := by
    have := congr_arg (Nat.cast (R := ZMod p)) hab
    push_cast at this; exact this
  -- Step 3: Algebraic — derive 2(a-c)(a-d) = 0 in ZMod p
  have hb_eq : (b : ZMod p) = (c : ZMod p) + (d : ZMod p) - (a : ZMod p) := by
    linear_combination hsum_z
  have h_prod_zero : ((a : ZMod p) - c) * ((a : ZMod p) - d) = 0 := by
    have h_identity : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 -
                      (c : ZMod p) ^ 2 - (d : ZMod p) ^ 2 =
                      2 * ((a : ZMod p) - c) * ((a : ZMod p) - d) := by
      rw [hb_eq]; ring
    have h_zero : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 -
                  (c : ZMod p) ^ 2 - (d : ZMod p) ^ 2 = 0 := by
      linear_combination hrem_z
    have h2_ne : (2 : ZMod p) ≠ 0 := by
      intro h
      have : p ∣ 2 := by
        rwa [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
             ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd (by norm_num) this) (by omega)
    rw [h_identity] at h_zero
    rw [mul_assoc] at h_zero
    exact (mul_eq_zero.mp h_zero).resolve_left h2_ne
  -- Step 4: (a-c)(a-d) = 0 means a≡c or a≡d (mod p), giving ab = cd
  rcases mul_eq_zero.mp h_prod_zero with hac | had
  · -- a ≡ c (mod p), so a = c (since a,c < p), then b = d
    have hac_eq : (a : ZMod p) = (c : ZMod p) := sub_eq_zero.mp hac
    have hac_mod : a % p = c % p := by
      have := congr_arg ZMod.val hac_eq
      rwa [ZMod.val_natCast, ZMod.val_natCast] at this
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc] at hac_mod
    have hbd : b = d := by omega
    simp [hac_mod, hbd]
  · -- a ≡ d (mod p), so a = d, b = c, giving ab = cd
    have had_eq : (a : ZMod p) = (d : ZMod p) := sub_eq_zero.mp had
    have had_mod : a % p = d % p := by
      have := congr_arg ZMod.val had_eq
      rwa [ZMod.val_natCast, ZMod.val_natCast] at this
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hd] at had_mod
    have hbc : b = c := by omega
    have : (a : ℤ) * b - c * d = 0 := by push_cast [had_mod, hbc]; ring
    rw [this]; exact dvd_zero _

/-- Key algebraic identity: (a-c)(a-d) = cd - ab when a+b = c+d. -/
theorem factor_identity (a b c d : ℤ) (h : a + b = c + d) :
    (a - c) * (a - d) = c * d - a * b := by
  have : b = c + d - a := by linarith
  rw [this]; ring

/-- Nat.sqrt N * Nat.sqrt N ≤ N (square of integer square root). -/
theorem sqrt_sq_le (N : ℕ) : Nat.sqrt N * Nat.sqrt N ≤ N :=
  Nat.sqrt_le N

/-- Nat.sqrt N ≤ 3 for N < 16. -/
theorem sqrt_le_three (N : ℕ) (hN : N < 16) : Nat.sqrt N ≤ 3 := by
  have h1 : Nat.sqrt N ≤ Nat.sqrt 15 := Nat.sqrt_le_sqrt (by omega)
  have h2 : Nat.sqrt 15 = 3 := by native_decide
  omega

end Erdos44Aristotle
