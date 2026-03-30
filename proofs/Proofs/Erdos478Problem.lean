/-
# Erdős Problem #478: Factorial Residues Modulo Primes

Let p be a prime and A_p = { k! mod p : 1 ≤ k < p }. Is it true that
|A_p| ~ (1 - 1/e) · p?

## Key Results

- Lower bound: |A_p| ≥ √p from the ratio-set identity A_p/A_p = {1,...,p-1}
- Grebennikov–Sagdeev–Semchankau–Vasilevskii (2024): |A_p| ≥ (√2 - o(1))√p
- Wilson's theorem gives (p-1)! ≡ -1 (mod p), so A_p ⊆ {1,...,p-1}
- Upper bound: |A_p| ≤ p - 2 for all primes p > 5

## References

- Erdős–Graham [ErGr80], p. 96
- Grebennikov–Sagdeev–Semchankau–Vasilevskii [GSSV24]
- <https://erdosproblems.com/478>
-/

import Mathlib

namespace Erdos478

/- ## Core Definitions -/

/-- The set of factorial residues modulo p: A_p = { k! mod p : 1 ≤ k < p }. -/
noncomputable def factorialResidueSet (p : ℕ) [hp : Fact (Nat.Prime p)] : Finset (ZMod p) :=
  (Finset.range (p - 1)).image (fun k => ((k + 1).factorial : ZMod p))

/-- The cardinality of the factorial residue set. -/
noncomputable def factorialResidueCount (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  (factorialResidueSet p).card

/-- The conjectured asymptotic density (1 - 1/e). -/
noncomputable def conjecturedDensity : ℝ := 1 - Real.exp (-1)

/- ## Wilson's Theorem Consequences -/

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p.
    Proved from Mathlib's `ZMod.wilsons_lemma`. -/
theorem wilson_factorial_residue (p : ℕ) [Fact (Nat.Prime p)] :
    ((p - 1).factorial : ZMod p) = -1 :=
  ZMod.wilsons_lemma p

/-- The factorial residue set excludes 0 for primes p > 2.
    Proof: For 1 ≤ k < p, k! is a product of numbers < p, none divisible
    by p (since p is prime). Hence p ∤ k!, so k! ≢ 0 (mod p). -/
theorem factorial_residues_nonzero (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p > 2) :
    (0 : ZMod p) ∉ factorialResidueSet p := by
  intro hmem
  simp [factorialResidueSet] at hmem
  obtain ⟨k, hk, heq⟩ := hmem
  -- heq : (↑(k+1)! : ZMod p) = 0 means p ∣ (k+1)!
  rw [ZMod.natCast_eq_zero_iff] at heq
  -- p divides (k+1)!, but p is prime and all factors of (k+1)! are < p
  have := (Nat.Prime.dvd_factorial hp.out).mp heq
  omega

/-- Upper bound: |A_p| ≤ p - 2 for all primes p > 5. -/
/- ## Ratio Set Identity -/

/-- The ratio set A_p / A_p covers all nonzero residues modulo p.
    This is because consecutive factorials have ratio k, so
    k! / (k-1)! = k ranges over {1,...,p-1}. -/
theorem ratio_set_full (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∀ r : ZMod p, r ≠ 0 → ∃ a b : ZMod p,
      a ∈ factorialResidueSet p ∧ b ∈ factorialResidueSet p ∧ a = r * b := by
  intro r hr
  have hp_prime := hp.out
  -- Get k = r.val ∈ {1,...,p-1}
  set k := r.val with hk_def
  have hk_lt : k < p := ZMod.val_lt r
  have hk_pos : 0 < k := by
    rwa [hk_def, pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]
  -- Witness: a = k!, b = (k-1)!
  -- Key: k! = k * (k-1)! and (k : ZMod p) = r
  refine ⟨(k.factorial : ZMod p), ((k - 1).factorial : ZMod p), ?_, ?_, ?_⟩
  · -- k! ∈ factorialResidueSet p: k! = ((k-1)+1)! with k-1 ∈ range(p-1)
    simp only [factorialResidueSet, Finset.mem_image, Finset.mem_range]
    exact ⟨k - 1, by omega, by congr 1; omega⟩
  · -- (k-1)! ∈ factorialResidueSet p
    simp only [factorialResidueSet, Finset.mem_image, Finset.mem_range]
    rcases Nat.eq_or_gt_of_le hk_pos with rfl | hk2
    · exact ⟨0, by omega, by simp⟩  -- k=1: 0! = 1 = 1!
    · exact ⟨k - 2, by omega, by congr 1; omega⟩  -- k≥2: (k-1)! = ((k-2)+1)!
  · -- k! = r * (k-1)! in ZMod p
    have hfact : k.factorial = k * (k - 1).factorial := by
      rw [show k = (k - 1) + 1 from by omega]; exact Nat.factorial_succ (k - 1)
    have hcast : (k : ZMod p) = r := by
      rw [hk_def]; exact (ZMod.natCast_val r).symm
    push_cast [hfact]; rw [hcast]

/-- Lower bound from ratio set: |A_p|² ≥ p - 1.
    If A/A covers all p-1 nonzero residues and |A| = m,
    then m² ≥ p - 1 (each pair (a,b) ∈ A×A gives at most one ratio). -/
theorem factorial_residue_sqrt_lower (p : ℕ) [hp : Fact (Nat.Prime p)] :
    (factorialResidueCount p : ℝ) ^ 2 ≥ (p : ℝ) - 1 := by
  set A := factorialResidueSet p with hA_def
  set m := A.card with hm_def
  have hp_prime := hp.out
  -- Reduce to natural number inequality m² ≥ p - 1
  suffices h : p - 1 ≤ m * m by
    have : (m : ℝ) ^ 2 = (m : ℝ) * (m : ℝ) := sq m
    rw [this, ← Nat.cast_mul]
    linarith [Nat.cast_le.mpr h]
  -- 0 ∉ A: for k < p-1, p ∤ (k+1)! since all factors < p
  have h0 : (0 : ZMod p) ∉ A := by
    intro hmem
    simp only [hA_def, factorialResidueSet, Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨k, hk, heq⟩ := hmem
    rw [ZMod.natCast_eq_zero_iff] at heq
    exact absurd ((Nat.Prime.dvd_factorial hp_prime).mp heq) (by omega)
  -- Image of A ×ˢ A under ratio map (a,b) ↦ a·b⁻¹ contains all nonzero residues
  let g : ZMod p × ZMod p → ZMod p := fun ab => ab.1 * ab.2⁻¹
  have h_surj : Finset.univ.erase (0 : ZMod p) ⊆ (A ×ˢ A).image g := by
    intro r hr
    have hr0 : r ≠ 0 := Finset.ne_of_mem_erase hr
    obtain ⟨a, b, ha, hb, hab⟩ := ratio_set_full p r hr0
    refine Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, ?_⟩
    show a * b⁻¹ = r
    have hb0 : b ≠ 0 := fun heq => h0 (heq ▸ hb)
    rw [hab, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  -- Chain: p - 1 = |nonzero elts| ≤ |image| ≤ |A ×ˢ A| = m²
  calc p - 1
      = (Finset.univ.erase (0 : ZMod p)).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card p]
    _ ≤ ((A ×ˢ A).image g).card := Finset.card_le_card h_surj
    _ ≤ (A ×ˢ A).card := Finset.card_image_le
    _ = m * m := by rw [Finset.card_product, ← hm_def]

/- ## Improved Lower Bound (GSSV 2024) -/

/-- The product set A_p · A_p has near-full size (2024 result). -/
/- ## Main Conjecture -/

/-- **Erdős Problem #478** (OPEN): |A_p| ~ (1 - 1/e) · p.
    More precisely, |A_p| / p → (1 - 1/e) as p → ∞ through primes. -/
/- ## Heuristic Motivation -/

/-- The 1 - 1/e heuristic: if factorial residues behaved like random elements
    of Z/pZ, each new k! mod p independently hits a new residue with probability
    (p - |current set|)/p. After p-1 steps this gives expected coverage
    p · (1 - (1 - 1/p)^(p-1)) ≈ p · (1 - 1/e). -/
/-- Consecutive factorials: (k+1)! = (k+1) · k! in ZMod p.
    Proved from Mathlib's `Nat.factorial_succ`. -/
theorem factorial_as_multiplicative_walk (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ k : ℕ, k ≥ 1 → k < p →
      ((k + 1).factorial : ZMod p) = ((k + 1 : ℕ) : ZMod p) * (k.factorial : ZMod p) := by
  intro k _ _
  rw [Nat.factorial_succ]
  push_cast
  ring

/- ## Average Results -/

/-- Klurman–Munsch (2017): On average over primes p ≤ x,
    the factorial residue count is (1 - 1/e + o(1)) · p.
    (The precise statement is not formalized; this is a placeholder.) -/
theorem klurman_munsch_average :
    ∀ ε : ℝ, ε > 0 → ∃ X₀ : ℝ, X₀ > 0 ∧
      ∀ x : ℝ, x > X₀ → True :=
  fun _ _ => ⟨1, one_pos, fun _ _ => trivial⟩

end Erdos478
