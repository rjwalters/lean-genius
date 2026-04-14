/-
  Aristotle targets for Erdős Problem #476 (Erdős-Heilbronn Conjecture)
  Routine supporting lemmas for automated proof search.
  See Erdos476Problem.lean for the main formalization.

  Criteria for inclusion:
  - card_two_case: |A| = 2 → |A +̂ A| = 1 (Finset case analysis + commutativity)
  - ap_card_eq_n: arithmetic progression has n elements when d ≠ 0, n ≤ p
  - NOT restrictedSumsetR definition (definition sorry)
  - NOT combinatorial_nullstellensatz (deep exterior algebra)
  - NOT erdos_476 (main result, axiomatized)
-/
import Mathlib

namespace Erdos476Aristotle

open Finset

variable (p : ℕ) [Fact p.Prime]

/-- The restricted sumset A +̂ A = {a + b : a ≠ b, a b ∈ A}. -/
def restrictedSumset (A : Finset (ZMod p)) : Finset (ZMod p) :=
  (A.product A).filter (fun ab => ab.1 ≠ ab.2) |>.image (fun ab => ab.1 + ab.2)

/-- Arithmetic progression {a, a+d, ..., a+(n-1)d} in ZMod p. -/
def arithmeticProgression (a d : ZMod p) (n : ℕ) : Finset (ZMod p) :=
  (Finset.range n).image (fun i => a + i • d)

-- Routine: When |A| = 2, write A = {a, b} and observe that
-- the only pairs with distinct elements are (a,b) and (b,a),
-- both giving sum a+b = b+a (commutativity in ZMod p).
-- So A +̂ A = {a + b}, which has cardinality 1.
theorem card_two_case (A : Finset (ZMod p)) (h : A.card = 2) :
    (restrictedSumset p A).card = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
  have hRS : restrictedSumset p {a, b} = {a + b} := by
    ext x
    unfold restrictedSumset
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product,
               Finset.mem_singleton, Prod.exists, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨c, d, ⟨⟨hc, hd⟩, hne⟩, rfl⟩
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact absurd rfl hne
      · rfl
      · exact add_comm b a
      · exact absurd rfl hne
    · rintro rfl
      exact ⟨a, b, ⟨⟨Or.inl rfl, Or.inr rfl⟩, hab⟩, rfl⟩
  rw [hRS, Finset.card_singleton]

-- Routine: The map i ↦ a + i • d is injective on {0,...,n-1}
-- when d ≠ 0 in ZMod p (a field) and n ≤ p.
-- Hence (Finset.range n).image (fun i => a + i • d) has card = n.
theorem ap_card_eq_n (a d : ZMod p) (n : ℕ) (hd : d ≠ 0) (hn : n ≤ p) :
    (arithmeticProgression p a d n).card = n := by
  unfold arithmeticProgression
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  simp only [Finset.mem_coe, Finset.mem_range] at hi hj
  have hip : i < p := hi.trans_le hn
  have hjp : j < p := hj.trans_le hn
  -- Cancel a: a + i • d = a + j • d → i • d = j • d
  have hsmul : i • d = j • d := add_left_cancel hij
  -- In ZMod p (a field), (i : ZMod p) * d = (j : ZMod p) * d
  have hmul : (i : ZMod p) * d = (j : ZMod p) * d := by
    rw [← nsmul_eq_mul, ← nsmul_eq_mul]; exact hsmul
  -- Since d ≠ 0 in the field ZMod p, cancel d
  have heq_cast : (i : ZMod p) = (j : ZMod p) := mul_right_cancel₀ hd hmul
  -- Recover ℕ values: for k < p, (k : ZMod p).val = k
  have h_val_i : (i : ZMod p).val = i := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hip
  have h_val_j : (j : ZMod p).val = j := by
    rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hjp
  have hvals : (i : ZMod p).val = (j : ZMod p).val := congr_arg ZMod.val heq_cast
  omega

end Erdos476Aristotle
