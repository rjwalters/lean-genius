import Proofs.Erdos85OddColumnSignedGram

/-!
# Concrete Clebsch three-fiber Gram exclusion

The points `3*x+i` encode `F₂⁴ × Fin 3`. These are the exact H,D matrices
of `check_weight_three_clebsch_internal.py`. The proof instantiates the
signed-Gram obstruction with the least-significant base-bit character.
It rules out the missing incidence matrix for this concrete candidate;
it makes no classification claim about arbitrary defect graphs or H.
-/

open scoped BigOperators Matrix

namespace Erdos85

def clebschConcreteDefect : Matrix (Fin 48) (Fin 48) ℤ := fun a b =>
  if Nat.xor (a.val / 3) (b.val / 3) ∈ ([1, 2, 4, 8, 15] : List ℕ)
  then 1 else 0

def clebschConcreteInternal : Matrix (Fin 48) (Fin 48) ℤ := fun a b =>
  if (b.val / 3 = Nat.xor (a.val / 3) 3 ∧
        b.val % 3 = (if a.val % 3 = 0 then 1 else if a.val % 3 = 1 then 0 else 2)) ∨
      (b.val / 3 = Nat.xor (a.val / 3) 5 ∧
        b.val % 3 = (if a.val % 3 = 0 then 2 else if a.val % 3 = 2 then 0 else 1)) ∨
      (b.val / 3 = Nat.xor (a.val / 3) 9 ∧
        b.val % 3 = (if a.val % 3 = 1 then 2 else if a.val % 3 = 2 then 1 else 0))
  then 1 else 0

def clebschConcreteSign (a : Fin 48) : ℤ :=
  if (a.val / 3) % 2 = 0 then 1 else -1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem clebschConcrete_sign_data :
    (∀ a, clebschConcreteSign a = 1 ∨ clebschConcreteSign a = -1) ∧
    (∑ a, clebschConcreteSign a) = 0 ∧
    (∀ a, (∑ b, clebschConcreteInternal a b * clebschConcreteSign b) =
      -3 * clebschConcreteSign a) ∧
    (∀ a, (∑ b, clebschConcreteDefect a b * clebschConcreteSign b) =
      3 * clebschConcreteSign a) := by
  decide

/-- No integer matrix with 208 columns of sum three realizes the required
Gram for the explicit Clebsch internal candidate. Binary incidence is a
special case; its entries need not be assumed nonnegative here. -/
theorem clebschConcrete_no_incidence
    (B : Matrix (Fin 48) (Fin 208) ℤ)
    (hcolumn : ∀ f, ∑ x, B x f = 3)
    (hGram : B * Bᵀ = (15 : ℤ) • (1 : Matrix (Fin 48) (Fin 48) ℤ) +
      Matrix.of (fun _ _ => (1 : ℤ)) - clebschConcreteDefect -
      clebschConcreteInternal * clebschConcreteInternal) : False := by
  obtain ⟨hs, hbalance, hH, hD⟩ := clebschConcrete_sign_data
  apply clebsch_signedGram_no_incidence B clebschConcreteInternal
    clebschConcreteDefect clebschConcreteSign hs hbalance hcolumn
  · funext a
    exact hH a
  · funext a
    exact hD a
  · exact hGram

end Erdos85

#print axioms Erdos85.clebschConcrete_sign_data
#print axioms Erdos85.clebschConcrete_no_incidence
