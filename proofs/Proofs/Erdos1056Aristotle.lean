/-
  Aristotle targets for Erdős Problem #1056
  Routine supporting lemmas for automated proof search.
  See Erdos1056Problem.lean for the main formalization.

  Main target: Prove Wilson's theorem constraint using Mathlib's
  ZMod.wilsons_lemma, bridging from ZMod to ℕ modular arithmetic.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result (Wilson's theorem) available in Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms
-/
import Mathlib.NumberTheory.Wilson
import Mathlib.Data.ZMod.Basic

open Finset

namespace Erdos1056Aristotle

/-- The product of [1, p) equals (p-1) factorial. -/
theorem ico_prod_eq_factorial (p : ℕ) (hp : p ≥ 1) :
    (Finset.Ico 1 p).prod id = Nat.factorial (p - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [show Finset.Ico 1 (m + 2) = Finset.Ico 1 (m + 1) ∪ {m + 1} from by
      ext x; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega]
    rw [Finset.prod_union (by
      rw [Finset.disjoint_left]
      intro x hx
      simp only [Finset.mem_Ico] at hx
      simp only [Finset.mem_singleton]
      omega)]
    rw [Finset.prod_singleton, id, ih (by omega), mul_comm, ← Nat.factorial_succ]

/-- Wilson's theorem in ℕ modular arithmetic:
    (p-1)! % p = p - 1 for any prime p.
    This bridges Mathlib's ZMod.wilsons_lemma to ℕ. -/
theorem wilson_nat (p : ℕ) (hp : Nat.Prime p) :
    Nat.factorial (p - 1) % p = p - 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have h := ZMod.wilsons_lemma p
  -- h : ((p-1)! : ZMod p) = -1
  -- Bridge via ZMod.val: val maps ZMod p → ℕ as canonical representative
  have h_lhs : ZMod.val ((Nat.factorial (p - 1) : ℕ) : ZMod p) =
      Nat.factorial (p - 1) % p := ZMod.val_natCast _ _
  have h_rhs : ZMod.val (-1 : ZMod p) = p - 1 := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
    simpa using ZMod.val_neg_one q
  calc Nat.factorial (p - 1) % p
      = ZMod.val ((↑(Nat.factorial (p - 1)) : ZMod p)) := h_lhs.symm
    _ = ZMod.val (-1 : ZMod p) := congr_arg ZMod.val h
    _ = p - 1 := h_rhs

/-- **Wilson's constraint for interval products:**
    For any prime p, (Finset.Ico 1 p).prod id % p = p - 1.
    This is the axiom wilson_constraint from Erdos1056Problem.lean. -/
theorem wilson_constraint (p : ℕ) (hp : Nat.Prime p) :
    (Finset.Ico 1 p).prod id % p = p - 1 := by
  rw [ico_prod_eq_factorial p hp.pos]
  exact wilson_nat p hp

end Erdos1056Aristotle
