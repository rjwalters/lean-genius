/-
Chinese Remainder Theorem — Minimal Non-Negative Solution (OQ-04-OQ-04)

Extends ChineseRemainderConstructiveOQ04.lean with the canonical minimal representative:
for any system of congruences with pairwise coprime positive moduli,
there is a unique solution in [0, M) where M = product of all moduli.

This is the n-moduli analogue of ZMod.val: the CRT isomorphism
  ℤ/M ≅ ℤ/m₁ × ... × ℤ/mₖ
gives a unique representative in {0, ..., M-1} for each tuple of residues.

Main results:
- `satisfies_mod`: reducing any solution modulo M gives a valid solution
- `crt_list_minimal_exists`: existence of solution in [0, M)
- `crt_list_minimal_unique`: uniqueness in [0, M)
- `crt_list_min`: combined ∃! theorem
-/

import Proofs.ChineseRemainderConstructiveOQ04

namespace CRTList

open Nat

/-! ## Reduction Lemma -/

/-- **Reduction Lemma**: If x satisfies the system, so does x % moduliProd sys.

    Each modulus m_i divides M = moduliProd sys, so for any congruence x ≡ a_i [MOD m_i]:
      (x % M) % m_i = x % m_i = a_i % m_i
    using the `mod_mod_of_dvd` chain. -/
lemma satisfies_mod {sys : List (ℕ × ℕ)} (x : ℕ) (hx : Satisfies x sys) :
    Satisfies (x % moduliProd sys) sys := by
  intro p hp
  have hmem : p.2 ∈ moduli sys := List.mem_map.mpr ⟨p, hp, rfl⟩
  have hdvd : p.2 ∣ moduliProd sys := dvd_list_prod hmem
  show x % moduliProd sys % p.2 = p.1 % p.2
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact hx p hp

/-! ## Minimal Non-Negative Solution -/

/-- **Existence**: Any CRT system with positive product modulus has a solution in [0, M). -/
theorem crt_list_minimal_exists (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime)
    (hM : 0 < moduliProd sys) :
    ∃ x < moduliProd sys, Satisfies x sys := by
  obtain ⟨y, hy⟩ := crt_list sys hpc
  exact ⟨y % moduliProd sys, Nat.mod_lt y hM, satisfies_mod y hy⟩

/-- **Uniqueness**: Two solutions both in [0, M) must be equal.

    By `crt_list_unique`, any two solutions satisfy x ≡ y [MOD M], i.e., x % M = y % M.
    Since x, y < M, we have x % M = x and y % M = y, so x = y. -/
theorem crt_list_minimal_unique (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime)
    (hM : 0 < moduliProd sys)
    {x y : ℕ} (hx : x < moduliProd sys) (hy : y < moduliProd sys)
    (hxs : Satisfies x sys) (hys : Satisfies y sys) :
    x = y := by
  -- crt_list_unique gives x ≡ y [MOD M], i.e., x % M = y % M
  have hmod : x % moduliProd sys = y % moduliProd sys := crt_list_unique sys hpc hxs hys
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod

/-- **Minimal CRT Theorem (∃!)**: For pairwise coprime positive moduli,
    there exists a unique solution in [0, moduliProd sys).

    This is the canonical form of the CRT: the system defines a unique element
    of ℤ/m₁ × ... × ℤ/mₖ, lifted to its minimal non-negative representative. -/
theorem crt_list_min (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime)
    (hM : 0 < moduliProd sys) :
    ∃! x, x < moduliProd sys ∧ Satisfies x sys := by
  obtain ⟨c, hclt, hcs⟩ := crt_list_minimal_exists sys hpc hM
  exact ⟨c, ⟨hclt, hcs⟩,
    fun y ⟨hyt, hys⟩ => crt_list_minimal_unique sys hpc hM hyt hclt hys hcs⟩

/-! ## Concrete Verification: The Sunzi Problem -/

/-- The classic Sunzi problem:
      x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7)
    has the unique minimal solution x = 23 (in [0, 105)). -/
theorem sunzi_minimal_solution :
    ∃! x, x < moduliProd [(2, 3), (3, 5), (2, 7)] ∧
          Satisfies x [(2, 3), (3, 5), (2, 7)] := by
  exact crt_list_min _ (by simp [moduli]; native_decide) (by native_decide)

theorem sunzi_solution_is_23 :
    23 < moduliProd [(2, 3), (3, 5), (2, 7)] ∧
    Satisfies 23 [(2, 3), (3, 5), (2, 7)] := by
  constructor
  · native_decide
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> native_decide

/-- Any minimal solution to the Sunzi system must equal 23. -/
theorem sunzi_unique :
    ∀ x < moduliProd [(2, 3), (3, 5), (2, 7)],
      Satisfies x [(2, 3), (3, 5), (2, 7)] → x = 23 := by
  intro x hx hs
  have hpc : (moduli [(2, 3), (3, 5), (2, 7)]).Pairwise Nat.Coprime := by
    simp [moduli]; native_decide
  have h23 := sunzi_solution_is_23
  exact crt_list_minimal_unique _ hpc (by native_decide) hx h23.1 hs h23.2

/-! ## Summary

The Minimal CRT theorem extends the list-CRT in two directions:

1. **Canonical form**: Each system of congruences has a unique "normal form"
   representative in [0, M), which is obtained by reducing any solution mod M.

2. **Effective computation**: Given any solution x (from `crt_list`),
   the minimal solution is `x % moduliProd sys`, computable in O(log M) time.

The key lemma `satisfies_mod` relies on:
- Each modulus m_i divides M = ∏ mᵢ (from `dvd_list_prod`)
- `Nat.mod_mod_of_dvd`: if m ∣ M then (x % M) % m = x % m
-/

end CRTList
