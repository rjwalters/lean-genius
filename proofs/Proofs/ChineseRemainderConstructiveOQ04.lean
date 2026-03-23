/-
Chinese Remainder Theorem for Arbitrary-Length Moduli Lists

Generalizes the CRT from fixed-size systems to arbitrary-length lists,
proved by induction on list structure. For pairwise coprime moduli
[m₁, ..., mₖ] and remainders [a₁, ..., aₖ], there exists x with
x ≡ aᵢ (mod mᵢ) for all i, unique modulo ∏mᵢ.

Extends ChineseRemainderConstructive.lean (2, 3, 4 moduli → arbitrary k).
-/
import Mathlib

namespace CRTList

open Nat

/-
## Definitions
-/

/-- Extract moduli from a system of congruences (remainder, modulus) -/
def moduli (sys : List (ℕ × ℕ)) : List ℕ := sys.map Prod.snd

/-- Product of all moduli -/
def moduliProd (sys : List (ℕ × ℕ)) : ℕ := (moduli sys).prod

/-- A number x satisfies all congruences in the system -/
def Satisfies (x : ℕ) (sys : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ sys, x ≡ p.1 [MOD p.2]

/-
## Helper Lemmas
-/

/-- Coprime to every element implies coprime to their product -/
lemma coprime_prod_of_forall (m : ℕ) (ms : List ℕ)
    (h : ∀ n ∈ ms, Nat.Coprime m n) : Nat.Coprime m ms.prod := by
  induction ms with
  | nil =>
    change Nat.gcd m 1 = 1
    exact Nat.gcd_one_right m
  | cons n ns ih =>
    rw [List.prod_cons]
    have h1 : Nat.Coprime m n := h n (List.mem_cons.mpr (Or.inl rfl))
    have h2 : Nat.Coprime m ns.prod := ih (fun k hk => h k (List.mem_cons.mpr (Or.inr hk)))
    exact h1.mul_right h2

/-- Each element of a list divides the list's product -/
lemma dvd_list_prod {a : ℕ} {l : List ℕ} (h : a ∈ l) : a ∣ l.prod := by
  induction l with
  | nil => exact nomatch h
  | cons b bs ih =>
    rw [List.prod_cons]
    rcases List.mem_cons.mp h with rfl | hbs
    · exact dvd_mul_right a bs.prod
    · exact dvd_mul_of_dvd_right (ih hbs) b

/-- Weaken modular equation through divisibility -/
private lemma modEq_of_dvd {m n a b : ℕ} (hd : m ∣ n) (h : a ≡ b [MOD n]) :
    a ≡ b [MOD m] := by
  obtain ⟨k, rfl⟩ := hd
  exact Nat.ModEq.of_mul_right k h

/-
## Main Theorems
-/

/-- **CRT for lists (existence)**: For any system of congruences with
    pairwise coprime moduli, a simultaneous solution exists. -/
theorem crt_list (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime) :
    ∃ x, Satisfies x sys := by
  induction sys with
  | nil => exact ⟨0, fun _ h => nomatch h⟩
  | cons pair rest ih =>
    -- Decompose pairwise coprimality of (pair.2 :: moduli rest)
    have hmod : moduli (pair :: rest) = pair.2 :: moduli rest := by simp [moduli]
    rw [hmod] at hpc
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpc
    -- By induction, a solution y exists for the tail system
    obtain ⟨y, hy⟩ := ih htail
    -- pair.2 is coprime to the product of remaining moduli
    have hcop : Nat.Coprime pair.2 (moduli rest).prod :=
      coprime_prod_of_forall pair.2 (moduli rest) hhead
    -- Apply two-moduli CRT: find x ≡ pair.1 [MOD pair.2] and x ≡ y [MOD prod]
    let sol := Nat.chineseRemainder hcop pair.1 y
    refine ⟨sol.val, fun p hp => ?_⟩
    rcases List.mem_cons.mp hp with rfl | hrest
    · -- Head: sol ≡ pair.1 [MOD pair.2] directly from CRT
      exact sol.property.1
    · -- Tail: sol ≡ y [MOD prod], and p.2 | prod, so sol ≡ y ≡ p.1 [MOD p.2]
      have hmem : p.2 ∈ moduli rest := List.mem_map.mpr ⟨p, hrest, rfl⟩
      exact (modEq_of_dvd (dvd_list_prod hmem) sol.property.2).trans (hy p hrest)

/-- **CRT for lists (uniqueness)**: Any two solutions are congruent modulo
    the product of all moduli. -/
theorem crt_list_unique (sys : List (ℕ × ℕ))
    (hpc : (moduli sys).Pairwise Nat.Coprime)
    {x y : ℕ} (hx : Satisfies x sys) (hy : Satisfies y sys) :
    x ≡ y [MOD moduliProd sys] := by
  induction sys with
  | nil =>
    -- moduliProd [] = 1, and x ≡ y [MOD 1] is trivial
    change x % 1 = y % 1
    omega
  | cons pair rest ih =>
    have hmod : moduli (pair :: rest) = pair.2 :: moduli rest := by simp [moduli]
    rw [hmod] at hpc
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hpc
    -- x ≡ pair.1 ≡ y [MOD pair.2], so x ≡ y [MOD pair.2]
    have hxy_m : x ≡ y [MOD pair.2] :=
      (hx pair (List.mem_cons.mpr (Or.inl rfl))).trans
        (hy pair (List.mem_cons.mpr (Or.inl rfl))).symm
    -- By induction: x ≡ y [MOD moduliProd rest]
    have hxy_rest : x ≡ y [MOD moduliProd rest] :=
      ih htail
        (fun p hp => hx p (List.mem_cons.mpr (Or.inr hp)))
        (fun p hp => hy p (List.mem_cons.mpr (Or.inr hp)))
    -- Combine: coprime moduli give x ≡ y [MOD pair.2 * moduliProd rest]
    have hcop : Nat.Coprime pair.2 (moduli rest).prod :=
      coprime_prod_of_forall pair.2 (moduli rest) hhead
    have hprod : moduliProd (pair :: rest) = pair.2 * moduliProd rest := by
      simp [moduliProd, moduli, List.prod_cons]
    rw [hprod]
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hxy_m, hxy_rest⟩

/-
## Concrete Examples
-/

/-- The classic Sunzi problem: x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7).
    Solution: x = 23. -/
example : Satisfies 23 [(2, 3), (3, 5), (2, 7)] := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> native_decide

/-- The Sunzi moduli are pairwise coprime -/
example : (moduli [(2, 3), (3, 5), (2, 7)]).Pairwise Nat.Coprime := by
  simp [moduli]; native_decide

/-- Four-moduli example: x ≡ 1 (mod 2), x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 4 (mod 7).
    Solution: x = 53. -/
example : Satisfies 53 [(1, 2), (2, 3), (3, 5), (4, 7)] := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> native_decide

/-- Six-moduli example using first six primes, all remainders 1.
    Solution: x = 1. -/
example : Satisfies 1 [(1, 2), (1, 3), (1, 5), (1, 7), (1, 11), (1, 13)] := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> native_decide

end CRTList
