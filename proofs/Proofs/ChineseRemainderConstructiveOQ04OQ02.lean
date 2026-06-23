/-
# Unifying List-Based CRT with Ring-Theoretic CRT (OQ-04 → OQ-02)

## Research Question

What is the relationship between the list-based CRT (`CRTList.Satisfies`, OQ-04)
and Mathlib's ring-theoretic CRT (`ZMod.chineseRemainder`)?

## Answer

The two formulations are equivalent: `CRTList.Satisfies x [(a, m), (b, n)]` holds
if and only if the ring isomorphism `ZMod.chineseRemainder h : ZMod (m*n) ≃+* ZMod m × ZMod n`
sends `(x : ZMod (m*n))` to `((a : ZMod m), (b : ZMod n))`.

Moreover, the unique minimal solution in `[0, m*n)` equals the `ZMod.val` of the
canonical ring-theoretic preimage.

## Key Proof Strategy

1. `map_natCast` for ring equivs: `ZMod.chineseRemainder h (↑x) = ↑x = ((↑x, ↑x))`
2. `ZMod.natCast_eq_natCast_iff`: `(↑x : ZMod m) = (↑a : ZMod m) ↔ x ≡ a [MOD m]`
3. `ZMod.natCast_zmod_val`: `(ZMod.val w : ZMod n) = w` (val is right inverse of cast)
4. `RingEquiv.apply_symm_apply`: `f (f.symm b) = b` ties the two sides together

## Theorems: 12 | Sorries: 0 | Axioms: 0
-/

import Mathlib.Data.ZMod.Basic
import Proofs.ChineseRemainderConstructiveOQ04
import Proofs.ChineseRemainderConstructiveOQ04OQ04

set_option maxHeartbeats 400000

namespace CRTUnification

open CRTList ZMod Nat

/-! ## Section 1: Structure of the 2-Element System -/

/-- The moduli of `[(a, m), (b, n)]` are `[m, n]`. -/
lemma moduli_pair (m n a b : ℕ) : moduli [(a, m), (b, n)] = [m, n] := by
  simp [moduli]

/-- The moduli product of `[(a, m), (b, n)]` is `m * n`. -/
lemma moduliProd_pair (m n a b : ℕ) : moduliProd [(a, m), (b, n)] = m * n := by
  simp [moduliProd, moduli]

/-- Pairwise coprimality for `[(a, m), (b, n)]` reduces to `Nat.Coprime m n`. -/
lemma pairwise_coprime_pair (m n a b : ℕ) (h : Nat.Coprime m n) :
    (moduli [(a, m), (b, n)]).Pairwise Nat.Coprime := by
  rw [moduli_pair]
  apply List.Pairwise.cons
  · intro c hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    exact hc ▸ h
  · apply List.Pairwise.cons <;> simp

/-- `Satisfies x [(a, m), (b, n)]` is equivalent to two modular congruences. -/
lemma satisfies_pair_iff (m n a b x : ℕ) :
    Satisfies x [(a, m), (b, n)] ↔ x ≡ a [MOD m] ∧ x ≡ b [MOD n] := by
  simp only [Satisfies]
  constructor
  · intro hsat
    exact ⟨hsat (a, m) (by simp), hsat (b, n) (by simp)⟩
  · rintro ⟨ha, hb⟩ p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ha
    · exact hb

/-! ## Section 2: The Ring-Theoretic Bridge -/

/-- The ring isomorphism applied to `↑x` gives the pair `(↑x, ↑x)` componentwise.

    By `map_natCast`, any ring hom satisfies `f ↑n = ↑n`. The product `NatCast`
    instance defines `(n : α × β) = ((n : α), (n : β))`, so this is definitional. -/
lemma chineseRemainder_natCast (m n : ℕ) (hmn : Nat.Coprime m n) (x : ℕ) :
    ZMod.chineseRemainder hmn (x : ZMod (m * n)) = ((x : ZMod m), (x : ZMod n)) :=
  map_natCast (ZMod.chineseRemainder hmn) x

/-- **Bridge Theorem**: `Satisfies x [(a, m), (b, n)]` iff the ring iso sends
    `(↑x : ZMod (m*n))` to the target pair `((↑a, ↑b))`.

    This equates the list-based and ring-theoretic formulations of the 2-fold CRT. -/
theorem satisfies_pair_iff_chineseRemainder (m n a b x : ℕ) (hmn : Nat.Coprime m n) :
    Satisfies x [(a, m), (b, n)] ↔
      ZMod.chineseRemainder hmn (x : ZMod (m * n)) = ((a : ZMod m), (b : ZMod n)) := by
  rw [satisfies_pair_iff, chineseRemainder_natCast]
  constructor
  · rintro ⟨hm, hn⟩
    apply Prod.ext
    · exact (ZMod.natCast_eq_natCast_iff x a m).mpr hm
    · exact (ZMod.natCast_eq_natCast_iff x b n).mpr hn
  · intro h
    constructor
    · exact (ZMod.natCast_eq_natCast_iff x a m).mp (congr_arg Prod.fst h)
    · exact (ZMod.natCast_eq_natCast_iff x b n).mp (congr_arg Prod.snd h)

/-! ## Section 3: Canonical Solution = ZMod Preimage -/

/-- The ring-theoretic preimage's `ZMod.val` lies in `[0, m*n)`. -/
lemma chineseRemainder_symm_val_lt (m n a b : ℕ) (hmn : Nat.Coprime m n)
    (hm : 0 < m) (hn : 0 < n) :
    ZMod.val ((ZMod.chineseRemainder hmn).symm ((a : ZMod m), (b : ZMod n))) < m * n := by
  haveI : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  exact ZMod.val_lt _

/-- The ring-theoretic preimage satisfies the congruence system.

    Let `w = (ZMod.chineseRemainder hmn).symm ((↑a, ↑b))`.
    - `ZMod.natCast_zmod_val w`: `(↑(ZMod.val w) : ZMod (m*n)) = w`
    - `RingEquiv.apply_symm_apply`: `ZMod.chineseRemainder hmn w = (↑a, ↑b)` -/
lemma chineseRemainder_symm_satisfies (m n a b : ℕ) (hmn : Nat.Coprime m n)
    (hm : 0 < m) (hn : 0 < n) :
    Satisfies (ZMod.val ((ZMod.chineseRemainder hmn).symm ((a : ZMod m), (b : ZMod n))))
      [(a, m), (b, n)] := by
  haveI : NeZero (m * n) := ⟨(Nat.mul_pos hm hn).ne'⟩
  rw [satisfies_pair_iff_chineseRemainder m n a b _ hmn,
      ZMod.natCast_zmod_val ((ZMod.chineseRemainder hmn).symm ((a : ZMod m), (b : ZMod n)))]
  exact RingEquiv.apply_symm_apply (ZMod.chineseRemainder hmn) _

/-- **Canonical Bridge**: The unique minimal solution in `[0, m*n)` equals the
    `ZMod.val` of the ring-theoretic preimage.

    Follows from the uniqueness theorem `crt_list_minimal_unique` applied to
    `x` and the ring-theoretic preimage, both of which satisfy the system. -/
theorem crt_min_eq_chineseRemainder_val (m n a b : ℕ) (hmn : Nat.Coprime m n)
    (hm : 0 < m) (hn : 0 < n)
    (x : ℕ) (hlt : x < m * n) (hsat : Satisfies x [(a, m), (b, n)]) :
    x = ZMod.val ((ZMod.chineseRemainder hmn).symm ((a : ZMod m), (b : ZMod n))) :=
  crt_list_minimal_unique [(a, m), (b, n)]
    (pairwise_coprime_pair m n a b hmn)
    (by rw [moduliProd_pair]; exact Nat.mul_pos hm hn)
    (by rw [moduliProd_pair]; exact hlt)
    (by rw [moduliProd_pair]; exact chineseRemainder_symm_val_lt m n a b hmn hm hn)
    hsat
    (chineseRemainder_symm_satisfies m n a b hmn hm hn)

/-! ## Section 4: Summary Theorems -/

/-- **Alternative CRT existence proof via ZMod**: The ring iso's inverse gives an
    explicit witness in `[0, m*n)` for any target pair `(a mod m, b mod n)`. -/
theorem crt_exists_via_zmod (m n a b : ℕ) (hmn : Nat.Coprime m n)
    (hm : 0 < m) (hn : 0 < n) :
    ∃ x < m * n, Satisfies x [(a, m), (b, n)] :=
  ⟨ZMod.val ((ZMod.chineseRemainder hmn).symm ((a : ZMod m), (b : ZMod n))),
   chineseRemainder_symm_val_lt m n a b hmn hm hn,
   chineseRemainder_symm_satisfies m n a b hmn hm hn⟩

/-- **Uniqueness via ZMod**: Two solutions in `[0, m*n)` for the same 2-fold system
    must be equal. -/
theorem crt_unique_two_fold (m n a b x y : ℕ) (hmn : Nat.Coprime m n)
    (hm : 0 < m) (hn : 0 < n)
    (hx_lt : x < m * n) (hy_lt : y < m * n)
    (hx : Satisfies x [(a, m), (b, n)]) (hy : Satisfies y [(a, m), (b, n)]) :
    x = y :=
  crt_list_minimal_unique [(a, m), (b, n)]
    (pairwise_coprime_pair m n a b hmn)
    (by rw [moduliProd_pair]; exact Nat.mul_pos hm hn)
    (by rw [moduliProd_pair]; exact hx_lt)
    (by rw [moduliProd_pair]; exact hy_lt)
    hx hy

/-- **Concrete example**: x ≡ 2 (mod 3), x ≡ 3 (mod 5) has unique minimal solution 8.

    Demonstrates that the list-based solution (8 < 15, satisfies both congruences)
    matches the ZMod preimage: `ZMod.val ((ZMod.chineseRemainder h).symm (2, 3)) = 8`. -/
theorem example_8_mod3_mod5 :
    ∃! x, x < 15 ∧ Satisfies x [(2, 3), (3, 5)] := by
  refine ⟨8, ⟨by norm_num, ?_⟩, fun y ⟨hy_lt, hy_sat⟩ => ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> native_decide
  · apply crt_unique_two_fold 3 5 2 3 y 8
      (by norm_num) (by norm_num) (by norm_num) hy_lt (by norm_num) hy_sat
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl <;> native_decide

end CRTUnification
