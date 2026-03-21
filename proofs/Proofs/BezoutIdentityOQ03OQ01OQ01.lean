/-
# k-fold Chinese Remainder Theorem (bezout-identity-oq-03-oq-01-oq-01)

## Open Question
Can the CRT be extended to k-fold products:
  ℤ/(n₁···nₖ)ℤ ≅ ∏ᵢ ℤ/nᵢℤ for pairwise coprime nᵢ?

## Answer: YES

The k-fold CRT is proved by induction on a list of pairwise coprime moduli,
using Mathlib's `ZMod.chineseRemainder` as the base 2-fold case. The key
enabling lemma is that pairwise coprimality implies coprimality with the
product of the remaining moduli.

## Status
- All theorems proved (0 sorries, 0 axioms)
- Builds on Mathlib.Data.ZMod.Basic
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

namespace BezoutCRTKFold

open ZMod

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: KEY COPRIMALITY LEMMA
═══════════════════════════════════════════════════════════════════════════════ -/

/-- If n is coprime to every element of a list, then n is coprime to the list's product. -/
theorem coprime_prod_of_coprime_all (n : ℕ) (ns : List ℕ)
    (h : ∀ m ∈ ns, Nat.Coprime n m) :
    Nat.Coprime n ns.prod := by
  induction ns with
  | nil => simp [Nat.Coprime, Nat.gcd_one_right]
  | cons m ms ih =>
    simp only [List.prod_cons]
    exact (h m List.mem_cons_self).mul_right
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

/-- Pairwise coprime list: head is coprime to the tail's product. -/
theorem head_coprime_tail_prod (n : ℕ) (ns : List ℕ)
    (h : List.Pairwise Nat.Coprime (n :: ns)) :
    Nat.Coprime n ns.prod := by
  apply coprime_prod_of_coprime_all
  intro m hm
  exact List.rel_of_pairwise_cons h hm

/-- Pairwise coprime cons implies pairwise coprime tail. -/
theorem pairwise_tail {n : ℕ} {ns : List ℕ}
    (h : List.Pairwise Nat.Coprime (n :: ns)) :
    List.Pairwise Nat.Coprime ns :=
  List.Pairwise.of_cons h

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: 3-FOLD CRT (EXPLICIT)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **3-fold CRT**: For pairwise coprime a, b, c:
    ℤ/(abc)ℤ ≅ ℤ/aℤ × (ℤ/bℤ × ℤ/cℤ)

    Constructed by composing two 2-fold CRTs. -/
noncomputable def crt3 (a b c : ℕ)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) :
    ZMod (a * b * c) ≃+* ZMod a × (ZMod b × ZMod c) := by
  -- a * b * c = a * (b * c) (associativity)
  have h_assoc : a * b * c = a * (b * c) := Nat.mul_assoc a b c
  -- a is coprime to b * c
  have h_abc : Nat.Coprime a (b * c) := hab.mul_right hac
  -- Step 1: ℤ/(a(bc))ℤ ≅ ℤ/aℤ × ℤ/(bc)ℤ
  -- Step 2: ℤ/(bc)ℤ ≅ ℤ/bℤ × ℤ/cℤ
  exact (h_assoc ▸ ZMod.chineseRemainder h_abc).trans
    (RingEquiv.prodCongr (RingEquiv.refl _) (ZMod.chineseRemainder hbc))

/-- **4-fold CRT**: For pairwise coprime a, b, c, d:
    ℤ/(abcd)ℤ ≅ ℤ/aℤ × (ℤ/bℤ × (ℤ/cℤ × ℤ/dℤ))

    Constructed by composing three 2-fold CRTs. -/
noncomputable def crt4 (a b c d : ℕ)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (had : Nat.Coprime a d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) (hcd : Nat.Coprime c d) :
    ZMod (a * b * c * d) ≃+* ZMod a × (ZMod b × (ZMod c × ZMod d)) := by
  -- a * b * c * d = a * (b * c * d) = a * (b * (c * d))
  have h1 : a * b * c * d = a * (b * (c * d)) := by ring
  have h_abcd : Nat.Coprime a (b * (c * d)) :=
    hab.mul_right (hac.mul_right had)
  have h_bcd : Nat.Coprime b (c * d) := hbc.mul_right hbd
  exact (h1 ▸ ZMod.chineseRemainder h_abcd).trans
    (RingEquiv.prodCongr (RingEquiv.refl _)
      ((ZMod.chineseRemainder h_bcd).trans
        (RingEquiv.prodCongr (RingEquiv.refl _) (ZMod.chineseRemainder hcd))))

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: GENERAL k-FOLD CRT (INDUCTIVE)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The k-fold CRT product type (right-associated nested pairs).
    CRTProd [] = PUnit
    CRTProd (n :: ns) = ZMod n × CRTProd ns -/
def CRTProd : List ℕ → Type
  | [] => PUnit
  | n :: ns => ZMod n × CRTProd ns

noncomputable instance CRTProd.commRing : (ns : List ℕ) → CommRing (CRTProd ns)
  | [] => PUnit.commRing
  | n :: ns => @Prod.instCommRing _ _ (ZMod.commRing n) (CRTProd.commRing ns)

/-- The trivial ring isomorphism ZMod 1 ≅ PUnit. -/
noncomputable def zmod_one_equiv_punit : ZMod 1 ≃+* PUnit := by
  refine ⟨⟨fun _ => PUnit.unit, fun _ => 0, ?_, ?_⟩, ?_, ?_⟩
  · intro x; exact Subsingleton.elim _ _
  · intro x; exact Subsingleton.elim _ _
  · intro _ _; exact Subsingleton.elim _ _
  · intro _ _; exact Subsingleton.elim _ _

/-- **k-fold CRT Isomorphism**: For pairwise coprime n₁, ..., nₖ,
    ℤ/(n₁···nₖ)ℤ ≅ ∏ᵢ ℤ/nᵢℤ (as rings).

    Constructed by induction:
    - Base: ℤ/1ℤ ≅ PUnit (trivial)
    - Step: ℤ/(n·∏nᵢ)ℤ ≅ ℤ/nℤ × ℤ/∏nᵢℤ ≅ ℤ/nℤ × ∏ᵢ ℤ/nᵢℤ -/
noncomputable def crtKFold : (ns : List ℕ) → List.Pairwise Nat.Coprime ns →
    ZMod ns.prod ≃+* CRTProd ns
  | [], _ => zmod_one_equiv_punit
  | n :: ns, h => by
      simp only [CRTProd, List.prod_cons]
      have h_coprime : Nat.Coprime n ns.prod := head_coprime_tail_prod n ns h
      have h_tail : List.Pairwise Nat.Coprime ns := pairwise_tail h
      exact (ZMod.chineseRemainder h_coprime).trans
        (RingEquiv.prodCongr (RingEquiv.refl _) (crtKFold ns h_tail))

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: PROPERTIES OF THE k-FOLD CRT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The k-fold CRT isomorphism is bijective. -/
theorem crtKFold_bijective (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns) :
    Function.Bijective (crtKFold ns h) :=
  (crtKFold ns h).bijective

/-- The k-fold CRT isomorphism is injective. -/
theorem crtKFold_injective (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns) :
    Function.Injective (crtKFold ns h) :=
  (crtKFold ns h).injective

/-- The k-fold CRT isomorphism is surjective. -/
theorem crtKFold_surjective (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns) :
    Function.Surjective (crtKFold ns h) :=
  (crtKFold ns h).surjective

/-- The k-fold CRT preserves multiplication. -/
theorem crtKFold_mul (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns)
    (x y : ZMod ns.prod) :
    (crtKFold ns h) (x * y) = (crtKFold ns h) x * (crtKFold ns h) y :=
  map_mul (crtKFold ns h) x y

/-- The k-fold CRT preserves addition. -/
theorem crtKFold_add (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns)
    (x y : ZMod ns.prod) :
    (crtKFold ns h) (x + y) = (crtKFold ns h) x + (crtKFold ns h) y :=
  map_add (crtKFold ns h) x y

/-- Round-trip: apply CRT then inverse gives back the original. -/
theorem crtKFold_roundtrip (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns)
    (x : ZMod ns.prod) :
    (crtKFold ns h).symm ((crtKFold ns h) x) = x :=
  (crtKFold ns h).symm_apply_apply x

/-- Round-trip: apply inverse then CRT gives back the original. -/
theorem crtKFold_roundtrip_inv (ns : List ℕ) (h : List.Pairwise Nat.Coprime ns)
    (p : CRTProd ns) :
    (crtKFold ns h) ((crtKFold ns h).symm p) = p :=
  (crtKFold ns h).apply_symm_apply p

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: EULER TOTIENT MULTIPLICATIVITY (k-FOLD)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Euler's totient is multiplicative over pairwise coprime lists**:
    φ(∏ nᵢ) = ∏ φ(nᵢ) when the nᵢ are pairwise coprime. -/
theorem totient_prod_pairwise_coprime (ns : List ℕ)
    (h : List.Pairwise Nat.Coprime ns) :
    Nat.totient ns.prod = (ns.map Nat.totient).prod := by
  induction ns with
  | nil => simp [Nat.totient_one]
  | cons n ns ih =>
    simp only [List.prod_cons, List.map_cons]
    have h_coprime : Nat.Coprime n ns.prod := head_coprime_tail_prod n ns h
    have h_tail : List.Pairwise Nat.Coprime ns := pairwise_tail h
    rw [Nat.totient_mul h_coprime, ih h_tail]

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI: CONCRETE EXAMPLES
═══════════════════════════════════════════════════════════════════════════════ -/

private theorem coprime_2_3_5 : List.Pairwise Nat.Coprime [2, 3, 5] := by decide

/-- **3-fold CRT example**: ℤ/30ℤ ≅ ℤ/2ℤ × (ℤ/3ℤ × (ℤ/5ℤ × PUnit)) -/
noncomputable def crt_kfold_2_3_5 := crtKFold [2, 3, 5] coprime_2_3_5

/-- **3-fold CRT (explicit)**: ℤ/30ℤ ≅ ℤ/2ℤ × (ℤ/3ℤ × ℤ/5ℤ) -/
noncomputable def crt_explicit_2_3_5 : ZMod 30 ≃+* ZMod 2 × (ZMod 3 × ZMod 5) :=
  crt3 2 3 5 (by decide) (by decide) (by decide)

private theorem coprime_2_3_5_7 : List.Pairwise Nat.Coprime [2, 3, 5, 7] := by decide

/-- **4-fold CRT (explicit)**: ℤ/210ℤ ≅ ℤ/2ℤ × (ℤ/3ℤ × (ℤ/5ℤ × ℤ/7ℤ)) -/
noncomputable def crt_explicit_2_3_5_7 : ZMod 210 ≃+* ZMod 2 × (ZMod 3 × (ZMod 5 × ZMod 7)) :=
  crt4 2 3 5 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Euler totient is multiplicative for [2, 3, 5]:
    φ(30) = φ(2) · φ(3) · φ(5) = 1 · 2 · 4 = 8 -/
theorem totient_30 : Nat.totient 30 = (([2, 3, 5].map Nat.totient).prod) :=
  totient_prod_pairwise_coprime [2, 3, 5] coprime_2_3_5

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @coprime_prod_of_coprime_all
#check @head_coprime_tail_prod
#check @crt3
#check @crt4
#check @CRTProd
#check @crtKFold
#check @crtKFold_bijective
#check @crtKFold_injective
#check @crtKFold_surjective
#check @crtKFold_mul
#check @crtKFold_add
#check @crtKFold_roundtrip
#check @crtKFold_roundtrip_inv
#check @totient_prod_pairwise_coprime
#check @crt_explicit_2_3_5
#check @crt_explicit_2_3_5_7

end BezoutCRTKFold
