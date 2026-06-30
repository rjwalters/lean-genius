/-
# k-fold CRT: Pi-type Ring Isomorphism (bezout-identity-oq-03-oq-01-oq-01-oq-03)

## Open Question
The parent file `BezoutIdentityOQ03OQ01OQ01.lean` proved the k-fold CRT in the
*list / nested-pair* form `ZMod ns.prod ≃+* CRTProd ns`, where `CRTProd` is a
right-associated tower of products ending in `PUnit`. Its third open question
asks to connect this to the canonical **dependent-product (Pi-type)** form:

  ℤ/(n₀·n₁···n_{k-1})ℤ  ≅  ∏_{i : Fin k} ℤ/nᵢℤ      (as rings)

indexed symmetrically by `Fin k`, where `ns : Fin k → ℕ` is pairwise coprime.

## Answer: YES

We build the isomorphism `crtPi` directly by induction on `k`:
- **Base** `k = 0`: the empty product is `1`, and `ZMod 1` together with the
  empty Pi-type `∀ i : Fin 0, _` are both subsingletons, hence canonically
  isomorphic.
- **Step** `k+1`: split off the head `ns 0`. The empty/`Fin.cons` decomposition
  `∏_{i : Fin (k+1)} nᵢ = n₀ · ∏_{i : Fin k} n_{i+1}` together with
  `head` coprime to the tail product lets us apply Mathlib's binary
  `ZMod.chineseRemainder`, recurse on the tail, and re-assemble via the
  `Fin.cons` ring isomorphism `Π_{Fin (k+1)} ≃+* (head) × Π_{Fin k}`.

This is the symmetric, reusable indexed form (no nested pairs / `PUnit` tail),
which is the standard statement of the Chinese Remainder Theorem.

## Status
- All theorems proved (0 sorries, 0 axioms, no `native_decide`).
- Builds on `Mathlib` only (self-contained; does not import the parent file).
-/
import Mathlib

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace BezoutCRTPi

open Finset

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: TWO STRUCTURAL RING ISOMORPHISMS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Any two subsingleton commutative rings are (uniquely) ring-isomorphic.
    Used for the empty (`k = 0`) base case of the CRT. -/
def ringEquivOfSubsingleton (A B : Type*) [CommRing A] [CommRing B]
    [Subsingleton A] [Subsingleton B] : A ≃+* B where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _

/-- **`Fin.cons` ring isomorphism**: a dependent product over `Fin (k+1)` splits
    as the head factor times the dependent product over the tail.

    The forward map `f ↦ (f 0, fun i => f i.succ)` is a ring homomorphism on the
    nose (operations are pointwise), so `map_mul'`/`map_add'` are `rfl`. The
    inverse is `Fin.cons`. -/
def finSplitRingEquiv {k : ℕ} (M : Fin (k + 1) → Type*) [∀ i, CommRing (M i)] :
    (∀ i : Fin (k + 1), M i) ≃+* M 0 × (∀ i : Fin k, M i.succ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv p := by
    ext
    · simp
    · simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: COPRIMALITY OF HEAD WITH TAIL PRODUCT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- For a pairwise-coprime family `ns : Fin (k+1) → ℕ`, the head `ns 0` is
    coprime to the product of the tail `∏ i : Fin k, ns i.succ`. -/
theorem head_coprime_tail_prod {k : ℕ} (ns : Fin (k + 1) → ℕ)
    (h : ∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) :
    Nat.Coprime (ns 0) (∏ i : Fin k, ns i.succ) := by
  apply Nat.Coprime.prod_right
  intro i _
  exact h 0 i.succ (Fin.succ_ne_zero i).symm

/-- The tail of a pairwise-coprime family is pairwise coprime. -/
theorem pairwise_tail {k : ℕ} (ns : Fin (k + 1) → ℕ)
    (h : ∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) :
    ∀ i j : Fin k, i ≠ j → Nat.Coprime (ns i.succ) (ns j.succ) := by
  intro i j hij
  exact h i.succ j.succ (fun he => hij (Fin.succ_injective k he))

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE k-FOLD CRT (PI-TYPE FORM)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **k-fold CRT, Pi-type form.** For a pairwise-coprime family
    `ns : Fin k → ℕ`,

      `ZMod (∏ i, ns i) ≃+* ∀ i, ZMod (ns i)`

    as rings. Constructed by induction on `k`. -/
def crtPi : (k : ℕ) → (ns : Fin k → ℕ) →
    (∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) →
    (ZMod (∏ i, ns i) ≃+* ∀ i, ZMod (ns i))
  | 0, ns, _ => by
      have hp : (∏ i : Fin 0, ns i) = 1 := by simp
      rw [hp]
      exact ringEquivOfSubsingleton _ _
  | k + 1, ns, h => by
      have hprod : (∏ i, ns i) = ns 0 * ∏ i : Fin k, ns i.succ :=
        Fin.prod_univ_succ ns
      have hco : Nat.Coprime (ns 0) (∏ i : Fin k, ns i.succ) :=
        head_coprime_tail_prod ns h
      -- recurse on the tail family
      have ih : ZMod (∏ i : Fin k, ns i.succ) ≃+* ∀ i : Fin k, ZMod (ns i.succ) :=
        crtPi k (fun i => ns i.succ) (pairwise_tail ns h)
      -- ZMod (∏) ≃ ZMod (ns 0) × ZMod (tail prod)  via binary CRT (with cast)
      have e1 : ZMod (∏ i, ns i) ≃+*
          ZMod (ns 0) × ZMod (∏ i : Fin k, ns i.succ) :=
        hprod ▸ ZMod.chineseRemainder hco
      -- spread the tail factor with the inductive hypothesis
      have e2 : ZMod (ns 0) × ZMod (∏ i : Fin k, ns i.succ) ≃+*
          ZMod (ns 0) × (∀ i : Fin k, ZMod (ns i.succ)) :=
        RingEquiv.prodCongr (RingEquiv.refl _) ih
      -- reassemble the Pi-type via the Fin.cons isomorphism
      have e3 : ZMod (ns 0) × (∀ i : Fin k, ZMod (ns i.succ)) ≃+*
          (∀ i, ZMod (ns i)) :=
        (finSplitRingEquiv (fun i => ZMod (ns i))).symm
      exact (e1.trans e2).trans e3

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: PROPERTIES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The Pi-type CRT is bijective. -/
theorem crtPi_bijective {k : ℕ} (ns : Fin k → ℕ)
    (h : ∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) :
    Function.Bijective (crtPi k ns h) :=
  (crtPi k ns h).bijective

/-- The Pi-type CRT preserves multiplication. -/
theorem crtPi_map_mul {k : ℕ} (ns : Fin k → ℕ)
    (h : ∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) (x y : ZMod (∏ i, ns i)) :
    crtPi k ns h (x * y) = crtPi k ns h x * crtPi k ns h y :=
  map_mul _ x y

/-- The Pi-type CRT preserves addition. -/
theorem crtPi_map_add {k : ℕ} (ns : Fin k → ℕ)
    (h : ∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) (x y : ZMod (∏ i, ns i)) :
    crtPi k ns h (x + y) = crtPi k ns h x + crtPi k ns h y :=
  map_add _ x y

/-- Round-trip identity (CRT then inverse). -/
theorem crtPi_symm_apply_apply {k : ℕ} (ns : Fin k → ℕ)
    (h : ∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) (x : ZMod (∏ i, ns i)) :
    (crtPi k ns h).symm (crtPi k ns h x) = x :=
  (crtPi k ns h).symm_apply_apply x

/-- **Cardinality consequence.** When every modulus is positive, the source
    `ZMod (∏ i, ns i)` and the target `∀ i, ZMod (ns i)` are finite of the same
    cardinality `∏ i, ns i`. This recovers `|ℤ/Nℤ| = ∏ |ℤ/nᵢℤ|`. -/
theorem crtPi_card {k : ℕ} (ns : Fin k → ℕ) (hpos : ∀ i, 0 < ns i)
    (h : ∀ i j, i ≠ j → Nat.Coprime (ns i) (ns j)) :
    Nat.card (∀ i, ZMod (ns i)) = ∏ i, ns i := by
  have hN : 0 < ∏ i, ns i := Finset.prod_pos (fun i _ => hpos i)
  haveI : NeZero (∏ i, ns i) := ⟨hN.ne'⟩
  -- transport cardinality across the ring equivalence
  have hbij := crtPi_bijective ns h
  have : Nat.card (∀ i, ZMod (ns i)) = Nat.card (ZMod (∏ i, ns i)) :=
    (Nat.card_eq_of_bijective _ hbij).symm
  rw [this]
  haveI : ∀ i, NeZero (ns i) := fun i => ⟨(hpos i).ne'⟩
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: CONCRETE EXAMPLE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Moduli `[2, 3, 5]` as a family `Fin 3 → ℕ`. -/
def ns235 : Fin 3 → ℕ := ![2, 3, 5]

theorem ns235_pairwise_coprime :
    ∀ i j : Fin 3, i ≠ j → Nat.Coprime (ns235 i) (ns235 j) := by
  decide

theorem ns235_prod : ∏ i, ns235 i = 30 := by decide

/-- **Concrete 3-fold CRT (Pi form):** `ℤ/30ℤ ≅ ∀ i : Fin 3, ZMod ([2,3,5] i)`. -/
def crt235 : ZMod (∏ i, ns235 i) ≃+* ∀ i, ZMod (ns235 i) :=
  crtPi 3 ns235 ns235_pairwise_coprime

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @ringEquivOfSubsingleton
#check @finSplitRingEquiv
#check @head_coprime_tail_prod
#check @pairwise_tail
#check @crtPi
#check @crtPi_bijective
#check @crtPi_map_mul
#check @crtPi_map_add
#check @crtPi_symm_apply_apply
#check @crtPi_card
#check @crt235

end BezoutCRTPi
