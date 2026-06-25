import Mathlib.Tactic
import Proofs.BurnsideCountingOQ04OQ02

/-
# Burnside Counting, OQ-04 → OQ-02 → OQ-02: the reflection half (odd `n`)

The parent file `BurnsideCountingOQ04OQ02OQ01` evaluated the **rotation half** of the dihedral
Burnside sum as the gcd-cycle sum `∑_i 2^{gcd(n,i)}`.  This file evaluates the **reflection
half**

      ∑_{i ∈ ZMod n} |Fix(sr i)|

for **odd** `n`, completing the closed form `b(n) = (rotations + reflections)/(2n)` in that case.

## The reflection involution

A reflection `sr i` acts on positions by `p ↦ -i - p` (the parent's `posPerm_sr = subLeft (-i)`),
which is the **involution** `refl i`.  A colouring is fixed by `sr i` exactly when it is constant
on the `refl i`-orbits.  Counting the invariant `2`-colourings of *any* involution `σ` gives

      |{c : α → Fin 2 // c ∘ σ = c}|  =  2 ^ ((|α| + |Fix σ|) / 2)

(`card_invariant_colorings_involutive`): the orbits are fixed points (singletons) and transposed
pairs, so `|α| = |Fix σ| + 2·(pairs)` and the number of orbits is `(|α| + |Fix σ|)/2`.

## Odd `n`

The fixed points of `refl i` are the solutions of `2p = -i`.  For odd `n`, `2` is a unit in
`ZMod n`, so there is exactly **one** fixed point for every `i` (`reflFix_odd`); hence every
reflection fixes `2^{(n+1)/2}` colourings and

      ∑_{i ∈ ZMod n} |Fix(sr i)|  =  n · 2^{(n+1)/2}            (`reflection_sum_odd`).

The even-`n` count (`2^{n/2+1}` and `2^{n/2}` over the two reflection classes) is the documented
follow-up; the general per-reflection count `card_fixedBy_reflection` below applies uniformly and
is the single ingredient that remains to be specialised by parity.

`#print axioms` on the headlines confirms only `propext, Classical.choice, Quot.sound`.
-/

namespace BurnsideCountingOQ04OQ02OQ02

open Finset MulAction BurnsideCountingOQ04OQ02

variable {n : ℕ}

/-! ### Unfolding the reflection action -/

/-- The reflection `sr i` acts on a colouring by `(sr i • c) p = c (-i - p)`.  Reads off the
parent's `smul_apply` at `g = sr i`, where `ρ (sr i) = Equiv.subLeft (-i)`, an involution. -/
theorem reflection_smul_apply (i : ZMod n) (c : Coloring n) (p : ZMod n) :
    ((DihedralGroup.sr i : DihedralGroup n) • c) p = c (-i - p) := by
  rw [smul_apply]
  congr 1
  have hρ : (ρ (DihedralGroup.sr i) : Equiv.Perm (Pos n)) = Equiv.subLeft (-i) := rfl
  rw [hρ, Equiv.symm_apply_eq]
  show p = -i - (-i - p)
  ring

/-- A colouring is fixed by the reflection `sr i` iff it is symmetric about the axis:
`c (-i - p) = c p`. -/
theorem fixed_iff_symm (i : ZMod n) (c : Coloring n) :
    (DihedralGroup.sr i : DihedralGroup n) • c = c ↔ ∀ p, c (-i - p) = c p := by
  constructor
  · intro h p
    have := congrFun h p
    rwa [reflection_smul_apply] at this
  · intro h
    funext p
    rw [reflection_smul_apply]
    exact h p

/-! ### The reflection involution on positions -/

/-- The position involution induced by the reflection `sr i`: `refl i p = -i - p`. -/
def refl (i : ZMod n) : ZMod n → ZMod n := fun p => -i - p

/-- `refl i` is an involution: `-i - (-i - p) = p`. -/
theorem refl_involutive (i : ZMod n) : Function.Involutive (refl i) := by
  intro p
  show -i - (-i - p) = p
  ring

/-! ### Counting invariant 2-colourings of an arbitrary involution

The orbits of an involution `σ` are singletons (fixed points) and transposed pairs.  We index
`α` by `ℕ` and pick the smaller-indexed element of each orbit as its representative; an invariant
colouring is freely determined by its values on the representatives.  The representatives are
`{a : f a ≤ f (σ a)}`, whose size is `(|α| + |Fix σ|)/2` because the non-fixed points split
evenly (via `σ`) between `f a < f (σ a)` and `f (σ a) < f a`. -/

/-- **Invariant `2`-colourings of an involution.**  For an involution `σ` on a finite type,
the number of `2`-colourings constant on `σ`-orbits is `2^{(|α| + |Fix σ|)/2}`. -/
theorem card_invariant_colorings_involutive {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α → α) (hσ : Function.Involutive σ) :
    Fintype.card {c : α → Fin 2 // ∀ a, c (σ a) = c a}
      = 2 ^ ((Fintype.card α + (univ.filter (fun a => σ a = a)).card) / 2) := by
  classical
  -- injective index function to ℕ
  let f : α → ℕ := fun a => (Fintype.equivFin α a).val
  have hf_inj : Function.Injective f := fun a b h => (Fintype.equivFin α).injective (Fin.ext h)
  -- the representative of each orbit (smaller index)
  let rep : α → α := fun a => if f a ≤ f (σ a) then a else σ a
  have hrep_def : ∀ a, rep a = if f a ≤ f (σ a) then a else σ a := fun _ => rfl
  set R : Finset α := univ.filter (fun a => f a ≤ f (σ a)) with hR
  have hrepR : ∀ a, rep a ∈ R := by
    intro a
    rw [hR, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    simp only [hrep_def]
    by_cases h : f a ≤ f (σ a)
    · rw [if_pos h]; exact h
    · rw [if_neg h, hσ a]; omega
  have hrep_symm : ∀ a, rep (σ a) = rep a := by
    intro a
    simp only [hrep_def, hσ a]
    rcases lt_trichotomy (f a) (f (σ a)) with h | h | h
    · rw [if_neg (show ¬ f (σ a) ≤ f a by omega), if_pos h.le]
    · have heq : a = σ a := hf_inj h
      rw [if_pos (le_of_eq h.symm), if_pos (le_of_eq h)]; exact heq.symm
    · rw [if_pos h.le, if_neg (show ¬ f a ≤ f (σ a) by omega)]
  have hrep_mem : ∀ a, a ∈ R → rep a = a := by
    intro a ha
    rw [hR, mem_filter] at ha
    rw [hrep_def, if_pos ha.2]
  have hrep_color : ∀ (c : {c : α → Fin 2 // ∀ a, c (σ a) = c a}) a, c.1 (rep a) = c.1 a := by
    intro c a
    rw [hrep_def]
    by_cases h : f a ≤ f (σ a)
    · rw [if_pos h]
    · rw [if_neg h]; exact c.2 a
  -- the bijection: invariant colourings ≃ functions on representatives
  have ecard : Fintype.card {c : α → Fin 2 // ∀ a, c (σ a) = c a}
      = Fintype.card (R → Fin 2) := by
    apply Fintype.card_congr
    refine
    { toFun := fun c r => c.1 r.1
      invFun := fun g => ⟨fun a => g ⟨rep a, hrepR a⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro a
      show g ⟨rep (σ a), hrepR (σ a)⟩ = g ⟨rep a, hrepR a⟩
      congr 1
      exact Subtype.ext (hrep_symm a)
    · intro c
      apply Subtype.ext
      funext a
      exact hrep_color c a
    · intro g
      funext r
      show g ⟨rep r.1, hrepR r.1⟩ = g r
      congr 1
      exact Subtype.ext (hrep_mem r.1 r.2)
  rw [ecard, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  congr 1
  -- count the representatives
  set Fix : Finset α := univ.filter (fun a => σ a = a) with hFix
  set L : Finset α := univ.filter (fun a => f a < f (σ a)) with hL
  set G : Finset α := univ.filter (fun a => f (σ a) < f a) with hG
  -- R = L ∪ Fix (disjoint)
  have hRLF : R.card = L.card + Fix.card := by
    have hdisj : Disjoint L Fix := by
      rw [hL, hFix, Finset.disjoint_filter]
      intro a _ h1 h2
      rw [h2] at h1
      exact absurd h1 (lt_irrefl _)
    have hpred : R = L ∪ Fix := by
      rw [hR, hL, hFix, ← Finset.filter_or]
      apply Finset.filter_congr
      intro a _
      constructor
      · intro h
        rcases lt_or_eq_of_le h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (hf_inj h').symm
      · rintro (h | h)
        · exact h.le
        · exact le_of_eq (congrArg f h).symm
    rw [hpred, Finset.card_union_of_disjoint hdisj]
  -- |R| + |G| = |α|
  have hRG : R.card + G.card = Fintype.card α := by
    have hGeq : G = univ.filter (fun a => ¬ f a ≤ f (σ a)) := by
      rw [hG]
      apply Finset.filter_congr
      intro a _
      exact not_le.symm
    rw [hR, hGeq, filter_card_add_filter_neg_card_eq_card, Finset.card_univ]
  -- |L| = |G| via σ
  have hLG : L.card = G.card := by
    rw [hL, hG]
    apply Finset.card_nbij' σ σ
    · intro a ha
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha ⊢
      rw [hσ a]; exact ha
    · intro a ha
      simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at ha ⊢
      rw [hσ a]; exact ha
    · intro a _; exact hσ a
    · intro a _; exact hσ a
  omega

/-! ### The per-reflection fixed-colouring count -/

/-- The number of positions fixed by `refl i`, i.e. solutions of `2p = -i`. -/
def reflFix [NeZero n] (i : ZMod n) : ℕ := (univ.filter (fun p : ZMod n => refl i p = p)).card

/-- **Per-reflection count.**  The number of colourings fixed by `sr i` is `2^{(n + reflFix i)/2}`:
they are the `2`-colourings invariant under the involution `refl i`. -/
theorem card_fixedBy_reflection [NeZero n] (i : ZMod n) :
    Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = 2 ^ ((n + reflFix i) / 2) := by
  classical
  have e : ↥(fixedBy (Coloring n) (DihedralGroup.sr i))
      ≃ {c : Coloring n // ∀ p, c (refl i p) = c p} :=
    Equiv.subtypeEquivRight (fun c => by rw [mem_fixedBy]; exact fixed_iff_symm i c)
  rw [Fintype.card_congr e, card_invariant_colorings_involutive (refl i) (refl_involutive i),
    ZMod.card]
  rfl

/-! ### Odd `n`: every reflection fixes `2^{(n+1)/2}` colourings -/

/-- For odd `n`, the involution `refl i` has a **unique** fixed point (`2` is a unit in `ZMod n`),
so `reflFix i = 1`. -/
theorem reflFix_odd [NeZero n] (hn : Odd n) (i : ZMod n) : reflFix i = 1 := by
  -- `2` is a unit in `ZMod n` for odd `n`
  have h2unit : IsUnit (2 : ZMod n) := by
    have h2 : (2 : ZMod n) = ((2 : ℕ) : ZMod n) := by norm_cast
    rw [h2, ZMod.isUnit_iff_coprime]
    exact Nat.coprime_two_left.mpr hn
  obtain ⟨u, hu⟩ := h2unit
  -- multiplication by the unit `2` is a bijection, so `2p = -i` has a unique solution
  have hbij : Function.Bijective (fun p : ZMod n => (2 : ZMod n) * p) := by
    have hb := Units.mulLeft_bijective u
    rwa [hu] at hb
  obtain ⟨p₀, hp₀, huniq⟩ := hbij.existsUnique (-i)
  -- `refl i p = p` is exactly `2p = -i`
  have hcond : ∀ p : ZMod n, refl i p = p ↔ (2 : ZMod n) * p = -i := by
    intro p
    simp only [refl]
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  rw [reflFix, Finset.card_eq_one]
  refine ⟨p₀, ?_⟩
  ext p
  simp only [mem_filter, mem_univ, true_and, mem_singleton, hcond]
  constructor
  · intro h; exact huniq p h
  · intro h; subst h; exact hp₀

/-- **The reflection half for odd `n`.**

      ∑_{i ∈ ZMod n} |Fix(sr i)|  =  n · 2^{(n+1)/2}. -/
theorem reflection_sum_odd [NeZero n] (hn : Odd n) :
    ∑ i : ZMod n, Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = n * 2 ^ ((n + 1) / 2) := by
  have h1 : ∀ i : ZMod n,
      Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i)) = 2 ^ ((n + 1) / 2) := by
    intro i
    rw [card_fixedBy_reflection, reflFix_odd hn i]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul]

end BurnsideCountingOQ04OQ02OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ04OQ02OQ02.card_invariant_colorings_involutive
#print axioms BurnsideCountingOQ04OQ02OQ02.card_fixedBy_reflection
#print axioms BurnsideCountingOQ04OQ02OQ02.reflection_sum_odd
