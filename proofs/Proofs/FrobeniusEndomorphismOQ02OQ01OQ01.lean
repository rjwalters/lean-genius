/-
  The divisor-lattice fixed fields of the Frobenius: `fixedField⟨frob^d⟩ = 𝔽_{p^d}`.

  Let `K` be a finite field of characteristic `p`, an extension of its prime
  subfield `𝔽_p = ZMod p` of degree `n = [K : 𝔽_p]`, so `|K| = p ^ n`.  The
  parent entry (`FrobeniusEndomorphismOQ02OQ01`) computed the fixed points of the
  *generator* of the Galois group: the prime Frobenius `frob : x ↦ x ^ p` fixes
  exactly the prime subfield, `#{x // frob x = x} = p` (the bottom of the lattice,
  `d = 1`).  This file climbs the **whole divisor lattice**: for every divisor
  `d ∣ n` it identifies the fixed field of the cyclic subgroup `⟨frob ^ d⟩` and
  counts its points.

  The Galois group `Gal(K / 𝔽_p) = ⟨frob⟩` is cyclic of order `n`; its subgroups
  are exactly `⟨frob ^ d⟩` for `d ∣ n`, and the fundamental theorem of Galois
  theory matches them with the intermediate fields.  The map `frob ^ d` is the
  honest `p^d`-power map, so its fixed points are the solution set of
  `x ^ (p ^ d) = x` — the unique copy of `𝔽_{p^d}` inside `K`.

  ## Results

  * `frob_pow_apply` — the `d`-fold Frobenius is the `p^d`-power map,
    `(frob ^ d) x = x ^ (p ^ d)`, over the prime base (any `d`, no divisibility);
  * `frob_pow_fixed_iff` — hence its fixed points are the solutions of
    `x ^ (p ^ d) = x`;
  * `mem_fixedField_zpowers_frob_pow_iff` — being fixed by the whole cyclic
    subgroup `⟨frob ^ d⟩` is the same as being fixed by its generator `frob ^ d`
    (fixed-by-generator promotes to fixed-by-group in a cyclic group);
  * `fixedField_frob_pow_eq_pow_solutions` — the fixed field of `⟨frob ^ d⟩` is,
    as a set, exactly `{x | x ^ (p ^ d) = x}`;
  * `orderOf_frob_pow` — `orderOf (frob ^ d) = n / d` for `d ∣ n`;
  * `finrank_fixedField_frob_pow` — **the degree drop**:
    `[fixedField⟨frob^d⟩ : 𝔽_p] = d` for `d ∣ n` (Artin's
    `finrank_fixedField_eq_card` + the tower law);
  * `card_fixedField_frob_pow` / `card_frob_pow_fixedPoints` / `card_pow_eq_self`
    — the **point count** `p ^ d` for `d ∣ n`, in three equivalent guises
    (intermediate field, fixed-point subtype, solutions of `x ^ (p ^ d) = x`);
  * `fixedField_frob_pow_injOn_divisors` — distinct divisors give distinct
    subfields, so `d ↦ fixedField⟨frob^d⟩` is **injective on the divisors of `n`**
    — the forward half of the bijection `{subfields of 𝔽_{p^n}} ↔ {divisors of n}`.

  The parent's `d = n` (the whole group, fixed field `𝔽_p`) and `d = 1` (the
  trivial subgroup, fixed field `K`) are the two extreme rungs; this file fills in
  every rung between.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.  Built on the parent's
  generation/order lemmas (`frob_apply`, `orderOf_frob`) and the Mathlib results
  `IntermediateField.finrank_fixedField_eq_card`, `Module.finrank_mul_finrank`,
  `orderOf_pow_of_dvd`, and `Module.card_eq_pow_finrank`.
-/
import Mathlib
import Proofs.FrobeniusEndomorphismOQ02

namespace FrobeniusEndomorphismOQ02OQ01OQ01

open FrobeniusEndomorphismOQ02
open Module (finrank)

variable (p : ℕ) [Fact p.Prime]
variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

/-! ### Part I: the `d`-fold Frobenius is the `p^d`-power map -/

/-- **The `d`-fold Frobenius is the `p^d`-power map.** Over the prime base field,
iterating the prime Frobenius `x ↦ x ^ p` exactly `d` times gives `x ↦ x ^ (p^d)`.
A clean induction on `d`, valid for *every* `d` with no divisibility hypothesis. -/
theorem frob_pow_apply (d : ℕ) (x : K) : (frob p ^ d) x = x ^ (p ^ d) := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
      rw [pow_succ, AlgEquiv.mul_apply, frob_apply, ih, ← pow_mul, ← pow_succ']

/-- The fixed points of `frob ^ d` are exactly the solutions of `x ^ (p ^ d) = x`. -/
theorem frob_pow_fixed_iff (d : ℕ) (x : K) :
    (frob p ^ d) x = x ↔ x ^ (p ^ d) = x := by
  rw [frob_pow_apply]

/-! ### Part II: fixed by the cyclic subgroup ⟺ fixed by its generator -/

omit [Fintype K] in
/-- If `x` is fixed by an automorphism `a`, it is fixed by every power `a ^ k`.
The induction that promotes "fixed by the generator" to "fixed by the whole
cyclic group `⟨a⟩`". -/
theorem pow_fixed {a : K ≃ₐ[ZMod p] K} {x : K} (hx : a x = x) (k : ℕ) :
    (a ^ k) x = x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]

/-- Being fixed by the **whole** cyclic subgroup `⟨frob ^ d⟩` is the same as being
fixed by its generator `frob ^ d`.  The `←` direction promotes a single fixed point
to all powers via `pow_fixed`; the `→` direction just evaluates at the generator. -/
theorem mem_fixedField_zpowers_frob_pow_iff (d : ℕ) (x : K) :
    x ∈ IntermediateField.fixedField (Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K))
      ↔ (frob p ^ d) x = x := by
  rw [IntermediateField.mem_fixedField_iff]
  constructor
  · intro h
    exact h _ (Subgroup.mem_zpowers _)
  · intro hx g hg
    obtain ⟨k, rfl⟩ :=
      (Submonoid.mem_powers_iff g (frob p ^ d)).mp (mem_powers_iff_mem_zpowers.mpr hg)
    exact pow_fixed p hx k

/-- **The fixed field of `⟨frob ^ d⟩` is, as a set, the solution set of
`x ^ (p ^ d) = x`** — the unique copy of `𝔽_{p^d}` inside `K`. -/
theorem fixedField_frob_pow_eq_pow_solutions (d : ℕ) :
    (IntermediateField.fixedField (Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K)) : Set K)
      = {x : K | x ^ (p ^ d) = x} := by
  ext x
  rw [SetLike.mem_coe, Set.mem_setOf_eq, mem_fixedField_zpowers_frob_pow_iff p d x]
  exact frob_pow_fixed_iff p d x

/-! ### Part III: order, degree, and the point count `p^d` for `d ∣ n` -/

/-- The degree `n = [K : 𝔽_p]` is positive (a finite field has at least two
elements). -/
theorem finrank_pos : 0 < finrank (ZMod p) K := by
  rcases Nat.eq_zero_or_pos (finrank (ZMod p) K) with h | h
  · exfalso
    have hcard : p ^ finrank (ZMod p) K = Fintype.card K := FiniteField.pow_finrank_eq_card p K
    rw [h, pow_zero] at hcard
    have := Fintype.one_lt_card (α := K)
    omega
  · exact h

/-- **The order of `frob ^ d` is `n / d`** for a divisor `d ∣ n`.  In the cyclic
group `⟨frob⟩` of order `n`, the subgroup generated by `frob ^ d` has order
`n / d`. -/
theorem orderOf_frob_pow {d : ℕ} (hd : d ∣ finrank (ZMod p) K) (hd0 : d ≠ 0) :
    orderOf (frob p ^ d : K ≃ₐ[ZMod p] K) = finrank (ZMod p) K / d := by
  have hdvd : d ∣ orderOf (frob p : K ≃ₐ[ZMod p] K) := by rw [orderOf_frob]; exact hd
  rw [orderOf_pow_of_dvd hd0 hdvd, orderOf_frob]

/-- **The degree drop.** For a divisor `d ∣ n`, the fixed field of `⟨frob ^ d⟩` has
degree exactly `d` over the prime subfield: `[fixedField⟨frob^d⟩ : 𝔽_p] = d`.

Artin's theorem `finrank_fixedField_eq_card` gives `[K : fixedField⟨frob^d⟩] =
#⟨frob^d⟩ = n / d`; the tower law `[K : 𝔽_p] = [fixedField : 𝔽_p] · [K : fixedField]`
then forces `[fixedField : 𝔽_p] = d`. -/
theorem finrank_fixedField_frob_pow {d : ℕ} (hd : d ∣ finrank (ZMod p) K) (hd0 : d ≠ 0) :
    finrank (ZMod p)
        (IntermediateField.fixedField (Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K))) = d := by
  set n := finrank (ZMod p) K with hn
  set H := Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K) with hH
  -- `[K : fixedField H] = #H = orderOf (frob^d) = n / d`
  have hcardH : finrank (IntermediateField.fixedField H) K = n / d := by
    rw [IntermediateField.finrank_fixedField_eq_card H, Nat.card_zpowers, orderOf_frob_pow p hd hd0]
  -- tower law: `[fixedField H : 𝔽_p] · [K : fixedField H] = [K : 𝔽_p] = n`
  have htower :
      finrank (ZMod p) (IntermediateField.fixedField H)
          * finrank (IntermediateField.fixedField H) K = n :=
    Module.finrank_mul_finrank (ZMod p) (IntermediateField.fixedField H) K
  rw [hcardH] at htower
  -- `d · (n / d) = n`, and `n / d > 0`, so cancel
  have hdn : d * (n / d) = n := Nat.mul_div_cancel' hd
  have hpos : 0 < n / d :=
    Nat.div_pos (Nat.le_of_dvd (finrank_pos p) hd) (Nat.pos_of_ne_zero hd0)
  have key : finrank (ZMod p) (IntermediateField.fixedField H) * (n / d) = d * (n / d) :=
    htower.trans hdn.symm
  exact Nat.eq_of_mul_eq_mul_right hpos key

/-- **The point count, intermediate-field form.** For `d ∣ n` the fixed field of
`⟨frob ^ d⟩` has exactly `p ^ d` elements: it is the copy of `𝔽_{p^d}`. -/
theorem card_fixedField_frob_pow {d : ℕ} (hd : d ∣ finrank (ZMod p) K) (hd0 : d ≠ 0) :
    Nat.card (IntermediateField.fixedField (Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K)))
      = p ^ d := by
  haveI : Fintype (IntermediateField.fixedField
      (Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K))) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card,
    finrank_fixedField_frob_pow p hd hd0]

/-- **The point count, fixed-point-subtype form.** For `d ∣ n` the Frobenius power
`frob ^ d` has exactly `p ^ d` fixed points. -/
theorem card_frob_pow_fixedPoints {d : ℕ} (hd : d ∣ finrank (ZMod p) K) (hd0 : d ≠ 0) :
    Nat.card {x : K // (frob p ^ d) x = x} = p ^ d := by
  have e : (IntermediateField.fixedField (Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K)))
      ≃ {x : K // (frob p ^ d) x = x} :=
    Equiv.subtypeEquivRight (mem_fixedField_zpowers_frob_pow_iff p d)
  rw [← Nat.card_congr e, card_fixedField_frob_pow p hd hd0]

/-- **The point count, polynomial form.** For `d ∣ n` the equation `x ^ (p ^ d) = x`
has exactly `p ^ d` solutions in `K` — the classical statement that `X^{p^d} - X`
splits with `p^d` distinct roots precisely when `𝔽_{p^d} ⊆ K`, i.e. when `d ∣ n`. -/
theorem card_pow_eq_self {d : ℕ} (hd : d ∣ finrank (ZMod p) K) (hd0 : d ≠ 0) :
    Nat.card {x : K // x ^ (p ^ d) = x} = p ^ d := by
  have e : {x : K // x ^ (p ^ d) = x} ≃ {x : K // (frob p ^ d) x = x} :=
    Equiv.subtypeEquivRight (fun x => (frob_pow_fixed_iff p d x).symm)
  rw [Nat.card_congr e, card_frob_pow_fixedPoints p hd hd0]

/-! ### Part IV: injectivity over the divisor lattice -/

/-- **Distinct divisors give distinct subfields.** The assignment
`d ↦ fixedField⟨frob^d⟩` is injective on the divisors of `n = [K : 𝔽_p]`: this is
the forward (injective) half of the Galois bijection
`{subfields of 𝔽_{p^n}} ↔ {divisors of n}`.  Injectivity is read off the point
count `p ^ d`, since `d ↦ p ^ d` is injective for `p ≥ 2`. -/
theorem fixedField_frob_pow_injOn_divisors :
    Set.InjOn
      (fun d => IntermediateField.fixedField (Subgroup.zpowers (frob p ^ d : K ≃ₐ[ZMod p] K)))
      {d : ℕ | d ∣ finrank (ZMod p) K} := by
  have hn0 : finrank (ZMod p) K ≠ 0 := (finrank_pos p).ne'
  intro a ha b hb hab
  simp only [Set.mem_setOf_eq] at ha hb
  have ha0 : a ≠ 0 := fun h => hn0 (Nat.eq_zero_of_zero_dvd (h ▸ ha))
  have hb0 : b ≠ 0 := fun h => hn0 (Nat.eq_zero_of_zero_dvd (h ▸ hb))
  have hab' : IntermediateField.fixedField (Subgroup.zpowers (frob p ^ a : K ≃ₐ[ZMod p] K))
      = IntermediateField.fixedField (Subgroup.zpowers (frob p ^ b : K ≃ₐ[ZMod p] K)) := hab
  have hcard : (p : ℕ) ^ a = p ^ b := by
    rw [← card_fixedField_frob_pow p ha ha0, ← card_fixedField_frob_pow p hb hb0, hab']
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard

end FrobeniusEndomorphismOQ02OQ01OQ01

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms FrobeniusEndomorphismOQ02OQ01OQ01.frob_pow_apply
#print axioms FrobeniusEndomorphismOQ02OQ01OQ01.finrank_fixedField_frob_pow
#print axioms FrobeniusEndomorphismOQ02OQ01OQ01.card_pow_eq_self
#print axioms FrobeniusEndomorphismOQ02OQ01OQ01.fixedField_frob_pow_injOn_divisors
