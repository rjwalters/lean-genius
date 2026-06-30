import Mathlib

/-
# The augmentation sequence of `𝔽_p[ℤ/p]` does not split

This file answers the open question `maschke-theorem-oq-01-oq-01-oq-01`: identify the nilpotent
`g - 1` with a generator of the augmentation ideal and show that the short exact sequence

```
0 → ker ε → 𝔽_p[ℤ/p] → 𝔽_p → 0,      ε : ∑ a_h h ↦ ∑ a_h,
```

does **not** split as a sequence of `𝔽_p[ℤ/p]`-modules, recovering the parent entry's
`exists_submodule_no_complement` with the *named* witness `I = ker ε`.

## The argument

Maschke's theorem fails in characteristic `p` because complete reducibility fails: the
augmentation ideal `I = ker ε` has no `A`-module complement, where `A = 𝔽_p[ℤ/p]`.

Suppose, for contradiction, that `J` is a complement, so `A = I ⊕ J`.  Writing `1 = a + b`
with `a ∈ I`, `b ∈ J`, the augmentation gives `ε b = 1` (since `ε a = 0`).  The element
`b` is then a "section value": for the generator `g`,

* `g * b - b ∈ I`, because `ε (g * b - b) = ε g · ε b - ε b = 1 · 1 - 1 = 0`;
* `g * b - b ∈ J`, because `J` is an ideal and `b ∈ J`.

Hence `g * b - b ∈ I ⊓ J = ⊥`, i.e. `g * b = b`: the element `b` is **`g`-invariant**.

But a `g`-invariant element of the regular representation has *constant* coefficients
(multiplication by `g = [1]` cyclically shifts coordinates, so all coordinates are equal).
For such an element the augmentation is the sum of `p` equal coefficients, hence
`ε b = p · c = 0` in `𝔽_p`.  This contradicts `ε b = 1`.

The cyclic-shift structure of the regular representation — not just the existence of a
nilpotent — is what kills the splitting; the obstruction is uniform in the prime `p`.

## Main statements

* `MaschkeAugmentationNoSplit.aug_zero_of_g_mul_self` — a `g`-invariant element has
  augmentation zero (the heart of the obstruction).
* `MaschkeAugmentationNoSplit.augmentation_no_complement` — **the augmentation ideal
  `ker ε` has no complement**: the sequence `0 → ker ε → A → 𝔽_p → 0` does not split.
* `MaschkeAugmentationNoSplit.exists_submodule_no_complement` — the parent's conclusion,
  now with `ker ε` exhibited as the explicit witness.
-/

open scoped MonoidAlgebra
open MonoidAlgebra

namespace MaschkeAugmentationNoSplit

variable (p : ℕ) [hp : Fact p.Prime]

/-- The cyclic group `ℤ/p`, written multiplicatively so its group algebra is a
`MonoidAlgebra`. -/
abbrev G : Type := Multiplicative (ZMod p)

/-- The modular group algebra `A = 𝔽_p[ℤ/p]`. -/
abbrev A : Type := MonoidAlgebra (ZMod p) (G p)

/-- The standard generator `g = [1]`: the basis element indexed by `1 ∈ ℤ/p`. -/
noncomputable def g : A p :=
  MonoidAlgebra.single (Multiplicative.ofAdd (1 : ZMod p)) (1 : ZMod p)

/-- The **augmentation map** `ε : 𝔽_p[ℤ/p] → 𝔽_p`, `∑ a_h h ↦ ∑ a_h`, realised as the
algebra hom sending every group element to `1`. -/
noncomputable def ε : A p →ₐ[ZMod p] ZMod p :=
  MonoidAlgebra.lift (ZMod p) (G p) (ZMod p) 1

/-- `ε` sends a basis element `single a b` to its coefficient `b`. -/
@[simp] theorem ε_single (a : G p) (b : ZMod p) : ε p (MonoidAlgebra.single a b) = b := by
  simp [ε]

/-- The generator has augmentation `1`. -/
@[simp] theorem ε_g : ε p (g p) = 1 := by
  rw [g, ε_single]

/-- The augmentation is the sum of all coefficients (over the finite group). -/
theorem ε_eq_sum (y : A p) : ε p y = ∑ h : G p, y h := by
  rw [ε, lift_apply]
  simp only [MonoidHom.one_apply, smul_eq_mul, mul_one]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]

/-- Membership in the augmentation ideal `ker ε` is having augmentation `0`. -/
theorem mem_ker_iff (x : A p) :
    x ∈ RingHom.ker (ε p).toRingHom ↔ ε p x = 0 := by
  rw [RingHom.mem_ker]; rfl

/-- **Cyclic shift.** If `g * y = y`, then the coefficient of `y` at `(ofAdd 1)⁻¹ * h`
equals that at `h`, for every `h`. -/
theorem coeff_shift {y : A p} (hy : g p * y = y) (h : G p) :
    y ((Multiplicative.ofAdd (1 : ZMod p))⁻¹ * h) = y h := by
  have h1 : (g p * y) h = y h := by rw [hy]
  simp only [g, single_mul_apply, one_mul] at h1
  exact h1

/-- A `g`-invariant element has the *same* coefficient at every group element. -/
theorem coeff_const {y : A p} (hy : g p * y = y) (t : ZMod p) :
    y (Multiplicative.ofAdd t) = y (Multiplicative.ofAdd (0 : ZMod p)) := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  -- one step of the shift, phrased additively: coefficient at `s+1` equals at `s`
  have step : ∀ s : ZMod p,
      y (Multiplicative.ofAdd (s + 1)) = y (Multiplicative.ofAdd s) := by
    intro s
    have hs := coeff_shift p hy (Multiplicative.ofAdd (s + 1))
    have hsimp : (Multiplicative.ofAdd (1 : ZMod p))⁻¹ * Multiplicative.ofAdd (s + 1)
        = Multiplicative.ofAdd s := by
      rw [← ofAdd_neg, ← ofAdd_add]
      congr 1
      ring
    rw [hsimp] at hs
    exact hs.symm
  -- iterate the step from `0`
  have nat_const : ∀ n : ℕ,
      y (Multiplicative.ofAdd ((n : ZMod p))) = y (Multiplicative.ofAdd (0 : ZMod p)) := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have hcast : ((k + 1 : ℕ) : ZMod p) = (k : ZMod p) + 1 := by push_cast; ring
      rw [hcast, step (k : ZMod p), ih]
  -- every element of `ZMod p` is the cast of its value
  have ht : ((t.val : ℕ) : ZMod p) = t := ZMod.natCast_rightInverse t
  calc y (Multiplicative.ofAdd t)
      = y (Multiplicative.ofAdd ((t.val : ℕ) : ZMod p)) := by rw [ht]
    _ = y (Multiplicative.ofAdd (0 : ZMod p)) := nat_const t.val

/-- **Heart of the obstruction.** A `g`-invariant element of `𝔽_p[ℤ/p]` has augmentation `0`:
its `p` coefficients are all equal, and `p · c = 0` in characteristic `p`. -/
theorem aug_zero_of_g_mul_self {y : A p} (hy : g p * y = y) : ε p y = 0 := by
  haveI : NeZero p := ⟨hp.out.pos.ne'⟩
  rw [ε_eq_sum]
  have hconst : ∀ h : G p, y h = y (Multiplicative.ofAdd (0 : ZMod p)) := by
    intro h
    have hc := coeff_const p hy (Multiplicative.toAdd h)
    rwa [ofAdd_toAdd] at hc
  rw [Finset.sum_congr rfl (fun h _ => hconst h), Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (G p) = p := by
    simp [G, ZMod.card]
  rw [hcard, nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- **The augmentation sequence does not split.** The augmentation ideal `ker ε` of
`𝔽_p[ℤ/p]` has no `A`-module complement: there is no `J` with `IsCompl (ker ε) J`. -/
theorem augmentation_no_complement :
    ¬ ∃ J : Submodule (A p) (A p), IsCompl (RingHom.ker (ε p).toRingHom) J := by
  rintro ⟨J, hJ⟩
  -- `1 = a + b`, `a ∈ ker ε`, `b ∈ J`
  have htop : (1 : A p) ∈ RingHom.ker (ε p).toRingHom ⊔ J := by
    rw [hJ.sup_eq_top]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at htop
  obtain ⟨a, ha, b, hb, hab⟩ := htop
  have hεa : ε p a = 0 := (mem_ker_iff p a).mp ha
  -- `ε b = 1`
  have hεb : ε p b = 1 := by
    have h := congrArg (ε p) hab
    rw [map_add, hεa, zero_add, map_one] at h
    exact h
  -- `b` is `g`-invariant: `g * b - b ∈ (ker ε) ⊓ J = ⊥`
  have hgb : g p * b = b := by
    have hmem_I : g p * b - b ∈ RingHom.ker (ε p).toRingHom := by
      rw [mem_ker_iff, map_sub, map_mul, ε_g, one_mul, sub_self]
    have hmem_J : g p * b - b ∈ J := by
      have h1 : g p * b ∈ J := by
        have := J.smul_mem (g p) hb
        rwa [smul_eq_mul] at this
      exact J.sub_mem h1 hb
    have hbot : g p * b - b ∈ RingHom.ker (ε p).toRingHom ⊓ J := ⟨hmem_I, hmem_J⟩
    rw [hJ.inf_eq_bot, Submodule.mem_bot] at hbot
    exact sub_eq_zero.mp hbot
  -- contradiction: `ε b = 0` and `ε b = 1`
  have hzero := aug_zero_of_g_mul_self p hgb
  rw [hεb] at hzero
  exact one_ne_zero hzero

/-- **Parent conclusion, with a named witness.** Complete reducibility fails for the regular
representation `𝔽_p[ℤ/p]`, and the explicit subrepresentation with no complement is the
augmentation ideal `ker ε`. -/
theorem exists_submodule_no_complement :
    ∃ I : Submodule (A p) (A p), ¬ ∃ J : Submodule (A p) (A p), IsCompl I J :=
  ⟨RingHom.ker (ε p).toRingHom, augmentation_no_complement p⟩

end MaschkeAugmentationNoSplit
