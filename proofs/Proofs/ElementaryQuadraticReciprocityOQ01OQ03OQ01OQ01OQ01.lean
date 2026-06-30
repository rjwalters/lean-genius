/-
  The Frobenius/Zolotarev Sign on a PRIME-POWER Modulus (units level):
  sign(x ↦ u·x on (ℤ/pⁿ)ˣ) = legendreSym p (u mod p)     for p an odd prime.
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01)

  Open Question (the explicit next step #1 left by the parent
  oq-01-oq-03-oq-01-oq-01, the squarefree-odd Frobenius/Zolotarev lemma):

    "Handle prime-power factors pᵉ (e ≥ 2): CRT does not split them and the sign
     on ℤ/pᵉ is a genuinely new computation; reaching it gives
     sign(ringMulPerm a on ℤ/n) = J(a | n) for every odd n."

  This file performs the heart of that new computation: the sign of the
  multiplication-by-`u` permutation of the *units* `(ℤ/pⁿ)ˣ`.  For a prime
  modulus the units form the multiplicative group of a field and Zolotarev's
  lemma is the quadratic character (`ElementaryQuadraticReciprocityOQ01OQ03OQ01`).
  For a prime *power* `pⁿ`, `ℤ/pⁿ` is no longer a field, yet `(ℤ/pⁿ)ˣ` is still
  cyclic (Mathlib's `ZMod.isCyclic_units_of_prime_pow`, for `p` odd), so the same
  left-regular-representation argument applies — but the value is now read off
  via the *reduction homomorphism* `ρ : (ℤ/pⁿ)ˣ → (ℤ/p)ˣ` instead of a field
  quadratic character:

        sign(x ↦ u·x on (ℤ/pⁿ)ˣ) = legendreSym p ((ρ u).val).

  ## The argument

  `x ↦ u·x` is left translation `Equiv.mulLeft u` in the finite group
  `G = (ℤ/pⁿ)ˣ`, i.e. an element of the left regular representation
  `mulLeftHom : G →* Perm G`.  Both `sign ∘ mulLeftHom` and
  `legendreSym p ∘ ρ` are homomorphisms `G → {±1}`, so (as `G` is cyclic with
  generator `g`) it suffices to check they agree on `g`:

  * `sign(mulLeft g) = -1`: a generator gives a single `|G|`-cycle and `|G|`,
    the totient `pⁿ⁻¹(p-1)`, is even.
  * `legendreSym p (ρ g) = -1`: `ρ` is surjective (`ZMod.unitsMap_surjective`),
    so `ρ g` generates `(ℤ/p)ˣ`, hence is a non-residue mod `p`.

  Writing an arbitrary `u = gᵏ`, both sides equal `(-1)ᵏ`.

  ## Honest scope

  This is the *units* sign on a prime-power modulus — the genuinely new content
  the parent flagged.  Assembling it with the action on the non-unit part
  `p·(ℤ/pⁿ⁻¹) ⊂ ℤ/pⁿ` to obtain the whole-ring statement
  `sign(ringMulPerm u on ℤ/pⁿ) = J(u | pⁿ)`, and thence every odd `n`, is left to
  the follow-up.  0 sorries, 0 axioms.

  References:
  - Zolotarev (1872); Frobenius (1914); Rousseau (1991), Amer. Math. Monthly.
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01

set_option maxHeartbeats 800000

namespace ZolotarevPrimePower

open Equiv Equiv.Perm

/-
═══════════════════════════════════════════════════════════════════════════════
PART 0: THE LEFT REGULAR REPRESENTATION OF A FINITE GROUP  (generic)
═══════════════════════════════════════════════════════════════════════════════ -/

section Generic
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Left translation as a monoid homomorphism into the symmetric group
    (the left regular representation). -/
def mulLeftHom : G →* Perm G where
  toFun := Equiv.mulLeft
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [Equiv.Perm.mul_apply, mul_assoc]

/-- Left translation by a non-identity element has no fixed point. -/
theorem mulLeft_no_fixed (a : G) (ha : a ≠ 1) (x : G) : Equiv.mulLeft a x ≠ x := by
  change a * x ≠ x
  intro h
  exact ha (mul_right_cancel (by rw [one_mul]; exact h))

/-- A generator's left translation is a single cycle. -/
theorem mulLeft_generator_isCycle (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hg1 : g ≠ 1) : (Equiv.mulLeft g).IsCycle := by
  refine ⟨1, mulLeft_no_fixed g hg1 1, ?_⟩
  intro y _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg y)
  refine ⟨k, ?_⟩
  have hpow : (Equiv.mulLeft g) ^ k = Equiv.mulLeft (g ^ k) := (map_zpow mulLeftHom g k).symm
  rw [hpow]
  change (g ^ k) * 1 = y
  rw [mul_one]; exact hk

/-- A non-identity left translation has full support. -/
theorem mulLeft_support_eq_univ (a : G) (ha : a ≠ 1) :
    (Equiv.mulLeft a).support = Finset.univ := by
  ext x
  simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
  exact mulLeft_no_fixed a ha x

/-- A generator of a group with more than one element is not the identity. -/
theorem generator_ne_one (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : 1 < Fintype.card G) : g ≠ 1 := by
  rintro rfl
  have h1 : ∀ x : G, x = 1 := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    simpa using hk.symm
  have : Fintype.card G ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => by rw [h1 a, h1 b])
  omega

/-- The sign of left translation by a generator of an even-order group is `-1`:
    a single `|G|`-cycle with `|G|` even. -/
theorem sign_mulLeft_generator (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hg1 : g ≠ 1) (hcard : Even (Fintype.card G)) :
    Equiv.Perm.sign (Equiv.mulLeft g) = -1 := by
  have hcyc := mulLeft_generator_isCycle g hg hg1
  rw [hcyc.sign, mulLeft_support_eq_univ g hg1, Finset.card_univ, Even.neg_one_pow hcard]

/-- The sign of left translation is multiplicative under powers. -/
theorem sign_mulLeft_pow (g : G) (n : ℕ) :
    Equiv.Perm.sign (Equiv.mulLeft (g ^ n)) = (Equiv.Perm.sign (Equiv.mulLeft g)) ^ n :=
  map_pow ((Equiv.Perm.sign).comp mulLeftHom) g n

end Generic

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: CARD OF THE PRIME-POWER UNIT GROUP IS EVEN
═══════════════════════════════════════════════════════════════════════════════ -/

/-- For an odd prime `p` and `n ≥ 1`, `|(ℤ/pⁿ)ˣ| = pⁿ⁻¹(p-1)` is even. -/
theorem card_units_prime_pow_even {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ≠ 0)
    [NeZero (p ^ n)] : Even (Fintype.card (ZMod (p ^ n))ˣ) := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp (Nat.pos_of_ne_zero hn)]
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have heven : Even (p - 1) := by rcases hodd with ⟨k, hk⟩; exact ⟨k, by omega⟩
  exact heven.mul_left _

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE UNITS-LEVEL PRIME-POWER ZOLOTAREV LEMMA
═══════════════════════════════════════════════════════════════════════════════ -/

open ZolotarevBaseCase (generator_not_isSquare legendreSym_unit_eq)

/-- **Prime-power Zolotarev (units, quadratic-character form).**  For an odd prime
    `p`, `n ≥ 1` and a unit `u : (ℤ/pⁿ)ˣ`, the sign of left multiplication by `u`
    on `(ℤ/pⁿ)ˣ` equals the quadratic character of the reduction `ρ u ∈ (ℤ/p)ˣ`. -/
theorem sign_mulLeft_eq_quadraticChar {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : n ≠ 0)
    [NeZero (p ^ n)] (u : (ZMod (p ^ n))ˣ) :
    ((Equiv.Perm.sign (Equiv.mulLeft u) : ℤ))
      = quadraticChar (ZMod p) ((ZMod.unitsMap (dvd_pow_self p hn) u : ZMod p)) := by
  haveI : IsCyclic (ZMod (p ^ n))ˣ := ZMod.isCyclic_units_of_prime_pow p hp.out hp2 n
  set ρ := ZMod.unitsMap (dvd_pow_self p hn) with hρ
  have hcard_even := card_units_prime_pow_even hp.out hp2 hn (p := p) (n := n)
  -- generator of the cyclic group
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (p ^ n))ˣ)
  have hcard1 : 1 < Fintype.card (ZMod (p ^ n))ˣ := by
    obtain ⟨k, hk⟩ := hcard_even
    have hpos : 0 < Fintype.card (ZMod (p ^ n))ˣ := Fintype.card_pos
    omega
  have hg1 : g ≠ 1 := generator_ne_one g hg hcard1
  -- ρ is surjective, so ρ g generates (ℤ/p)ˣ
  have hρsurj : Function.Surjective ρ := ZMod.unitsMap_surjective (dvd_pow_self p hn)
  have hρg_gen : ∀ y : (ZMod p)ˣ, y ∈ Subgroup.zpowers (ρ g) := by
    intro y
    obtain ⟨x, rfl⟩ := hρsurj y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
    exact ⟨k, by rw [← hk, map_zpow]⟩
  -- the two anchor values at the generator
  have hsg : ((Equiv.Perm.sign (Equiv.mulLeft g) : ℤ)) = -1 := by
    rw [sign_mulLeft_generator g hg hg1 hcard_even]; rfl
  have hqg : quadraticChar (ZMod p) ((ρ g : ZMod p)) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (generator_not_isSquare (ρ g) hp2 hρg_gen)
  -- write u as a power of g
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hg u))
  have hsign : ((Equiv.Perm.sign (Equiv.mulLeft u) : ℤ)) = (-1) ^ k := by
    have hpow : Equiv.Perm.sign (Equiv.mulLeft u) = (Equiv.Perm.sign (Equiv.mulLeft g)) ^ k := by
      rw [← hk]; exact sign_mulLeft_pow g k
    rw [hpow, Units.val_pow_eq_pow_val, hsg]
  have hchar : quadraticChar (ZMod p) ((ρ u : ZMod p)) = (-1) ^ k := by
    have hgu : ρ u = (ρ g) ^ k := by rw [← hk, map_pow]
    rw [hgu, Units.val_pow_eq_pow_val, map_pow, hqg]
  rw [hsign, hchar]

/-- **Prime-power Zolotarev (units, Legendre form).**  The sign of left
    multiplication by `u` on `(ℤ/pⁿ)ˣ` equals the Legendre symbol mod `p` of the
    reduction of `u`. -/
theorem sign_mulLeft_eq_legendre {p n : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hn : n ≠ 0)
    [NeZero (p ^ n)] (u : (ZMod (p ^ n))ˣ) :
    ((Equiv.Perm.sign (Equiv.mulLeft u) : ℤ))
      = legendreSym p (((ZMod.unitsMap (dvd_pow_self p hn) u : ZMod p).val : ℤ)) := by
  rw [sign_mulLeft_eq_quadraticChar hp2 hn u,
    legendreSym_unit_eq (ZMod.unitsMap (dvd_pow_self p hn) u)]

end ZolotarevPrimePower

#check @ZolotarevPrimePower.sign_mulLeft_eq_quadraticChar
#check @ZolotarevPrimePower.sign_mulLeft_eq_legendre
