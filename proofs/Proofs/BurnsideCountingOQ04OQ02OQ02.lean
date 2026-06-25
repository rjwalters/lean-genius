import Mathlib.Tactic
import Proofs.BurnsideCountingOQ04OQ02

/-
# Burnside Counting, OQ-04 → OQ-02 → OQ-02: the reflection half by parity of `n`

## What this file proves

The parent file `BurnsideCountingOQ04OQ02` built, for every `n`, the dihedral action of
`Dₙ` on the binary colourings `Coloring n = ZMod n → Fin 2` of the `n`-cycle and the
orbit-counting identity

      ∑_{g ∈ Dₙ} |Fix(g)|  =  b(n) · (2n)            (`bracelet_burnside`).

The sibling `BurnsideCountingOQ04OQ02OQ01` evaluated the **rotation half**
`∑_{rotations} |Fix(r i)| = ∑_i 2^{gcd(n,i)}`.  This file evaluates the **reflection half**

      ∑_{i ∈ ZMod n} |Fix(sr i)|

in closed form, split by the parity of `n`:

* for **odd** `n`: every reflection fixes `2^{(n+1)/2}` colourings, so the total is
  `n · 2^{(n+1)/2}`                                          (`reflection_sum_odd`);
* for **even** `n`: the `n/2` reflections through two opposite vertices each fix
  `2^{n/2+1}` colourings and the `n/2` reflections through two edge-midpoints each fix
  `2^{n/2}`, so the total is `(n/2)·(2^{n/2+1} + 2^{n/2}) = 3·(n/2)·2^{n/2}`
                                                              (`reflection_sum_even`).

## The per-reflection count

The single new geometric input is the **per-reflection fixed-point count**

      |Fix(sr i)|  =  2 ^ ((n + f i) / 2),     f i := #{p : σᵢ p = p}        (`card_fixedBy_reflection`)

where `σᵢ : p ↦ -i - p` is the position involution of the reflection `sr i`.  A colouring is
fixed by `sr i` exactly when it is constant on the `⟨σᵢ⟩`-orbits of `ZMod n`; there are
`(n + f i)/2` such orbits (each `2`-cycle of the involution merges two positions, the `f i`
fixed positions stay singletons), so the fixed colourings are functions on those orbits.

The orbit count `(n + f i)/2` is itself Burnside's lemma applied to the order-`2` group
`⟨σᵢ⟩` acting on the `n` positions: `n + f i = |Fix(1)| + |Fix(σᵢ)| = 2·(#orbits)`.

## The fixed-position count `f i`

`σᵢ p = p ⟺ 2p = -i`, so `f i` counts the solutions of `2p = -i` in `ZMod n`:

* `n` odd: `2` is a unit, so `f i = 1` for every `i`;
* `n` even: `2p` ranges over the even residues, so `f i = 2` when `i.val` is even and
  `f i = 0` when `i.val` is odd.

`#print axioms` confirms only `propext, Classical.choice, Quot.sound` — no `native_decide`.
-/

namespace BurnsideCountingOQ04OQ02OQ02

open Finset MulAction BurnsideCountingOQ04OQ02

variable {n : ℕ}

/-! ## Part I: the reflection involution on positions -/

/-- The position permutation of the reflection `sr i`: `σᵢ p = -i - p`.  This is the parent's
`ρ (sr i) = Equiv.subLeft (-i)`. -/
def reflPerm (i : ZMod n) : Equiv.Perm (ZMod n) := Equiv.subLeft (-i)

@[simp] theorem reflPerm_apply (i : ZMod n) (p : ZMod n) : reflPerm i p = -i - p := rfl

/-- `σᵢ` is an involution: `σᵢ (σᵢ p) = p`. -/
theorem reflPerm_involutive (i : ZMod n) : Function.Involutive (reflPerm i) := by
  intro p; simp only [reflPerm_apply]; ring

@[simp] theorem reflPerm_symm (i : ZMod n) : (reflPerm i).symm = reflPerm i :=
  Equiv.ext fun p => (reflPerm_involutive i).injective (by simp)

/-- A position `p` is fixed by `σᵢ` exactly when `2p = -i`. -/
theorem reflPerm_fixed_iff (i p : ZMod n) : reflPerm i p = p ↔ 2 * p = -i := by
  rw [reflPerm_apply, sub_eq_iff_eq_add, ← two_mul, eq_comm]

/-- `σᵢ` is not the identity once `n ≥ 3` (more precisely whenever some position moves).  We
record the clean criterion via order: `σᵢ ≠ 1`. -/
theorem reflPerm_ne_one [NeZero n] (hn : 3 ≤ n) (i : ZMod n) : reflPerm i ≠ 1 := by
  intro h
  have h0 := Equiv.ext_iff.mp h 0
  have h1 := Equiv.ext_iff.mp h 1
  simp only [reflPerm_apply, Equiv.Perm.one_apply, sub_zero] at h0 h1
  -- h0 : -i = 0, h1 : -i - 1 = 1
  rw [h0] at h1
  -- h1 : 0 - 1 = 1, i.e. -1 = 1, i.e. 2 = 0 in ZMod n
  have h2 : (2 : ZMod n) = 0 := by
    have : (-1 : ZMod n) = 1 := by linear_combination h1
    linear_combination -this
  -- 2 = 0 in ZMod n means n ∣ 2, contradicting n ≥ 3
  have hdvd : (n : ℕ) ∣ 2 := by
    have := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast h2)
    exact this
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- `orderOf σᵢ = 2` for `n ≥ 3`. -/
theorem orderOf_reflPerm [NeZero n] (hn : 3 ≤ n) (i : ZMod n) : orderOf (reflPerm i) = 2 := by
  apply orderOf_eq_prime
  · ext p; simp [pow_two]
  · exact reflPerm_ne_one hn i

/-! ## Part II: unfolding the reflection action on colourings -/

/-- The reflection `sr i` acts on a colouring by `(sr i • c) p = c (σᵢ p) = c (-i - p)`.  Reads
off the parent's `smul_apply` at `g = sr i`, where `ρ (sr i) = Equiv.subLeft (-i)` is an
involution (hence equal to its own inverse). -/
theorem reflection_smul_apply (i : ZMod n) (c : Coloring n) (p : ZMod n) :
    ((DihedralGroup.sr i : DihedralGroup n) • c) p = c (reflPerm i p) := by
  rw [smul_apply]
  congr 1
  have hρ : (ρ (DihedralGroup.sr i) : Equiv.Perm (ZMod n)) = reflPerm i := rfl
  rw [hρ, reflPerm_symm]

/-- A colouring is fixed by the reflection `sr i` iff it is `σᵢ`-symmetric: `c (σᵢ p) = c p`. -/
theorem fixed_iff_reflection (i : ZMod n) (c : Coloring n) :
    (DihedralGroup.sr i : DihedralGroup n) • c = c ↔ ∀ p, c (reflPerm i p) = c p := by
  constructor
  · intro h p
    have := congrFun h p
    rwa [reflection_smul_apply] at this
  · intro h
    funext p
    rw [reflection_smul_apply]; exact h p

/-- A `σᵢ`-symmetric colouring is invariant under every integer power of `σᵢ`. -/
theorem reflection_zpow (i : ZMod n) {c : Coloring n} (hc : ∀ p, c (reflPerm i p) = c p) :
    ∀ (k : ℤ) (a : ZMod n), c ((reflPerm i ^ k) a) = c a := by
  have hstep : ∀ a, c (reflPerm i a) = c a := hc
  -- `σᵢ² = 1`, so every natural power of `σᵢ` is self-inverse and preserves a `σᵢ`-symmetric `c`.
  have hsq : reflPerm i ^ 2 = 1 := by ext p; simp [pow_two]
  have hpow : ∀ (m : ℕ) (a : ZMod n), c ((reflPerm i ^ m) a) = c a := by
    intro m
    induction m with
    | zero => intro a; simp
    | succ m ih => intro a; rw [pow_succ, Equiv.Perm.mul_apply, ih (reflPerm i a)]; exact hstep a
  have hself : ∀ m : ℕ, (reflPerm i ^ m)⁻¹ = reflPerm i ^ m := fun m =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_add, ← two_mul, pow_mul, hsq, one_pow])
  intro k a
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]; exact hpow m a
  · rw [zpow_neg, zpow_natCast, hself m]; exact hpow m a

/-! ## Part III: fixed colourings ≃ functions on the orbit quotient -/

variable [NeZero n]

/-- The cyclic group `⟨σᵢ⟩ ≤ Equiv.Perm (ZMod n)` acts on positions; its orbit quotient indexes
the cycles of the reflection. -/
abbrev ReflOrbit (i : ZMod n) := orbitRel.Quotient (Subgroup.zpowers (reflPerm i)) (ZMod n)

/-- The orbit quotient `ReflOrbit i` is a `Fintype` (a quotient of the finite type `ZMod n`). -/
noncomputable instance reflOrbitFintype (i : ZMod n) : Fintype (ReflOrbit i) := by
  classical
  exact Fintype.ofFinite _

/-- **Fixed colourings ≃ functions on the reflection orbit quotient.**  A colouring fixed by
`sr i` is constant on the `⟨σᵢ⟩`-orbits, so it descends to a function on `ReflOrbit i`; any
function on the quotient pulls back to a `σᵢ`-symmetric colouring. -/
def fixedReflectionEquiv (i : ZMod n) :
    ↥(fixedBy (Coloring n) (DihedralGroup.sr i)) ≃ (ReflOrbit i → Fin 2) where
  toFun c := Quotient.lift c.1 (by
    intro a b hab
    have hsym : ∀ p, c.1 (reflPerm i p) = c.1 p :=
      (fixed_iff_reflection i c.1).mp ((mem_fixedBy).mp c.2)
    -- `a ≈ b` means `∃ g ∈ ⟨σᵢ⟩, g • b = a`
    obtain ⟨g, hg⟩ := (orbitRel_apply ..).mp hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have ha : a = (reflPerm i ^ k) b := by
      rw [← hg]; show (g : Equiv.Perm (ZMod n)) b = _; rw [← hk]
    rw [ha, reflection_zpow i hsym k b])
  invFun f :=
    ⟨fun p => f (Quotient.mk'' p), by
      rw [mem_fixedBy, fixed_iff_reflection]
      intro p
      show f (Quotient.mk'' (reflPerm i p)) = f (Quotient.mk'' p)
      congr 1
      rw [Quotient.eq'']
      exact (orbitRel_apply ..).mpr
        ⟨⟨reflPerm i, Subgroup.mem_zpowers _⟩, rfl⟩⟩
  left_inv := by rintro ⟨c, hc⟩; rfl
  right_inv := by
    intro f; funext q
    induction q using Quotient.inductionOn' with
    | _ a => rfl

/-! ## Part IV: the orbit count is `(n + f i)/2` (Burnside on `⟨σᵢ⟩`) -/

variable (i : ZMod n)

/-- The number of positions fixed by the involution `σᵢ`. -/
noncomputable def reflFix (i : ZMod n) : ℕ := Fintype.card {p : ZMod n // reflPerm i p = p}

/-- `reflFix i` counts the solutions of `2p = -i` in `ZMod n`. -/
theorem reflFix_eq (i : ZMod n) : reflFix i = Fintype.card {p : ZMod n // 2 * p = -i} := by
  rw [reflFix]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => reflPerm_fixed_iff i p))

/-- **Orbit count via Burnside.**  Applying Burnside's lemma to the order-`2` group `⟨σᵢ⟩`
acting on the `n` positions gives `|Fix(1)| + |Fix(σᵢ)| = (#orbits)·2`, i.e.
`#orbits = (n + f i)/2`. -/
theorem card_reflOrbit (hn : 3 ≤ n) :
    Fintype.card (ReflOrbit i) = (n + reflFix i) / 2 := by
  classical
  -- Burnside's lemma (Cauchy–Frobenius) for the order-`2` group `⟨σᵢ⟩` acting on positions.
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Subgroup.zpowers (reflPerm i)) (ZMod n)
  -- `|⟨σᵢ⟩| = orderOf σᵢ = 2`.
  have hcardG : Fintype.card (Subgroup.zpowers (reflPerm i)) = 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers, orderOf_reflPerm hn i]
  -- The Cauchy–Frobenius sum over `⟨σᵢ⟩ = {1, σᵢ}` is `|Fix(1)| + |Fix(σᵢ)| = n + reflFix i`.
  have hsum : ∑ g : Subgroup.zpowers (reflPerm i),
      Fintype.card (fixedBy (ZMod n) g) = n + reflFix i := by
    -- The group `⟨σᵢ⟩` has exactly the two distinct elements `1` and `σᵢ`.
    set σ : ↥(Subgroup.zpowers (reflPerm i)) := ⟨reflPerm i, Subgroup.mem_zpowers _⟩ with hσ
    have hne : (1 : ↥(Subgroup.zpowers (reflPerm i))) ≠ σ := by
      intro h
      apply reflPerm_ne_one hn i
      have hval : (1 : Equiv.Perm (ZMod n)) = reflPerm i := congrArg Subtype.val h
      exact hval.symm
    have huniv : (Finset.univ : Finset ↥(Subgroup.zpowers (reflPerm i))) = {1, σ} := by
      apply (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
      rw [Finset.card_pair hne, Finset.card_univ, hcardG]
    -- `|Fix(1)| = n` (the identity fixes every position).
    have hf1 : Fintype.card (fixedBy (ZMod n) (1 : ↥(Subgroup.zpowers (reflPerm i)))) = n := by
      have huniv' : fixedBy (ZMod n) (1 : ↥(Subgroup.zpowers (reflPerm i))) = Set.univ :=
        fixedBy_one_eq_univ (ZMod n) _
      rw [Fintype.card_congr (Equiv.setCongr huniv'),
        Fintype.card_congr (Equiv.Set.univ (ZMod n)), ZMod.card]
    -- `|Fix(σᵢ)| = f i` (the positions fixed by the reflection involution).
    have hfσ : Fintype.card (fixedBy (ZMod n) σ) = reflFix i := by
      rw [reflFix]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun p => Iff.rfl))
    rw [huniv, Finset.sum_pair hne, hf1, hfσ]
  rw [hcardG, hsum] at hburn
  -- `hburn : n + reflFix i = Fintype.card (ReflOrbit i) * 2`.  The `Fintype` instance Burnside
  -- synthesised for the orbit quotient need not be defeq to `reflOrbitFintype`, so we pass through
  -- the instance-independent `Nat.card` to let `omega` finish.
  rw [← Nat.card_eq_fintype_card] at hburn ⊢
  -- Unfold the orbit-quotient abbreviation so the goal's `Nat.card` atom matches `hburn`'s.
  show Nat.card (Quotient (orbitRel (Subgroup.zpowers (reflPerm i)) (ZMod n))) = (n + reflFix i) / 2
  omega

/-! ## Part V: the per-reflection fixed-colouring count -/

/-- **Per-reflection count.**  The number of binary colourings fixed by the reflection `sr i`
is `2^((n + f i)/2)`. -/
theorem card_fixedBy_reflection (hn : 3 ≤ n) :
    Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i)) = 2 ^ ((n + reflFix i) / 2) := by
  classical
  rw [Fintype.card_congr (fixedReflectionEquiv i), Fintype.card_fun, Fintype.card_fin,
    card_reflOrbit i hn]

/-! ## Part VI: the fixed-position count by parity -/

/-- For odd `n`, the involution `σᵢ` has exactly one fixed position (`2` is a unit, so
`2p = -i` has a unique solution). -/
theorem reflFix_odd (hodd : Odd n) : reflFix i = 1 := by
  have h2 : IsUnit (2 : ZMod n) := by
    have hcop : Nat.Coprime 2 n := (Nat.coprime_two_left).mpr hodd
    simpa using (ZMod.isUnit_iff_coprime 2 n).mpr hcop
  rw [reflFix_eq i, Fintype.card_eq_one_iff]
  obtain ⟨u, hu⟩ := h2
  refine ⟨⟨(↑u⁻¹ : ZMod n) * (-i), ?_⟩, ?_⟩
  · show (2 : ZMod n) * ((↑u⁻¹ : ZMod n) * (-i)) = -i
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨q, hq⟩
    have hq' : (2 : ZMod n) * q = -i := hq
    refine Subtype.ext ?_
    show q = (↑u⁻¹ : ZMod n) * (-i)
    rw [← hq', ← hu, ← mul_assoc, Units.inv_mul, one_mul]

/-- For even `n`, `σᵢ` fixes `2` positions when `i.val` is even and `0` when `i.val` is odd. -/
theorem reflFix_even (heven : Even n) :
    reflFix i = if Even i.val then 2 else 0 := by
  rw [reflFix_eq i]
  obtain ⟨kk, hkk⟩ := heven
  have hn2 : 2 * (n / 2) = n := by omega
  have h2n : 2 ≤ n := by have := NeZero.ne n; omega
  -- `n/2` is a nonzero element with `2·(n/2) = 0`: the nontrivial element of the kernel.
  have hc_mem : (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = 0 := by
    have h : (2 : ZMod n) * ((n / 2 : ℕ) : ZMod n) = ((2 * (n / 2) : ℕ) : ZMod n) := by
      push_cast; ring
    rw [h, hn2, ZMod.natCast_self]
  have hc0 : ((n / 2 : ℕ) : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
  by_cases h : Even i.val
  · rw [if_pos h]
    -- `p₀ := -(i.val / 2)` solves `2·p₀ = -i`, so the solution set is a coset of the kernel.
    have hp₀ : 2 * (-(((i.val / 2 : ℕ)) : ZMod n)) = -i := by
      rw [mul_neg]; congr 1
      have h2 : 2 * (i.val / 2) = i.val := by obtain ⟨m, hm⟩ := h; omega
      calc (2 : ZMod n) * ((i.val / 2 : ℕ) : ZMod n)
          = ((2 * (i.val / 2) : ℕ) : ZMod n) := by push_cast; ring
        _ = ((i.val : ℕ) : ZMod n) := by rw [h2]
        _ = i := ZMod.natCast_zmod_val i
    set p₀ : ZMod n := -(((i.val / 2 : ℕ)) : ZMod n)
    have e : {p : ZMod n // 2 * p = -i} ≃ {q : ZMod n // 2 * q = 0} :=
      { toFun := fun p => ⟨p.1 - p₀, by rw [mul_sub, p.2, hp₀, sub_self]⟩
        invFun := fun q => ⟨q.1 + p₀, by rw [mul_add, q.2, hp₀, zero_add]⟩
        left_inv := fun p => by ext; simp
        right_inv := fun q => by ext; simp }
    rw [Fintype.card_congr e, ← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
    refine ⟨⟨0, by ring⟩, ⟨((n / 2 : ℕ) : ZMod n), hc_mem⟩, ?_, ?_⟩
    · intro hcontra; exact hc0 (Subtype.ext_iff.mp hcontra).symm
    · rw [Set.eq_univ_iff_forall]
      rintro ⟨q, hq⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff]
      -- `2q = 0` forces `n ∣ 2·q.val`, so `q.val ∈ {0, n/2}`.
      have hdvd : n ∣ 2 * q.val := by
        have hz : ((2 * q.val : ℕ) : ZMod n) = 0 := by
          push_cast; rw [ZMod.natCast_zmod_val]; exact hq
        rwa [ZMod.natCast_eq_zero_iff] at hz
      have hqlt : q.val < n := q.val_lt
      obtain ⟨c, hc⟩ := hdvd
      rcases c with _ | _ | c
      · left
        simp only [Nat.mul_zero] at hc
        exact (ZMod.val_eq_zero q).mp (by omega)
      · right
        rw [Nat.mul_one] at hc
        have hqv : q.val = n / 2 := by omega
        rw [← ZMod.natCast_zmod_val q, hqv]
      · exfalso
        have hge : n * 2 ≤ n * (c + 1 + 1) := by gcongr; omega
        omega
  · rw [if_neg h, Fintype.card_eq_zero_iff]
    refine ⟨fun p => ?_⟩
    obtain ⟨p, hp⟩ := p
    apply h
    -- `2p = -i` ⇒ `i = 2·(-p)`; reducing mod `2` shows `i.val` is even.
    have hdvd2 : (2 : ℕ) ∣ n := ⟨n / 2, hn2.symm⟩
    set φ : ZMod n →+* ZMod 2 := ZMod.castHom hdvd2 (ZMod 2) with hφ
    have hi2q : i = 2 * (-p) := by linear_combination hp
    have key : ((i.val : ℕ) : ZMod 2) = 0 := by
      have h1 : ((i.val : ℕ) : ZMod 2) = φ i := by
        rw [← map_natCast φ i.val, ZMod.natCast_zmod_val]
      have hφ2 : φ (2 : ZMod n) = 0 := by rw [map_ofNat]; decide
      rw [h1, hi2q, map_mul, hφ2, zero_mul]
    exact (ZMod.natCast_eq_zero_iff_even).mp key

/-! ## Part VII: the reflection half of the Burnside sum, by parity -/

/-- **Reflection half, odd `n`.**  For odd `n`, every reflection fixes `2^{(n+1)/2}`
colourings, so `∑_i |Fix(sr i)| = n · 2^{(n+1)/2}`. -/
theorem reflection_sum_odd (hn : 3 ≤ n) (hodd : Odd n) :
    ∑ i : ZMod n, Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = n * 2 ^ ((n + 1) / 2) := by
  have hterm : ∀ i : ZMod n,
      Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i)) = 2 ^ ((n + 1) / 2) := by
    intro i
    rw [card_fixedBy_reflection i hn, reflFix_odd i hodd]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    ZMod.card, smul_eq_mul]

/-- **Reflection half, even `n`.**  For even `n`, the `n/2` vertex reflections fix `2^{n/2+1}`
and the `n/2` edge reflections fix `2^{n/2}`, so
`∑_i |Fix(sr i)| = (n/2)·(2^{n/2+1} + 2^{n/2})`. -/
theorem reflection_sum_even (hn : 3 ≤ n) (heven : Even n) :
    ∑ i : ZMod n, Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
      = (n / 2) * (2 ^ (n / 2 + 1) + 2 ^ (n / 2)) := by
  -- Per reflection: `2^{n/2+1}` when `i.val` is even (vertex reflection), else `2^{n/2}`.
  have hterm : ∀ i : ZMod n,
      Fintype.card (fixedBy (Coloring n) (DihedralGroup.sr i))
        = if Even i.val then 2 ^ (n / 2 + 1) else 2 ^ (n / 2) := by
    intro i
    rw [card_fixedBy_reflection i hn, reflFix_even i heven]
    by_cases h : Even i.val
    · rw [if_pos h, if_pos h]; congr 1; omega
    · rw [if_neg h, if_neg h]; congr 1
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hn2 : 2 * (n / 2) = n := by obtain ⟨k, hk⟩ := heven; omega
  -- Exactly `n/2` residues have even `val`: map by `val` to `range n`, then `j ↦ 2j` to `range (n/2)`.
  have hcard : (Finset.univ.filter (fun i : ZMod n => Even i.val)).card = n / 2 := by
    rw [← Finset.card_image_of_injective _ (ZMod.val_injective n)]
    have himg : (Finset.univ.filter (fun i : ZMod n => Even i.val)).image ZMod.val
        = (Finset.range n).filter (fun k => Even k) := by
      ext k
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨i.val_lt, hi⟩
      · rintro ⟨hk, hek⟩
        exact ⟨(k : ZMod n), by rw [ZMod.val_natCast_of_lt hk]; exact hek,
          ZMod.val_natCast_of_lt hk⟩
    rw [himg]
    have hbij : (Finset.range n).filter (fun k => Even k)
        = (Finset.range (n / 2)).image (fun j => 2 * j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hk, m, rfl⟩; exact ⟨m, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; exact ⟨by omega, ⟨j, by ring⟩⟩
    rw [hbij, Finset.card_image_of_injective _ (fun a b h => by omega), Finset.card_range]
  -- Split the sum by the parity of `val` and evaluate both constant pieces.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : ZMod n => Even i.val)]
  rw [Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_filter.mp hi).2),
    Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_filter.mp hi).2),
    Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul, hcard]
  have hcardN : (Finset.univ.filter (fun i : ZMod n => ¬ Even i.val)).card = n / 2 := by
    have htot := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (ZMod n))) (p := fun i => Even i.val)
    rw [hcard, Finset.card_univ, ZMod.card] at htot
    omega
  rw [hcardN]; ring

end BurnsideCountingOQ04OQ02OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ04OQ02OQ02.card_fixedBy_reflection
#print axioms BurnsideCountingOQ04OQ02OQ02.card_reflOrbit
#print axioms BurnsideCountingOQ04OQ02OQ02.reflFix_even
#print axioms BurnsideCountingOQ04OQ02OQ02.reflection_sum_odd
#print axioms BurnsideCountingOQ04OQ02OQ02.reflection_sum_even
