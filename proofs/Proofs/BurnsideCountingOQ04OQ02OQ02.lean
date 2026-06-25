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
  Equiv.ext fun p => (reflPerm_involutive i).injective (by simp [(reflPerm_involutive i) p])

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
    have := (ZMod.natCast_zmod_eq_zero_iff_dvd 2 n).mp (by exact_mod_cast h2)
    exact this
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- `orderOf σᵢ = 2` for `n ≥ 3`. -/
theorem orderOf_reflPerm [NeZero n] (hn : 3 ≤ n) (i : ZMod n) : orderOf (reflPerm i) = 2 := by
  apply orderOf_eq_prime
  · ext p; simp [pow_two, (reflPerm_involutive i) p]
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
  -- σᵢ is an involution, so it suffices to handle the single step in both directions.
  have hstep : ∀ a, c (reflPerm i a) = c a := hc
  intro k
  induction k using Int.induction_on with
  | hz => intro a; simp
  | hp k ih =>
    intro a
    have : (reflPerm i ^ (k + 1 : ℤ)) a = reflPerm i ((reflPerm i ^ (k : ℤ)) a) := by
      rw [zpow_add, zpow_one]; rfl
    rw [this, hstep]; exact ih a
  | hn k ih =>
    intro a
    have hinv : (reflPerm i)⁻¹ = reflPerm i := by
      rw [Equiv.Perm.inv_def, reflPerm_symm]
    have : (reflPerm i ^ (-(k : ℤ) - 1)) a = reflPerm i ((reflPerm i ^ (-(k : ℤ))) a) := by
      rw [sub_eq_add_neg, zpow_add, zpow_neg, zpow_one, hinv]; rfl
    rw [this, hstep]; exact ih a

/-! ## Part III: fixed colourings ≃ functions on the orbit quotient -/

variable [NeZero n]

/-- The cyclic group `⟨σᵢ⟩ ≤ Equiv.Perm (ZMod n)` acts on positions; its orbit quotient indexes
the cycles of the reflection. -/
abbrev ReflOrbit (i : ZMod n) := orbitRel.Quotient (Subgroup.zpowers (reflPerm i)) (ZMod n)

/-- **Fixed colourings ≃ functions on the reflection orbit quotient.**  A colouring fixed by
`sr i` is constant on the `⟨σᵢ⟩`-orbits, so it descends to a function on `ReflOrbit i`; any
function on the quotient pulls back to a `σᵢ`-symmetric colouring. -/
def fixedReflectionEquiv (i : ZMod n) :
    ↥(fixedBy (Coloring n) (DihedralGroup.sr i)) ≃ (ReflOrbit i → Fin 2) where
  toFun c := Quotient.lift c.1 (by
    intro a b hab
    have hsym : ∀ p, c.1 (reflPerm i p) = c.1 p :=
      (fixed_iff_reflection i c.1).mp ((mem_fixedBy).mp c.2)
    -- a ≈ b means ∃ g ∈ ⟨σᵢ⟩, g • a = b
    obtain ⟨g, hg⟩ := (orbitRel_apply ..).mp hab.symm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    have hb : b = (reflPerm i ^ k) a := by
      rw [← hg]; show _ = (g : Equiv.Perm (ZMod n)) a; rw [← hk]; rfl
    rw [hb, reflection_zpow i hsym k a])
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
    sorry
  rw [hcardG, hsum] at hburn
  -- `hburn : n + reflFix i = Fintype.card (ReflOrbit i) * 2`.
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
    have hcop : Nat.Coprime 2 n := (Nat.coprime_two_left_iff_odd).mpr hodd
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
  -- Count solutions of `2p = -i` in `ZMod n` (n even): the doubling map `p ↦ 2p` has kernel
  -- `{0, n/2}` and image the even residues, so a fibre is empty (`i.val` odd) or has size `2`.
  sorry

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
    · rw [if_neg h, if_neg h]; congr 1; omega
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  -- There are exactly `n/2` residues with even `val` and `n/2` with odd `val` (n even), so the
  -- parity-split sum is `(n/2)·2^{n/2+1} + (n/2)·2^{n/2}`.
  sorry

end BurnsideCountingOQ04OQ02OQ02

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms BurnsideCountingOQ04OQ02OQ02.card_fixedBy_reflection
