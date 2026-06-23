import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-
# Gauss-Wilson, Non-Cyclic Case: A Direct Single-Involution Argument (Self-Contained)

This file answers the open question

  *Wilson's theorem: a direct involution argument for the non-cyclic case,
   without a companion file.*

The parent gallery entry (`wilsons-theorem-oq-02`) proves the non-cyclic half of
the Gauss-Wilson theorem,

  ¬IsCyclic (ZMod n)ˣ  →  ∏ units = 1,

by delegating to *two* companion files (`WilsonsTheoremOQ02Ext` and
`GaussWilsonNonCyclic`) and using a **two-involution trick**: three applications
of a constant-product involution lemma followed by a cancellation.

Here we give a **single, self-contained file** with a genuinely **direct
single-involution argument**.  The key new observation is:

  The 2-torsion `S = {x | x² = 1}` of a finite commutative group is itself a
  2-group, hence `|S|` is a power of `2`.  When `|S| ≥ 3` we therefore have
  `4 ∣ |S|`, so for *any* nontrivial `a ∈ S` the single involution `x ↦ a·x`
  gives `∏ S = a^(|S|/2) = (a²)^(|S|/4) = 1`.

This replaces the three-involution cancellation by one involution plus the
elementary "power-of-two cardinality" fact, and needs no companion file: the
number-theoretic input (`¬cyclic → |S| ≥ 3`, via CRT and the `2^k` case) is
inlined below.

## Results (all sorry-free, no `axiom`s, no `native_decide`)

* `twoTorsion`                       — the 2-torsion subgroup `{x | x² = 1}`
* `card_two_torsion_eq_pow_two`      — `|{x | x² = 1}|` is a power of `2`
* `prod_two_torsion_eq_one`          — **direct single-involution**: `|S| ≥ 3 → ∏ S = 1`
* `prod_units_one_of_not_cyclic`     — `¬IsCyclic (ZMod n)ˣ → ∏ units = 1`  (self-contained)
* `prod_units_neg_one_of_cyclic`     — `IsCyclic (ZMod n)ˣ → ∏ units = -1`
* `gaussWilson`                      — `∏ units = -1 ↔ IsCyclic (ZMod n)ˣ`
-/

namespace WilsonsTheoremOQ02OQ02

open Nat Finset ZMod

-- ============================================================================
-- Section 1: Coercion and small `-1 ≠ 1` facts
-- ============================================================================

/-- Push the units coercion through a product. -/
private theorem units_val_prod {ι : Type*} {M : Type*} [CommMonoid M]
    (s : Finset ι) (f : ι → Mˣ) :
    (↑(∏ i ∈ s, f i) : M) = ∏ i ∈ s, (↑(f i) : M) :=
  map_prod (Units.coeHom M) f s

/-- `-1 ≠ 1` in `ZMod n` for `n ≥ 3`. -/
private theorem neg_one_ne_one_zmod {n : ℕ} (hn : n ≥ 3) : (-1 : ZMod n) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro heq
  have h11 : (1 : ZMod n) + 1 = 0 := by
    have := neg_add_cancel (1 : ZMod n); rwa [heq] at this
  have hchar : (2 : ZMod n) = 0 := by
    have h2eq : (2 : ZMod n) = 1 + 1 := by norm_num
    rw [h2eq]; exact h11
  have hdvd : n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 n).mp (by exact_mod_cast hchar)
  exact absurd (Nat.le_of_dvd (by norm_num) hdvd) (by omega)

/-- `-1 ≠ 1` in `(ZMod n)ˣ` for `n ≥ 3`. -/
private theorem neg_one_ne_one_units {n : ℕ} (hn : n ≥ 3) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h; apply neg_one_ne_one_zmod hn
  have hv := congr_arg (Units.val : (ZMod n)ˣ → ZMod n) h
  simp only [Units.val_neg, Units.val_one] at hv; exact hv

-- ============================================================================
-- Section 2: Abstract involution infrastructure
-- ============================================================================

/-- In a commutative group, `x² = 1 ↔ x = x⁻¹`. -/
private theorem sq_eq_one_iff_eq_inv {G : Type*} [CommGroup G] (x : G) :
    x ^ 2 = 1 ↔ x = x⁻¹ := by rw [sq, mul_eq_one_iff_eq_inv]

/-- `∏ G = ∏ {x | x² = 1}`: the involution `x ↦ x⁻¹` pairs off everything outside
    the 2-torsion. -/
theorem prod_eq_prod_two_torsion (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1), x := by
  have hsplit : ∏ x : G, x =
      (∏ x ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1), x) *
      (∏ x ∈ Finset.univ.filter (fun x : G => ¬(x ^ 2 = 1)), x) :=
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : G => x ^ 2 = 1) id).symm
  have hrest : ∏ x ∈ Finset.univ.filter (fun x : G => ¬(x ^ 2 = 1)), x = 1 := by
    -- `Finset.prod_involution` orders its goals as: pair-product, fixed-point-free,
    -- double-application, then membership.
    apply Finset.prod_involution (fun x _ => x⁻¹)
    · intros a _; exact mul_inv_cancel a
    · intro a ha _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact fun heq => ha ((sq_eq_one_iff_eq_inv a).mpr heq.symm)
    · intros a _; exact inv_inv a
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rwa [inv_pow, inv_eq_one]
  rw [hsplit, hrest, mul_one]

/-- Membership in `S \ {a, σ a}`, unpacked. -/
private theorem mem_sdiff_pair {α : Type*} [DecidableEq α] {S : Finset α} {a b : α} {x : α} :
    x ∈ S \ {a, b} ↔ (x ∈ S ∧ x ≠ a ∧ x ≠ b) := by
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto

/-- A fixed-point-free involution on a `Finset` gives even cardinality. -/
theorem even_card_of_fpf_involution {α : Type*} [DecidableEq α]
    {S : Finset α} {σ : α → α}
    (hσ_mem : ∀ x ∈ S, σ x ∈ S)
    (hσ_inv : ∀ x ∈ S, σ (σ x) = x)
    (hσ_ne : ∀ x ∈ S, σ x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS; exact ⟨0, by simp⟩
    · obtain ⟨a, ha⟩ := hS
      have hσa_mem : σ a ∈ S := hσ_mem a ha
      have hσa_ne : σ a ≠ a := hσ_ne a ha
      set T := S \ {a, σ a} with hTdef
      have hpair_sub : ({a, σ a} : Finset α) ⊆ S := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hσa_mem
      have hpair_card : ({a, σ a} : Finset α).card = 2 := Finset.card_pair hσa_ne.symm
      have hT_mem : ∀ x ∈ T, σ x ∈ T := by
        intro x hx
        rw [hTdef, mem_sdiff_pair] at hx ⊢
        obtain ⟨hxS, hxa, hxsa⟩ := hx
        refine ⟨hσ_mem x hxS, ?_, ?_⟩
        · intro h; exact hxsa (by rw [← hσ_inv x hxS, h])
        · intro h; exact hxa (by rw [← hσ_inv x hxS, h, hσ_inv a ha])
      have hT_inv : ∀ x ∈ T, σ (σ x) = x :=
        fun x hx => hσ_inv x (mem_sdiff_pair.mp (hTdef ▸ hx)).1
      have hT_ne : ∀ x ∈ T, σ x ≠ x :=
        fun x hx => hσ_ne x (mem_sdiff_pair.mp (hTdef ▸ hx)).1
      have hT_lt : T ⊂ S := Finset.sdiff_ssubset hpair_sub ⟨a, Finset.mem_insert_self a _⟩
      obtain ⟨k, hk⟩ := ih T hT_lt hT_mem hT_inv hT_ne
      have hcardT : T.card = S.card - 2 := by
        rw [hTdef, Finset.card_sdiff_of_subset hpair_sub, hpair_card]
      have hge : 2 ≤ S.card := by
        have := Finset.card_le_card hpair_sub; rw [hpair_card] at this; omega
      exact ⟨k + 1, by omega⟩

/-- Product over a `Finset` carrying a fixed-point-free involution with constant
    pair product `c`: the product is `c ^ (|S| / 2)`. -/
theorem prod_involution_const {G : Type*} [CommGroup G] [DecidableEq G]
    {S : Finset G} {σ : G → G} {c : G}
    (hσ_mem : ∀ x ∈ S, σ x ∈ S)
    (hσ_inv : ∀ x ∈ S, σ (σ x) = x)
    (hσ_ne : ∀ x ∈ S, σ x ≠ x)
    (hσ_prod : ∀ x ∈ S, x * σ x = c) :
    ∏ x ∈ S, x = c ^ (S.card / 2) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS; simp
    · obtain ⟨a, ha⟩ := hS
      have hσa_mem : σ a ∈ S := hσ_mem a ha
      have hσa_ne : σ a ≠ a := hσ_ne a ha
      set T := S \ {a, σ a} with hTdef
      have hpair_sub : ({a, σ a} : Finset G) ⊆ S := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ha
        · exact hσa_mem
      have hpair_card : ({a, σ a} : Finset G).card = 2 := Finset.card_pair hσa_ne.symm
      have hT_mem : ∀ x ∈ T, σ x ∈ T := by
        intro x hx
        rw [hTdef, mem_sdiff_pair] at hx ⊢
        obtain ⟨hxS, hxa, hxsa⟩ := hx
        refine ⟨hσ_mem x hxS, ?_, ?_⟩
        · intro h; exact hxsa (by rw [← hσ_inv x hxS, h])
        · intro h; exact hxa (by rw [← hσ_inv x hxS, h, hσ_inv a ha])
      have hT_inv : ∀ x ∈ T, σ (σ x) = x :=
        fun x hx => hσ_inv x (mem_sdiff_pair.mp (hTdef ▸ hx)).1
      have hT_ne : ∀ x ∈ T, σ x ≠ x :=
        fun x hx => hσ_ne x (mem_sdiff_pair.mp (hTdef ▸ hx)).1
      have hT_prod : ∀ x ∈ T, x * σ x = c :=
        fun x hx => hσ_prod x (mem_sdiff_pair.mp (hTdef ▸ hx)).1
      have hT_lt : T ⊂ S := Finset.sdiff_ssubset hpair_sub ⟨a, Finset.mem_insert_self a _⟩
      have hih := ih T hT_lt hT_mem hT_inv hT_ne hT_prod
      have hsplit : (∏ x ∈ T, x) * (∏ x ∈ ({a, σ a} : Finset G), x) = ∏ x ∈ S, x := by
        rw [hTdef]; exact Finset.prod_sdiff hpair_sub
      have hprod_pair : ∏ x ∈ ({a, σ a} : Finset G), x = c := by
        rw [Finset.prod_pair hσa_ne.symm]; exact hσ_prod a ha
      have hcardT : T.card = S.card - 2 := by
        rw [hTdef, Finset.card_sdiff_of_subset hpair_sub, hpair_card]
      have hge : 2 ≤ S.card := by
        have := Finset.card_le_card hpair_sub; rw [hpair_card] at this; omega
      obtain ⟨k, hk⟩ := even_card_of_fpf_involution hT_mem hT_inv hT_ne
      rw [← hsplit, hih, hprod_pair,
        show T.card / 2 = k from by omega, show S.card / 2 = k + 1 from by omega, pow_succ]

-- ============================================================================
-- Section 3: The 2-torsion is a 2-group — hence has power-of-two cardinality
-- ============================================================================

/-- The **2-torsion subgroup** `{x | x² = 1}` of a commutative group. -/
def twoTorsion (G : Type*) [CommGroup G] : Subgroup G where
  carrier := {x | x ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [inv_pow, ha, inv_one]

@[simp] theorem mem_twoTorsion {G : Type*} [CommGroup G] (x : G) :
    x ∈ twoTorsion G ↔ x ^ 2 = 1 := Iff.rfl

/-- The 2-torsion is a `2`-group: every element satisfies `g ^ 2 = 1`. -/
theorem isPGroup_twoTorsion (G : Type*) [CommGroup G] : IsPGroup 2 (twoTorsion G) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [pow_one, Subgroup.coe_pow]
  exact g.2

/-- **The 2-torsion has power-of-two cardinality.**  `|{x | x² = 1}| = 2 ^ n`. -/
theorem card_two_torsion_eq_pow_two (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∃ n : ℕ, (Finset.univ.filter (fun x : G => x ^ 2 = 1)).card = 2 ^ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (isPGroup_twoTorsion G)
  refine ⟨n, ?_⟩
  calc (Finset.univ.filter (fun x : G => x ^ 2 = 1)).card
      = Nat.card {x : G // x ^ 2 = 1} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card ↥(twoTorsion G) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => (mem_twoTorsion x).symm))
    _ = 2 ^ n := hn

-- ============================================================================
-- Section 4: The direct single-involution lemma
-- ============================================================================

/-- **Direct single-involution argument.**

    In a finite commutative group, if the 2-torsion `S = {x | x² = 1}` has at
    least `3` elements, then `∏ S = 1`.

    *Proof.* `|S|` is a power of `2` (`card_two_torsion_eq_pow_two`); being `≥ 3`
    it is in fact `≥ 4`, so `4 ∣ |S|`.  Pick any `a ∈ S` with `a ≠ 1`.  The map
    `x ↦ a·x` is a fixed-point-free involution of `S` with constant pair product
    `a`, so `∏ S = a ^ (|S|/2)`.  Since `4 ∣ |S|`, `|S|/2 = 2·(|S|/4)` is even,
    hence `a ^ (|S|/2) = (a²) ^ (|S|/4) = 1`. -/
theorem prod_two_torsion_eq_one (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
    (hcard : 3 ≤ (Finset.univ.filter (fun x : G => x ^ 2 = 1)).card) :
    ∏ x ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1), x = 1 := by
  set S := Finset.univ.filter (fun x : G => x ^ 2 = 1) with hS
  -- `|S|` is a power of two, and ≥ 3, hence divisible by 4.
  obtain ⟨n, hn⟩ := card_two_torsion_eq_pow_two G
  rw [← hS] at hn
  have hn2 : 2 ≤ n := by
    by_contra h; push_neg at h; interval_cases n <;> omega
  have h4 : 4 ∣ S.card := by
    rw [hn, show n = (n - 2) + 2 from by omega, pow_add, show (4 : ℕ) = 2 ^ 2 from by norm_num]
    exact dvd_mul_left _ _
  -- Pick `a ∈ S`, `a ≠ 1`.
  obtain ⟨a, ha_mem, ha_ne⟩ : ∃ a ∈ S, a ≠ 1 :=
    Finset.exists_mem_ne (by omega) 1
  have ha_sq : a ^ 2 = 1 := by simpa [hS, Finset.mem_filter] using ha_mem
  -- The involution `x ↦ a·x` on `S`.
  have hmem : ∀ x ∈ S, a * x ∈ S := by
    intro x hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [mul_pow, ha_sq, hx, one_mul]
  have hinv : ∀ x ∈ S, a * (a * x) = x := by
    intro x _; rw [← mul_assoc, ← sq, ha_sq, one_mul]
  have hne : ∀ x ∈ S, a * x ≠ x := by
    intro x _ h
    apply ha_ne
    have h' : a * x = 1 * x := by rw [one_mul]; exact h
    exact mul_right_cancel h'
  have hprod : ∀ x ∈ S, x * (a * x) = a := by
    intro x hx
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [mul_comm x (a * x), mul_assoc, ← sq, hx, mul_one]
  -- `∏ S = a ^ (|S|/2)`, and `|S|/2` is even.
  rw [prod_involution_const hmem hinv hne hprod]
  obtain ⟨m, hm⟩ := h4
  rw [show S.card / 2 = 2 * m from by omega, pow_mul, ha_sq, one_pow]

-- ============================================================================
-- Section 5: Lifting `x² = 1` from `ZMod n` to units
-- ============================================================================

/-- An element `x` with `x² = 1` is a unit (its own inverse). -/
private def unitOfSqEqOne {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) : (ZMod n)ˣ :=
  ⟨x, x, by rw [← sq]; exact hx, by rw [← sq]; exact hx⟩

@[simp] private theorem unitOfSqEqOne_val {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) :
    (unitOfSqEqOne x hx : ZMod n) = x := rfl

private theorem unitOfSqEqOne_sq {n : ℕ} [NeZero n] (x : ZMod n) (hx : x ^ 2 = 1) :
    (unitOfSqEqOne x hx) ^ 2 = 1 := by ext; simp [Units.val_pow_eq_pow_val, hx]

private theorem unitOfSqEqOne_ne_one {n : ℕ} [NeZero n] {x : ZMod n} (hx : x ^ 2 = 1)
    (hne : x ≠ 1) : unitOfSqEqOne x hx ≠ 1 := fun h => hne (congr_arg Units.val h)

private theorem unitOfSqEqOne_ne_neg_one {n : ℕ} [NeZero n] {x : ZMod n} (hx : x ^ 2 = 1)
    (hne : x ≠ -1) : unitOfSqEqOne x hx ≠ -1 := by
  intro h
  have : (unitOfSqEqOne x hx : ZMod n) = ((-1 : (ZMod n)ˣ) : ZMod n) := congr_arg Units.val h
  simp at this; exact hne this

-- ============================================================================
-- Section 6: Number theory — a third square root of unity when not cyclic
-- ============================================================================

/-- CRT: for coprime `a, b ≥ 3`, `ZMod (a*b)` has a square root of unity ≠ ±1. -/
private theorem exists_third_sqrt_coprime {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : a ≥ 3) (hb : b ≥ 3) :
    ∃ x : ZMod (a * b), x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 := by
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  haveI : NeZero (a * b) := ⟨by positivity⟩
  set e := ZMod.chineseRemainder hab with he_def
  refine ⟨e.symm (1, -1), ?_, ?_, ?_⟩
  · have h1 : e.symm (1, -1) ^ 2 = e.symm ((1, -1) ^ 2) := by rw [map_pow]
    rw [h1]
    have h2 : ((1 : ZMod a), (-1 : ZMod b)) ^ 2 = 1 := by ext <;> simp [sq]
    rw [h2, map_one]
  · intro h
    have : e (e.symm (1, -1)) = e 1 := by rw [h]
    rw [e.apply_symm_apply] at this
    have h2 := congr_arg Prod.snd this
    simp at h2
    exact neg_one_ne_one_zmod hb h2
  · intro h
    have : e (e.symm (1, -1)) = e (-1) := by rw [h]
    rw [e.apply_symm_apply] at this
    have h1 := congr_arg Prod.fst this
    simp at h1
    exact neg_one_ne_one_zmod ha h1.symm

private lemma two_pow_helper (k : ℕ) (hk : k ≥ 3) : 2 * 2 ^ (k - 1) = 2 ^ k := by
  conv_rhs => rw [show k = (k - 1) + 1 from by omega, pow_succ]
  ring

private lemma two_pow_lt (k : ℕ) (hk : k ≥ 3) : 2 ^ (k - 1) + 1 < 2 ^ k := by
  have h1 := two_pow_helper k hk
  have h2 : 2 ≤ 2 ^ (k - 1) := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

private theorem pow2_sq_sub_one_dvd (k : ℕ) (hk : k ≥ 3) :
    2 ^ k ∣ ((2 ^ (k - 1) + 1) ^ 2 - 1) := by
  refine ⟨2 ^ (k - 2) + 1, ?_⟩
  set a := 2 ^ (k - 2)
  have ha1 : 2 ^ (k - 1) = 2 * a := by
    simp only [a]; conv_lhs => rw [show k - 1 = (k - 2) + 1 from by omega, pow_succ]
    exact mul_comm _ _
  have ha2 : 2 ^ k = 2 * (2 * a) := by
    have := two_pow_helper k hk; linarith
  have hsq : (2 * a + 1) ^ 2 = 4 * a * a + 4 * a + 1 := by ring
  have hrhs : 2 * (2 * a) * (a + 1) = 4 * a * a + 4 * a := by ring
  rw [ha1, ha2, hsq, hrhs]; omega

private theorem pow2_cast_sq_eq_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ^ 2 = 1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨by positivity⟩
  have hdvd := pow2_sq_sub_one_dvd k hk
  rw [show ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ^ 2 =
    ((((2 ^ (k - 1) + 1) ^ 2 : ℕ) : ZMod (2 ^ k))) from by push_cast; ring]
  have hge1 : 1 ≤ (2 ^ (k - 1) + 1) ^ 2 := by
    have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by omega); nlinarith [sq_nonneg (2 ^ (k - 1))]
  rw [show (2 ^ (k - 1) + 1) ^ 2 = ((2 ^ (k - 1) + 1) ^ 2 - 1) + 1 from by omega]
  rw [Nat.cast_add, Nat.cast_one]
  have : (((2 ^ (k - 1) + 1) ^ 2 - 1 : ℕ) : ZMod (2 ^ k)) = 0 := by
    rwa [ZMod.natCast_eq_zero_iff]
  rw [this]; simp

private theorem pow2_cast_ne_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ≠ 1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨by positivity⟩
  intro h
  have hlt := two_pow_lt k hk
  have hval := congr_arg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval
  have hv1 : ZMod.val (1 : ZMod (2 ^ k)) = 1 := by
    haveI : Fact (1 < 2 ^ k) := ⟨by
      calc 1 < 2 := by omega
        _ = 2 ^ 1 := by ring
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)⟩
    exact ZMod.val_one _
  rw [hv1] at hval
  have : 1 ≤ 2 ^ (k - 1) := Nat.one_le_pow _ _ (by omega); linarith

private theorem pow2_cast_ne_neg_one (k : ℕ) (hk : k ≥ 3) :
    ((2 ^ (k - 1) + 1 : ℕ) : ZMod (2 ^ k)) ≠ -1 := by
  haveI : NeZero (2 ^ k : ℕ) := ⟨by positivity⟩
  intro h
  have hlt := two_pow_lt k hk
  have hval := congr_arg ZMod.val h
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hval
  have hvm1 : ZMod.val (-1 : ZMod (2 ^ k)) = 2 ^ k - 1 := by
    have heq : 2 ^ k = (2 ^ k - 1) + 1 := by
      have : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega); omega
    conv => lhs; rw [heq]
    exact ZMod.val_neg_one _
  rw [hvm1] at hval
  have h1 := two_pow_helper k hk
  have h2 : 4 ≤ 2 ^ (k - 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel (by linarith : 1 ≤ 2 ^ k)
  linarith

private theorem exists_third_sqrt_pow2 (k : ℕ) (hk : k ≥ 3) :
    ∃ x : ZMod (2 ^ k), x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 :=
  ⟨_, pow2_cast_sq_eq_one k hk, pow2_cast_ne_one k hk, pow2_cast_ne_neg_one k hk⟩

private lemma is_pow2_of_no_odd_prime_factor {n : ℕ} (hn : n ≥ 3) (hn4 : n ≠ 4)
    (h_no_odd : ∀ p, Nat.Prime p → p ≠ 2 → ¬(p ∣ n)) :
    ∃ k, n = 2 ^ k ∧ k ≥ 3 := by
  have h_all2 : ∀ p, Nat.Prime p → p ∣ n → p = 2 := by
    intro p hp hpn; by_contra hne; exact h_no_odd p hp hne hpn
  have hn_ne : n ≠ 0 := by omega
  set v := n.factorization 2
  have hn_split : 2 ^ v * (n / 2 ^ v) = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have hcop : Nat.Coprime 2 (n / 2 ^ n.factorization 2) :=
    Nat.coprime_ordCompl Nat.prime_two hn_ne
  have h2_ndvd : ¬ (2 ∣ n / 2 ^ v) := by
    intro h2d
    have : 2 ∣ Nat.gcd 2 (n / 2 ^ v) := Nat.dvd_gcd (dvd_refl 2) h2d
    rw [hcop] at this; omega
  have hcompl_one : n / 2 ^ v = 1 := by
    by_contra hc
    have hcompl_pos : 0 < n / 2 ^ v := by
      apply Nat.pos_of_ne_zero; intro h0; rw [h0, mul_zero] at hn_split; omega
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hc
    have hq_dvd_n : q ∣ n := by rw [← hn_split]; exact dvd_mul_of_dvd_right hq_dvd _
    have hq2 : q = 2 := h_all2 q hq_prime hq_dvd_n
    subst hq2; exact h2_ndvd hq_dvd
  have hn_eq : n = 2 ^ v := by nlinarith [hn_split]
  refine ⟨v, hn_eq, ?_⟩
  by_contra hlt; push_neg at hlt
  interval_cases v <;> omega

private lemma coprime_split_of_odd_factor {n : ℕ} (hn : n ≥ 3)
    {p : ℕ} (hp : Nat.Prime p) (hp_odd : p ≠ 2) (hp_dvd : p ∣ n)
    (hform : ∀ q m, Nat.Prime q → Odd q → 1 ≤ m → n ≠ q ^ m ∧ n ≠ 2 * q ^ m) :
    ∃ a b, n = a * b ∧ Nat.Coprime a b ∧ a ≥ 3 ∧ b ≥ 3 := by
  set v := n.factorization p
  set a := p ^ v
  set b := n / a
  have hn_ne : n ≠ 0 := by omega
  have hv_pos : v ≥ 1 := by
    simp only [v, ge_iff_le, Nat.one_le_iff_ne_zero]
    have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hp_dvd, hn_ne⟩
    rw [← Nat.support_factorization] at hp_mem
    exact Finsupp.mem_support_iff.mp hp_mem
  have hv_ne : v ≠ 0 := by omega
  have ha_ge : a ≥ 3 := by
    have ha_ge_p : a ≥ p := le_self_pow₀ hp.one_le hv_ne
    have hp_ge : p ≥ 3 := by
      have h2le := hp.two_le
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp_odd
      · have : Odd p := Nat.odd_iff.mpr h; obtain ⟨k, hk⟩ := this; omega
    omega
  have hab_eq : n = a * b := by
    simp only [a, b]; exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hab_cop : Nat.Coprime a b := by
    simp only [a, b]
    exact (Nat.coprime_ordCompl hp hn_ne).pow_left v
  have hp_odd' : Odd p := by
    rcases hp.eq_two_or_odd with h | h; exact absurd h hp_odd; exact Nat.odd_iff.mpr h
  have hb_ne1 : b ≠ 1 := by
    intro hb1; have : n = a := by rw [hab_eq, hb1, mul_one]
    exact (hform p v hp hp_odd' hv_pos).1 (this ▸ rfl)
  have hb_ne2 : b ≠ 2 := by
    intro hb2; have : n = 2 * a := by rw [hab_eq, hb2]; ring
    exact (hform p v hp hp_odd' hv_pos).2 this
  have hb_pos : 0 < b := by
    by_contra h; push_neg at h; simp at h; rw [h] at hab_eq; simp at hab_eq; omega
  exact ⟨a, b, hab_eq, hab_cop, ha_ge, by omega⟩

/-- **Key number-theoretic input.**  When `(ZMod n)ˣ` is not cyclic (`n ≥ 3`),
    there is a square root of unity in `ZMod n` other than `±1`. -/
private theorem exists_third_sqrt_of_not_cyclic {n : ℕ} (hn : n ≥ 3)
    [_hne : NeZero n] (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    ∃ x : ZMod n, x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ -1 := by
  rw [ZMod.isCyclic_units_iff] at hncyc
  push_neg at hncyc
  obtain ⟨_, _, _, hn4, hform⟩ := hncyc
  by_cases h_has_odd : ∃ p, Nat.Prime p ∧ p ≠ 2 ∧ p ∣ n
  · obtain ⟨p, hp, hp2, hpn⟩ := h_has_odd
    obtain ⟨a, b, hab_eq, hab_cop, ha, hb⟩ :=
      coprime_split_of_odd_factor hn hp hp2 hpn hform
    rw [hab_eq]; exact exists_third_sqrt_coprime hab_cop ha hb
  · push_neg at h_has_odd
    obtain ⟨k, hk_eq, hk_ge⟩ :=
      is_pow2_of_no_odd_prime_factor hn hn4 (fun p hp hp2 => h_has_odd p hp hp2)
    rw [hk_eq]; exact exists_third_sqrt_pow2 k hk_ge

/-- When not cyclic, the 2-torsion of `(ZMod n)ˣ` has at least `3` elements. -/
private theorem card_two_torsion_units_ge_three {n : ℕ} (hn : n ≥ 3) [_hne : NeZero n]
    (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    3 ≤ (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
  obtain ⟨x, hx_sq, hx_ne1, hx_neN1⟩ := exists_third_sqrt_of_not_cyclic hn hncyc
  let u := unitOfSqEqOne x hx_sq
  have hu_sq : u ^ 2 = 1 := unitOfSqEqOne_sq x hx_sq
  have hu_ne1 : u ≠ 1 := unitOfSqEqOne_ne_one hx_sq hx_ne1
  have hu_neN1 : u ≠ -1 := unitOfSqEqOne_ne_neg_one hx_sq hx_neN1
  have hne_1_N1 : (1 : (ZMod n)ˣ) ≠ -1 := (neg_one_ne_one_units hn).symm
  have hsub : {1, -1, u} ⊆ Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl | rfl
    · simp
    · simp
    · exact hu_sq
  have hcard3 : ({1, -1, u} : Finset (ZMod n)ˣ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (h | h); exact hne_1_N1 h; exact hu_ne1 h.symm)]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]; exact fun h => hu_neN1 h.symm)]
    rw [Finset.card_singleton]
  linarith [Finset.card_le_card hsub]

-- ============================================================================
-- Section 7: Gauss-Wilson — assembled, self-contained
-- ============================================================================

/-- **Non-cyclic Gauss-Wilson (direct involution, self-contained).**

    When `(ZMod n)ˣ` is not cyclic and `n ≥ 3`, the product of all units is `1`. -/
theorem prod_units_one_of_not_cyclic {n : ℕ} (hn : n ≥ 3)
    [hne : NeZero n] (hncyc : ¬ IsCyclic (ZMod n)ˣ) :
    ∏ x : (ZMod n)ˣ, (x : ZMod n) = 1 := by
  suffices hprod : ∏ x : (ZMod n)ˣ, x = 1 by
    rw [show (∏ x : (ZMod n)ˣ, (x : ZMod n)) = (↑(∏ x : (ZMod n)ˣ, x) : ZMod n) from
      (units_val_prod _ _).symm, hprod]
    simp
  rw [prod_eq_prod_two_torsion]
  exact prod_two_torsion_eq_one (ZMod n)ˣ (card_two_torsion_units_ge_three hn hncyc)

/-- **Cyclic Gauss-Wilson.**  When `(ZMod n)ˣ` is cyclic and `n ≥ 3`, the product
    of all units is `-1`.  Here the 2-torsion is exactly `{1, -1}`. -/
theorem prod_units_neg_one_of_cyclic {n : ℕ} (hn : n ≥ 3)
    [hne : NeZero n] [hcyc : IsCyclic (ZMod n)ˣ] :
    ∏ x : (ZMod n)ˣ, (x : ZMod n) = -1 := by
  suffices hprod : ∏ x : (ZMod n)ˣ, x = -1 by
    rw [show (∏ x : (ZMod n)ˣ, (x : ZMod n)) = (↑(∏ x : (ZMod n)ˣ, x) : ZMod n) from
      (units_val_prod _ _).symm, hprod]; simp
  rw [prod_eq_prod_two_torsion]
  have hle := IsCyclic.card_pow_eq_one_le (α := (ZMod n)ˣ) (by norm_num : 0 < 2)
  have h1_mem : (1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hn1_mem : (-1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hne' : (1 : (ZMod n)ˣ) ≠ -1 := (neg_one_ne_one_units hn).symm
  have hsub : {1, -1} ⊆ Finset.univ.filter (fun (x : (ZMod n)ˣ) => x ^ 2 = 1) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard_pair : ({1, -1} : Finset (ZMod n)ˣ).card = 2 := Finset.card_pair hne'
  have heq := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  rw [heq, Finset.prod_pair hne']
  exact one_mul (-1)

/-- **Gauss-Wilson Theorem.**  For `n ≥ 3`,
    `∏ units = -1` iff `(ZMod n)ˣ` is cyclic. -/
theorem gaussWilson {n : ℕ} (hn : n ≥ 3) [hne : NeZero n] :
    (∏ x : (ZMod n)ˣ, (x : ZMod n) = -1) ↔ IsCyclic (ZMod n)ˣ := by
  constructor
  · intro hprod
    by_contra hncyc
    have h1 := prod_units_one_of_not_cyclic hn hncyc
    rw [h1] at hprod
    exact neg_one_ne_one_zmod hn hprod.symm
  · intro hcyc
    exact @prod_units_neg_one_of_cyclic n hn hne hcyc

#check @prod_two_torsion_eq_one
#check @card_two_torsion_eq_pow_two
#check @prod_units_one_of_not_cyclic
#check @gaussWilson

end WilsonsTheoremOQ02OQ02
