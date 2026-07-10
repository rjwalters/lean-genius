import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Burnside's Lemma and Counting Applications

## What This Proves

We demonstrate Burnside's lemma (also known as the Cauchy-Frobenius lemma
or the orbit-counting theorem) and apply it to counting necklaces.

**Burnside's Lemma**: For a finite group G acting on a finite set X, the number of
orbits equals the average number of fixed points:
  |X/G| = (1/|G|) * Σ_{g ∈ G} |Fix(g)|

Or equivalently (avoiding division):
  Σ_{g ∈ G} |Fix(g)| = |X/G| * |G|

## Applications

1. **Binary Necklaces of Length 4**: We prove there are exactly 6 distinct
   binary necklaces under cyclic rotation, using Burnside's lemma computationally.

## Status
- [x] Burnside's lemma statement (from Mathlib)
- [x] Cyclic group action on colorings
- [x] Binary necklace counting example (with axioms for modular arithmetic)

## Mathlib Dependencies
- `Mathlib.GroupTheory.GroupAction.Quotient` : Burnside's lemma
- `Mathlib.Data.ZMod.Basic` : Z/nZ arithmetic
-/

namespace BurnsideCounting

open Finset MulAction

/-! ## Part I: Burnside's Lemma from Mathlib -/

/-- **Burnside's Lemma (Cauchy-Frobenius Lemma)**:
    For a finite group G acting on a set X, the sum of fixed point counts
    equals the number of orbits times the group size.

    This is the multiplicative form that avoids division. -/
theorem burnside_lemma {G : Type*} {X : Type*} [Group G] [MulAction G X]
    [Fintype G] [(g : G) → Fintype (fixedBy X g)] [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
      Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X

/-! ## Part II: Cyclic Group Action on Finite Colorings

We define colorings of Fin n with Fin k colors, and the cyclic group Z_n
acting by rotation. -/

/-- A coloring assigns to each of n positions one of k colors. -/
abbrev Coloring (n k : ℕ) := Fin n → Fin k

/-- Rotate a coloring by an element of Z_n.
    The rotation sends position i to position (i - r). -/
def rotateColoring (n k : ℕ) [NeZero n] (r : ZMod n) (c : Coloring n k) : Coloring n k :=
  fun i => c ⟨((i : ℕ) + n - (r.val % n)) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Helper: compute the rotated index. -/
def rotatedIndex (n : ℕ) [NeZero n] (r : ZMod n) (i : Fin n) : Fin n :=
  ⟨((i : ℕ) + n - (r.val % n)) % n, Nat.mod_lt _ (NeZero.pos n)⟩

/-- Zero rotation leaves index unchanged.
    Proof: (i + n - 0) % n = (i + n) % n = i for i < n. -/
theorem rotatedIndex_zero (n : ℕ) [NeZero n] (i : Fin n) :
    rotatedIndex n 0 i = i := by
  simp only [rotatedIndex, ZMod.val_zero, Nat.zero_mod, Nat.sub_zero]
  ext
  simp only [Fin.val_mk]
  have hi : i.val < n := i.isLt
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hi

/-- Auxiliary: for `0 ≤ a < 2n` and `n ≤ a`, the value `a % n` is `a - n`.
    Reformulates a common omega-resistant identity via `Nat.add_mod_right`. -/
private lemma mod_eq_sub (a n : ℕ) (h1 : n ≤ a) (h2 : a < 2 * n) :
    a % n = a - n := by
  conv_lhs =>
    rw [show a = (a - n) + n from by omega]
  rw [Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- Auxiliary: rewrite `(a + n) % n` style expressions by absorbing the
    leading `n`.  Used to peel off the outer `+ n` from `(i.val + n - r.val + n - s.val) % n`-shape arguments
    when the underlying value is < `n`. -/
private lemma mod_of_shift (a c n : ℕ) (h_eq : a = c + n) (h_lt : c < n) :
    a % n = c := by
  rw [h_eq, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt h_lt

/-- Auxiliary: when the argument is < n, mod is identity, but expressed
    with a Nat-`omega`-verifiable equal target rather than the literal arg. -/
private lemma mod_of_eq (a b n : ℕ) (h_eq : a = b) (h_lt : a < n) :
    a % n = b := by
  rw [h_eq]
  exact Nat.mod_eq_of_lt (h_eq ▸ h_lt)

/-- Rotation by `r` then `s` equals rotation by `r + s`.
    Proof: reduce to a `ℕ`-modular `Fin.val` identity, then enumerate the
    8 sign-cases of `(i.val ⋚ r.val) × (r.val + s.val ⋚ n) × (i.val ⋚ r.val + s.val - n)`
    where applicable.  Each leaf normalizes both sides to the same `ℕ`
    value using the auxiliaries `mod_eq_sub` / `mod_of_shift` / `mod_of_eq`. -/
theorem rotatedIndex_add (n : ℕ) [NeZero n] (r s : ZMod n) (i : Fin n) :
    rotatedIndex n s (rotatedIndex n r i) = rotatedIndex n (r + s) i := by
  have hn : 0 < n := NeZero.pos n
  have hr : r.val < n := ZMod.val_lt r
  have hs : s.val < n := ZMod.val_lt s
  have hi : i.val < n := i.isLt
  have hrs : (r + s).val = (r.val + s.val) % n := ZMod.val_add r s
  apply Fin.ext
  show ((i.val + n - r.val % n) % n + n - s.val % n) % n
      = (i.val + n - (r + s).val % n) % n
  rw [hrs, Nat.mod_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs]
  -- Case A: `i.val ≥ r.val`.  Pull a single `n` out of the inner mod.
  by_cases hir : r.val ≤ i.val
  · have h_inner : (i.val + n - r.val) % n = i.val - r.val := by
      apply mod_of_shift _ _ _ (by omega : i.val + n - r.val = (i.val - r.val) + n)
      omega
    rw [h_inner]
    by_cases hi_rs : i.val < r.val + s.val
    · -- Sub-case A1: `i.val - r.val < s.val`.  LHS is in range.
      have hlhs : (i.val - r.val + n - s.val) % n
          = i.val - r.val + n - s.val :=
        Nat.mod_eq_of_lt (by omega)
      by_cases hsum : r.val + s.val < n
      · have h_sum : (r.val + s.val) % n = r.val + s.val :=
          Nat.mod_eq_of_lt hsum
        rw [h_sum]
        have hrhs : (i.val + n - (r.val + s.val)) % n
            = i.val + n - r.val - s.val :=
          mod_of_eq _ _ _ (by omega) (by omega)
        rw [hlhs, hrhs]
        omega
      · push_neg at hsum
        have h_sum : (r.val + s.val) % n = r.val + s.val - n :=
          mod_eq_sub _ _ (by omega) (by omega)
        rw [h_sum]
        have hrhs : (i.val + n - (r.val + s.val - n)) % n
            = i.val - r.val + n - s.val :=
          mod_of_shift _ _ _ (by omega) (by omega)
        rw [hlhs, hrhs]
    · -- Sub-case A2: `i.val ≥ r.val + s.val`.  Then `r.val + s.val < n`.
      push_neg at hi_rs
      have hsum : r.val + s.val < n := by omega
      have h_sum : (r.val + s.val) % n = r.val + s.val :=
        Nat.mod_eq_of_lt hsum
      rw [h_sum]
      have hlhs : (i.val - r.val + n - s.val) % n = i.val - r.val - s.val :=
        mod_of_shift _ _ _ (by omega) (by omega)
      have hrhs : (i.val + n - (r.val + s.val)) % n = i.val - r.val - s.val :=
        mod_of_shift _ _ _ (by omega) (by omega)
      rw [hlhs, hrhs]
  · -- Case B: `i.val < r.val`.  Inner mod is identity.
    push_neg at hir
    have h_inner : (i.val + n - r.val) % n = i.val + n - r.val :=
      Nat.mod_eq_of_lt (by omega)
    rw [h_inner]
    by_cases hsum : r.val + s.val < n
    · -- Sub-case B1: `r.val + s.val < n`.
      have h_sum : (r.val + s.val) % n = r.val + s.val :=
        Nat.mod_eq_of_lt hsum
      rw [h_sum]
      have hlhs : (i.val + n - r.val + n - s.val) % n
          = i.val + n - r.val - s.val :=
        mod_of_shift _ _ _ (by omega) (by omega)
      have hrhs : (i.val + n - (r.val + s.val)) % n
          = i.val + n - r.val - s.val :=
        mod_of_eq _ _ _ (by omega) (by omega)
      rw [hlhs, hrhs]
    · -- Sub-case B2: `r.val + s.val ≥ n`.  Further split.
      push_neg at hsum
      have h_sum : (r.val + s.val) % n = r.val + s.val - n :=
        mod_eq_sub _ _ (by omega) (by omega)
      rw [h_sum]
      by_cases hi_rs_n : r.val + s.val - n ≤ i.val
      · -- Sub-case B2a: both wrap.
        have hlhs : (i.val + n - r.val + n - s.val) % n
            = i.val + n - r.val - s.val :=
          mod_of_shift _ _ _ (by omega) (by omega)
        have hrhs : (i.val + n - (r.val + s.val - n)) % n
            = i.val + n - r.val - s.val :=
          mod_of_shift _ _ _ (by omega) (by omega)
        rw [hlhs, hrhs]
      · -- Sub-case B2b: `i.val < r.val + s.val - n`.  Both stay in range.
        push_neg at hi_rs_n
        have hlhs : (i.val + n - r.val + n - s.val) % n
            = i.val + n - r.val + n - s.val :=
          Nat.mod_eq_of_lt (by omega)
        have hrhs : (i.val + n - (r.val + s.val - n)) % n
            = i.val + n - r.val + n - s.val :=
          mod_of_eq _ _ _ (by omega) (by omega)
        rw [hlhs, hrhs]

/-- The rotation action forms an additive group action of Z_n on colorings.
    The zero_vadd and add_vadd properties follow from index rotation lemmas. -/
instance cyclicAddActionOnColorings (n k : ℕ) [NeZero n] :
    AddAction (ZMod n) (Coloring n k) where
  vadd := rotateColoring n k
  zero_vadd := fun c => by
    funext i
    show rotateColoring n k 0 c i = c i
    unfold rotateColoring
    have h := rotatedIndex_zero n i
    simp only [rotatedIndex, ZMod.val_zero, Nat.zero_mod, Nat.sub_zero] at h
    simp only [ZMod.val_zero, Nat.zero_mod, Nat.sub_zero, h]
  add_vadd := fun r s c => by
    funext i
    show rotateColoring n k (r + s) c i = rotateColoring n k r (rotateColoring n k s c) i
    unfold rotateColoring
    have h := rotatedIndex_add n r s i
    have hr : r.val % n = r.val := Nat.mod_eq_of_lt (ZMod.val_lt r)
    have hs : s.val % n = s.val := Nat.mod_eq_of_lt (ZMod.val_lt s)
    simp only [rotatedIndex, hr, hs] at h
    simp only [hr, hs]
    congr 1
    exact h.symm

/-! ## Part III: Concrete Example - Binary 4-Necklaces

We verify the classic result: there are 6 distinct binary necklaces of length 4.

The 6 equivalence classes under rotation are:
1. {0000}
2. {0001, 0010, 0100, 1000}
3. {0011, 0110, 1100, 1001}
4. {0101, 1010}
5. {0111, 1110, 1101, 1011}
6. {1111}

By Burnside's lemma, we compute:
- |Fix(0)| = 16 (identity fixes all 2^4 colorings)
- |Fix(1)| = 2 (only 0000 and 1111 have period 1)
- |Fix(2)| = 4 (period divides 2: 0000, 0101, 1010, 1111)
- |Fix(3)| = 2 (same as rotation by 1)

Sum = 16 + 2 + 4 + 2 = 24
Orbits = 24 / 4 = 6 -/

/-- Total number of binary colorings of 4 positions. -/
theorem binary_4_colorings_count : Fintype.card (Coloring 4 2) = 16 := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  norm_num

/-- A coloring is constant if all positions have the same color. -/
def IsConstant {n k : ℕ} (c : Coloring n k) : Prop :=
  ∀ i j : Fin n, c i = c j

/-- Constant colorings are decidable. -/
instance {n k : ℕ} [NeZero n] : DecidablePred (@IsConstant n k) :=
  fun c => decidable_of_iff (∀ i, c i = c 0) ⟨
    fun h i j => (h i).trans (h j).symm,
    fun h i => h i 0
  ⟩

/-- Number of constant colorings equals k. -/
theorem constant_coloring_count (n k : ℕ) [NeZero n] :
    Fintype.card { c : Coloring n k // IsConstant c } = k := by
  -- Bijection with Fin k: a constant coloring is determined by c(0)
  let f : { c : Coloring n k // IsConstant c } → Fin k := fun ⟨c, _⟩ => c 0
  let g : Fin k → { c : Coloring n k // IsConstant c } :=
    fun v => ⟨fun _ => v, fun _ _ => rfl⟩
  have hfg : Function.LeftInverse g f := fun ⟨c, hc⟩ => by
    simp only [f, g, Subtype.mk.injEq]
    funext i
    exact hc 0 i
  have hgf : Function.RightInverse g f := fun v => rfl
  have heq := Fintype.card_eq.mpr ⟨Equiv.ofBijective f ⟨hfg.injective, hgf.surjective⟩⟩
  simp only [Fintype.card_fin] at heq
  exact heq

/-- For n=4, k=2: there are 2 constant colorings. -/
theorem constant_4_2 : Fintype.card { c : Coloring 4 2 // IsConstant c } = 2 :=
  constant_coloring_count 4 2

/-- A coloring has period dividing 2 (for n=4). -/
def HasPeriod2 (c : Coloring 4 2) : Prop :=
  c 0 = c 2 ∧ c 1 = c 3

instance : DecidablePred HasPeriod2 :=
  fun c => show Decidable (c 0 = c 2 ∧ c 1 = c 3) from inferInstance

/-- Period-2 colorings are determined by first two values. -/
theorem period2_count : Fintype.card { c : Coloring 4 2 // HasPeriod2 c } = 4 := by
  -- Bijection with Fin 2 × Fin 2
  let f : { c : Coloring 4 2 // HasPeriod2 c } → Fin 2 × Fin 2 := fun ⟨c, _⟩ => (c 0, c 1)
  let g : Fin 2 × Fin 2 → { c : Coloring 4 2 // HasPeriod2 c } :=
    fun ⟨a, b⟩ => ⟨![a, b, a, b], ⟨rfl, rfl⟩⟩
  have hfg : Function.LeftInverse g f := fun ⟨c, hc⟩ => by
    simp only [f, g]
    ext i
    fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hc.1, hc.2]
  have hgf : Function.RightInverse g f := fun ⟨a, b⟩ => by
    simp [f, g, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  have := Fintype.card_eq.mpr ⟨Equiv.ofBijective f ⟨hfg.injective, hgf.surjective⟩⟩
  rw [this]
  simp [Fintype.card_prod, Fintype.card_fin]

/-! ## Part IV: Summary

We have demonstrated:
1. Burnside's lemma from Mathlib
2. Cyclic group action on colorings
3. Counting constant and period-2 colorings

The key counts for binary 4-necklaces:
- |Fix(identity)| = 16 (all colorings)
- |Fix(rotation by 1)| = 2 (constant colorings)
- |Fix(rotation by 2)| = 4 (period-2 colorings)
- |Fix(rotation by 3)| = 2 (constant colorings)

By Burnside: (16 + 2 + 4 + 2) / 4 = 6 distinct necklaces.

The full computation of |orbits| = 6 would require showing the fixed-point
sets have the cardinalities above and applying Burnside's lemma. The key
infrastructure (action definition, fixed-point characterization) is in place. -/

/-- A coloring is fixed by rotation r if rotating by r gives the same coloring. -/
def IsFixedByRotation {n k : ℕ} [NeZero n] (r : ZMod n) (c : Coloring n k) : Prop :=
  r +ᵥ c = c

instance {n k : ℕ} [NeZero n] (r : ZMod n) : DecidablePred (@IsFixedByRotation n k _ r) :=
  fun c => decidable_of_iff (∀ i, (r +ᵥ c) i = c i)
    ⟨fun h => funext h, fun h i => congrFun h i⟩

/-- Two colorings are equivalent if one is a rotation of the other. -/
def ColoringEquiv {n k : ℕ} [NeZero n] (c₁ c₂ : Coloring n k) : Prop :=
  ∃ r : ZMod n, r +ᵥ c₁ = c₂

/-- The fixed point sum for binary 4-necklaces.
    - |Fix(0)| = 16 (identity fixes all)
    - |Fix(1)| = 2 (only constant colorings)
    - |Fix(2)| = 4 (period-2 colorings)
    - |Fix(3)| = 2 (only constant colorings)
    Sum = 24.

    Discharged by `decide` (S3 originally used `native_decide`; the S5 drift
    repair for Mathlib v4.26 switched to the kernel tactic `decide`, which
    both fixes a native-compilation crash and removes the `Lean.ofReduceBool`
    dependency for this theorem):
    `Coloring 4 2 = Fin 4 → Fin 2` is finite; `IsFixedByRotation r` is
    decidable (instance above); hence
    `Fintype.card { c // IsFixedByRotation r c }` is computable and the
    arithmetic identity is verified by kernel evaluation of `decide`. -/
theorem fixed_point_sum_binary_4 :
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 0 c } +
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 1 c } +
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 2 c } +
    Fintype.card { c : Coloring 4 2 // IsFixedByRotation 3 c } = 24 := by
  decide

/-- The equivalence relation on colorings by rotation.
    Derived from `AddAction.orbitRel` (replacing the prior axiom): two
    colorings are equivalent iff one is a rotation (in `ZMod n`) of the
    other. -/
def coloringSetoid (n k : ℕ) [NeZero n] : Setoid (Coloring n k) :=
  AddAction.orbitRel (ZMod n) (Coloring n k)

/-- The orbit relation on colorings is decidable: two colorings are in
    the same orbit iff `∃ r : ZMod n, r +ᵥ b = a`, which is decidable
    because `ZMod n` is a `Fintype` and equality of colorings is
    decidable (`Fin n → Fin k` has decidable equality). -/
instance coloringSetoid_decidableRel (n k : ℕ) [NeZero n] :
    DecidableRel (coloringSetoid n k).r := fun a b =>
  decidable_of_iff (∃ x : ZMod n, x +ᵥ b = a) AddAction.mem_orbit_iff.symm

/-- The quotient of colorings by rotation has a Fintype instance,
    derived via `Quotient.fintype` from the finite carrier `Coloring n k`
    and the decidable orbit relation above.  Replaces the prior axiom. -/
def coloringQuotientFintype (n k : ℕ) [NeZero n] :
    Fintype (Quotient (@coloringSetoid n k _)) := by
  letI : Setoid (Coloring n k) := coloringSetoid n k
  haveI : DecidableRel (α := Coloring n k) (· ≈ ·) := coloringSetoid_decidableRel n k
  exact Quotient.fintype _

/-- **Binary Necklaces of Length 4**:
    There are exactly 6 distinct binary necklaces of length 4.

    Mathematically this is Burnside's lemma: `(16 + 2 + 4 + 2) / 4 = 6`.

    S4 originally discharged this by `native_decide` over the computable
    `coloringQuotientFintype 4 2`, enumerating the orbit quotient directly.
    The S5 drift repair replaces that with a genuine application of Mathlib's
    additive Burnside lemma
    `AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup`:
      `∑ a : ZMod 4, |Fix a| = |orbits| * |ZMod 4|`.
    The fixed-point sum is `24` (`fixed_point_sum_binary_4`, whose subtypes
    `{c // IsFixedByRotation a c}` are defeq to `fixedBy (Coloring 4 2) a`)
    and `|ZMod 4| = 4`, so `|orbits| * 4 = 24`, giving `|orbits| = 6` by
    arithmetic — no quotient enumeration required. This route is kernel-checked
    (no `native_decide`, no `Lean.ofReduceBool`): it counts orbits from the
    fixed-point data rather than by native evaluation of the quotient. -/
theorem binary_necklaces_4 :
    @Fintype.card (Quotient (@coloringSetoid 4 2 _)) (coloringQuotientFintype 4 2) = 6 := by
  -- Supply the orbit-quotient `Fintype` in BOTH the `coloringSetoid` form (used
  -- by the goal / calc LHS) and the defeq `orbitRel` form (used by Burnside's
  -- `hb` and the calc RHS), both as `coloringQuotientFintype 4 2`, so every
  -- `Fintype.card` of the quotient resolves to the same instance.
  letI : Fintype (Quotient (@coloringSetoid 4 2 _)) := coloringQuotientFintype 4 2
  letI : Fintype (Quotient (AddAction.orbitRel (ZMod 4) (Coloring 4 2))) :=
    coloringQuotientFintype 4 2
  -- Additive Burnside: `∑ a, |Fix a| = |orbits| * |ZMod 4|`.
  have hb := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (ZMod 4) (Coloring 4 2)
  -- `fixedBy (Coloring 4 2) a` and `{c // IsFixedByRotation a c}` are defeq.
  have hbridge : ∀ a : ZMod 4,
      Fintype.card (AddAction.fixedBy (Coloring 4 2) a) =
        Fintype.card { c : Coloring 4 2 // IsFixedByRotation a c } := fun a =>
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hsum : (∑ a : ZMod 4, Fintype.card (AddAction.fixedBy (Coloring 4 2) a)) = 24 := by
    simp only [hbridge]
    decide
  have hcard : Fintype.card (ZMod 4) = 4 := by decide
  rw [hsum, hcard] at hb
  -- hb : 24 = Fintype.card (Quotient (orbitRel (ZMod 4) (Coloring 4 2))) * 4.
  -- Bridge the goal's quotient (`coloringSetoid` form + `coloringQuotientFintype`
  -- instance) to Burnside's (`orbitRel` form) in term mode; a `rw` would force
  -- the kernel to reduce `coloringQuotientFintype`, which is expensive.
  calc @Fintype.card (Quotient (@coloringSetoid 4 2 _)) (coloringQuotientFintype 4 2)
      = Fintype.card (Quotient (AddAction.orbitRel (ZMod 4) (Coloring 4 2))) :=
        Fintype.card_congr (Equiv.refl _)
    _ = 6 := by omega

/-! ## Part V: A Reusable Necklace-Count Engine

The `binary_necklaces_4` proof hard-codes the Burnside orbit-count step for
`(n, k) = (4, 2)`.  The lemma below factors out that step for **arbitrary**
length `n ≥ 1` and palette size `k`: given the fixed-point sum
`∑_{a : ZMod n} |Fix a|`, it returns `|necklaces| · n`.  Any concrete necklace
count then reduces to evaluating one finite sum (by `decide`) and a single
`omega`, with no `native_decide` and no `Lean.ofReduceBool` dependency.  As a
demonstration we count the binary necklaces of length 3. -/

/-- **General necklace-count engine.**  For any length `n ≥ 1` and palette
    size `k`, the additive Burnside identity specializes to
    `∑_{a : ZMod n} |Fix a| = |necklaces| · n`, where `|necklaces|` is the
    number of rotation orbits of `Coloring n k` (counted with the computable
    `coloringQuotientFintype`).  This packages the fixed-point-sum ⟹
    orbit-count step so that any concrete `(n, k)` is a one-line corollary.

    The proof is Mathlib's additive Burnside lemma
    `AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup` composed with
    the `fixedBy ≃ {c // IsFixedByRotation}` bridge (defeq) and `|ZMod n| = n`;
    it is kernel-checked with no native evaluation. -/
theorem sum_fixedBy_eq_card_necklaces_mul (n k : ℕ) [NeZero n] :
    (∑ a : ZMod n, Fintype.card { c : Coloring n k // IsFixedByRotation a c })
      = @Fintype.card (Quotient (@coloringSetoid n k _))
          (coloringQuotientFintype n k) * n := by
  -- Pin BOTH quotient forms (goal's `coloringSetoid`, Burnside's `orbitRel`)
  -- to the same computable instance so every `Fintype.card` agrees.
  letI : Fintype (Quotient (@coloringSetoid n k _)) := coloringQuotientFintype n k
  letI : Fintype (Quotient (AddAction.orbitRel (ZMod n) (Coloring n k))) :=
    coloringQuotientFintype n k
  have hb := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (ZMod n) (Coloring n k)
  -- `fixedBy (Coloring n k) a` and `{c // IsFixedByRotation a c}` are defeq.
  have hbridge : ∀ a : ZMod n,
      Fintype.card (AddAction.fixedBy (Coloring n k) a) =
        Fintype.card { c : Coloring n k // IsFixedByRotation a c } := fun a =>
    Fintype.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  have hcard : Fintype.card (ZMod n) = n := ZMod.card n
  simp only [hbridge] at hb
  rw [hcard] at hb
  calc (∑ a : ZMod n, Fintype.card { c : Coloring n k // IsFixedByRotation a c })
      = Fintype.card (Quotient (AddAction.orbitRel (ZMod n) (Coloring n k))) * n := hb
    _ = @Fintype.card (Quotient (@coloringSetoid n k _))
          (coloringQuotientFintype n k) * n := rfl

/-- The fixed-point sum for binary 3-necklaces.
    - |Fix(0)| = 8 (identity fixes all `2^3` colorings)
    - |Fix(1)| = 2 (only the two constant colorings have period 1)
    - |Fix(2)| = 2 (same as rotation by 1)
    Sum = 12.  Kernel-evaluated by `decide` (each `IsFixedByRotation r` is
    decidable and `Coloring 3 2 = Fin 3 → Fin 2` is finite). -/
theorem fixed_point_sum_binary_3 :
    Fintype.card { c : Coloring 3 2 // IsFixedByRotation 0 c } +
    Fintype.card { c : Coloring 3 2 // IsFixedByRotation 1 c } +
    Fintype.card { c : Coloring 3 2 // IsFixedByRotation 2 c } = 12 := by
  decide

/-- **Binary Necklaces of Length 3**: there are exactly 4 distinct binary
    necklaces of length 3.  The rotation classes of `Coloring 3 2` are
    `{000}`, `{001, 010, 100}`, `{011, 110, 101}`, `{111}`.

    Mathematically this is Burnside's lemma: `(8 + 2 + 2) / 3 = 4`.  Derived
    from the general engine `sum_fixedBy_eq_card_necklaces_mul`: the
    fixed-point sum is `12` (kernel-`decide`) and `12 = |necklaces| * 3`, so
    `|necklaces| = 4` by `omega`.  No quotient enumeration, no
    `native_decide`. -/
theorem binary_necklaces_3 :
    @Fintype.card (Quotient (@coloringSetoid 3 2 _))
      (coloringQuotientFintype 3 2) = 4 := by
  have h := sum_fixedBy_eq_card_necklaces_mul 3 2
  rw [show (∑ a : ZMod 3,
      Fintype.card { c : Coloring 3 2 // IsFixedByRotation a c }) = 12 from by decide] at h
  omega

/-! ## Part VI: The Primitive-Rotation Fixed-Point Count

The concrete facts `|Fix(1)| = |Fix(3)| = 2` used in `fixed_point_sum_binary_4`
are the `(n, k) = (4, 2)` instances of a general theorem: when the rotation
amount `r` is a **unit** of `ZMod n` (equivalently `gcd(r, n) = 1`, i.e. `r`
generates the cyclic group), the only colorings fixed by `r` are the constant
ones, so `|Fix(r)| = k`.  This is the `gcd = 1` case of the classical necklace
fixed-point formula `|Fix(r)| = k ^ gcd(r, n)`; it feeds the general engine
`sum_fixedBy_eq_card_necklaces_mul` and evaluates the primitive-rotation fixed
sets with no `decide` cost. -/

/-- Iterating a fixed rotation: if `c` is fixed by `r` then it is fixed by every
    natural multiple `m • r`.  Proof by induction on `m` using only the
    `AddAction` axioms (`zero_vadd`, `add_vadd`). -/
theorem isFixed_nsmul {n k : ℕ} [NeZero n] {r : ZMod n} {c : Coloring n k}
    (h : r +ᵥ c = c) : ∀ m : ℕ, (m • r) +ᵥ c = c := by
  intro m
  induction m with
  | zero => rw [zero_nsmul, zero_vadd]
  | succ m ih => rw [succ_nsmul, add_vadd, h, ih]

/-- A coloring fixed by the rotation `1` is constant: rotation by `1` sends
    position `i` to `i - 1`, so `c(i) = c(i-1)` for every `i`; iterating around
    the `n`-cycle forces every position to agree with position `0`. -/
theorem isConstant_of_isFixedByRotation_one {n k : ℕ} [NeZero n]
    {c : Coloring n k} (h : IsFixedByRotation (1 : ZMod n) c) : IsConstant c := by
  have hn : 0 < n := NeZero.pos n
  have h' : rotateColoring n k 1 c = c := h
  suffices hbase : ∀ m (hm : m < n), c ⟨m, hm⟩ = c ⟨0, hn⟩ by
    intro i j
    calc c i = c ⟨i.val, i.isLt⟩ := by rw [Fin.eta]
      _ = c ⟨0, hn⟩ := hbase i.val i.isLt
      _ = c ⟨j.val, j.isLt⟩ := (hbase j.val j.isLt).symm
      _ = c j := by rw [Fin.eta]
  rcases eq_or_ne n 1 with hn1 | hn1
  · -- `n = 1`: only position `0` exists.
    intro m hm
    have : m = 0 := by omega
    subst this
    rfl
  · haveI : Fact (1 < n) := ⟨by omega⟩
    have hv1 : (1 : ZMod n).val = 1 := ZMod.val_one n
    intro m
    induction m with
    | zero => intro hm; rfl
    | succ m ih =>
      intro hm
      -- Rotation by `1` sends position `m + 1` to position `m`.
      have hrot : rotatedIndex n 1 ⟨m + 1, hm⟩ = ⟨m, by omega⟩ := by
        apply Fin.ext
        simp only [rotatedIndex, Fin.val_mk, hv1]
        have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1n]
        have he : (m + 1) + n - 1 = m + n := by omega
        rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : m < n)]
      have step : c ⟨m, by omega⟩ = c ⟨m + 1, hm⟩ := by
        have hi := congrFun h' ⟨m + 1, hm⟩
        rw [show rotateColoring n k 1 c ⟨m + 1, hm⟩
              = c (rotatedIndex n 1 ⟨m + 1, hm⟩) from rfl, hrot] at hi
        exact hi
      rw [← step]
      exact ih (by omega)

/-- **Unit rotations fix only constant colorings.**  For a unit `r : ZMod n`
    (equivalently `gcd(r, n) = 1`), a coloring is fixed by rotation by `r` iff it
    is constant.  The forward direction promotes "fixed by `r`" to "fixed by
    `1`" — since some multiple `m • r = 1` when `r` is a unit — and then applies
    `isConstant_of_isFixedByRotation_one`; the reverse direction is immediate
    because constant colorings are fixed by every rotation. -/
theorem isFixedByRotation_unit_iff_isConstant {n k : ℕ} [NeZero n]
    {r : ZMod n} (hr : IsUnit r) (c : Coloring n k) :
    IsFixedByRotation r c ↔ IsConstant c := by
  constructor
  · intro hc
    obtain ⟨u, rfl⟩ := hr
    have hc' : (↑u : ZMod n) +ᵥ c = c := hc
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ZMod n) = (↑u⁻¹ : ZMod n) :=
      ⟨(↑u⁻¹ : ZMod n).val, ZMod.natCast_rightInverse _⟩
    have key : (m • (↑u : ZMod n)) = 1 := by
      rw [nsmul_eq_mul, hm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h1 : (1 : ZMod n) +ᵥ c = c := by
      have hfix := isFixed_nsmul hc' m
      rwa [key] at hfix
    exact isConstant_of_isFixedByRotation_one h1
  · intro hconst
    show r +ᵥ c = c
    funext i
    show rotateColoring n k r c i = c i
    exact hconst _ i

/-- **Primitive-rotation fixed-point count.**  For any length `n ≥ 1`, palette
    size `k`, and unit rotation `r : ZMod n` (i.e. `gcd(r, n) = 1`), the number
    of colorings fixed by `r` is exactly `k` — the `k` constant colorings.  This
    is the `gcd = 1` case of `|Fix(r)| = k ^ gcd(r, n)` and generalizes the
    hard-coded `|Fix(1)| = |Fix(3)| = 2` used for binary `4`-necklaces. -/
theorem fixedBy_card_of_isUnit {n k : ℕ} [NeZero n] {r : ZMod n} (hr : IsUnit r) :
    Fintype.card { c : Coloring n k // IsFixedByRotation r c } = k := by
  rw [Fintype.card_congr
    (Equiv.subtypeEquivRight (isFixedByRotation_unit_iff_isConstant hr))]
  exact constant_coloring_count n k

/-- Cross-check: for binary `4`-necklaces the primitive rotation by `1` fixes
    exactly the `2` constant colorings, recovering the `|Fix(1)| = 2` entry of
    `fixed_point_sum_binary_4` from the general formula. -/
example : Fintype.card { c : Coloring 4 2 // IsFixedByRotation 1 c } = 2 :=
  fixedBy_card_of_isUnit isUnit_one

/-! ## Part VII: Prime-Length Necklaces and Fermat's Little Theorem

For a **prime** length `p`, every nonzero rotation `a : ZMod p` is a unit (since
`ZMod p` is a field), so by `fixedBy_card_of_isUnit` it fixes only the `k` constant
colorings, while the identity fixes all `kᵖ`.  Burnside's engine then evaluates the
necklace count in closed form, and the divisibility it forces is exactly Fermat's
Little Theorem. -/

/-- **Necklace count for prime length.**  For a prime `p` and palette size `k`, the
number of rotation orbits (necklaces) of `Coloring p k` satisfies
`|necklaces| · p = kᵖ + (p − 1)·k`.  The identity fixes all `kᵖ` colorings; every
nonzero rotation is a unit of the field `ZMod p` and hence fixes only the `k` constant
colorings (`fixedBy_card_of_isUnit`).  Summing over the `p` rotations and applying the
Burnside engine `sum_fixedBy_eq_card_necklaces_mul` gives the identity. -/
theorem necklaces_prime_length_mul {p : ℕ} (hp : p.Prime) (k : ℕ) :
    @Fintype.card (Quotient (@coloringSetoid p k _)) (coloringQuotientFintype p k) * p
      = k ^ p + (p - 1) * k := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- Fixed-point count at each rotation: `kᵖ` at the identity, `k` at every unit.
  have hf : ∀ a : ZMod p,
      Fintype.card { c : Coloring p k // IsFixedByRotation a c }
        = if a = 0 then k ^ p else k := by
    intro a
    by_cases ha : a = 0
    · subst ha
      rw [if_pos rfl]
      have huniv : ∀ c : Coloring p k, IsFixedByRotation (0 : ZMod p) c :=
        fun c => zero_vadd c
      rw [Fintype.card_congr (Equiv.subtypeUnivEquiv huniv)]
      show Fintype.card (Fin p → Fin k) = k ^ p
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    · rw [if_neg ha]
      exact fixedBy_card_of_isUnit (isUnit_iff_ne_zero.mpr ha)
  -- Evaluate the total fixed-point sum: `kᵖ + (p−1)·k`.
  have hsum : (∑ a : ZMod p, Fintype.card { c : Coloring p k // IsFixedByRotation a c })
      = k ^ p + (p - 1) * k := by
    simp only [hf]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (0 : ZMod p)), if_pos rfl]
    congr 1
    rw [Finset.sum_congr rfl (fun a ha => if_neg (Finset.ne_of_mem_erase ha)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
      Finset.card_univ, ZMod.card, smul_eq_mul]
  exact (sum_fixedBy_eq_card_necklaces_mul p k).symm.trans hsum

/-- **Fermat's Little Theorem, combinatorially.**  For a prime `p` and any `k`,
`p ∣ kᵖ − k`.  The prime-length necklace identity `|necklaces| · p = kᵖ + (p−1)·k`
rearranges to `kᵖ − k = (kᵖ + (p−1)·k) − ((p−1)·k + k)`, a difference of two multiples
of `p`: the `p` cyclic rotations partition the `kᵖ − k` non-constant colorings into
orbits of size exactly `p`.  No `native_decide`, no `Lean.ofReduceBool`. -/
theorem prime_dvd_pow_sub_self {p : ℕ} (hp : p.Prime) (k : ℕ) : p ∣ k ^ p - k := by
  have h := necklaces_prime_length_mul hp k
  have hdvd1 : p ∣ k ^ p + (p - 1) * k := by rw [← h]; exact dvd_mul_left p _
  have hpk : (p - 1) * k + k = p * k := by
    rw [Nat.sub_one_mul, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k hp.pos)]
  have hdvd2 : p ∣ (p - 1) * k + k := by rw [hpk]; exact dvd_mul_right p k
  have hrw : k ^ p - k = (k ^ p + (p - 1) * k) - ((p - 1) * k + k) := by omega
  rw [hrw]
  exact Nat.dvd_sub' hdvd1 hdvd2
