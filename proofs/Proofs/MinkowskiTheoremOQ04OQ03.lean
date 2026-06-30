import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Proofs.MinkowskiTheoremOQ04
import Mathlib.Tactic

/-
# Sharpness of the Blichfeldt Volume Threshold (Minkowski OQ-04-OQ-03)

## What This Proves

The parent file `MinkowskiTheoremOQ04` proves **Blichfeldt's theorem**: a measurable
set `S ⊆ ℝⁿ` of Lebesgue measure **strictly greater than `k`** contains `k+1` distinct
points that are pairwise congruent modulo the integer lattice `ℤⁿ`
(`BlichfeldtTheorem.blichfeldt_general`; the `k = 1` case is
`BlichfeldtTheorem.blichfeldt_basic`).

This file shows the threshold is **sharp**: the strict inequality `k < volume S`
cannot be weakened to `k ≤ volume S`. Concretely we exhibit, for every `k`, a
measurable set of volume **exactly `k`** that contains **no** `k+1` pairwise
`ℤⁿ`-congruent distinct points.

* `k = 1` witness — the half-open unit cube `[0,1)ⁿ = stdFundDomain n` itself:
    - volume exactly `1` (`stdLattice_covolume`), yet
    - no two distinct points are `ℤⁿ`-congruent (`stdFundDomain_congruent_eq`).
  Hence Blichfeldt's `blichfeldt_basic` hypothesis `1 < volume S` is sharp
  (`blichfeldt_basic_threshold_not_le`).

* general `k` witness — the box `[0,k) × [0,1)ⁿ⁻¹` (`box n k`):
    - volume exactly `k` (`volume_box`), yet
    - it holds at most `k` mutually `ℤⁿ`-congruent points, so the Blichfeldt
      conclusion (`k+1` congruent points) fails (`blichfeldt_general_threshold_sharp`).

## Key Idea

`ℤⁿ`-congruent points have **equal fractional parts** (`ZSpan.fract_eq_fract`), and a
point of a half-open box is **determined** by its fractional part together with its
integer floor in the one "long" coordinate. The floor lives in `{0, …, k-1}`, so a box
of volume `k` can hold at most `k` mutually congruent points — pigeonhole then rules out
`k+1`.

## Axioms

Zero axioms beyond Mathlib's foundational set; `#print axioms` lists only
`propext`, `Classical.choice`, `Quot.sound`.
-/

open MeasureTheory Set MinkowskiProved

namespace BlichfeldtSharpness

variable (n : ℕ) [NeZero n]

-- ============================================================
-- PART 1: k = 1 — the fundamental domain is the sharp witness
-- ============================================================

/-- **Pointwise uniqueness of fundamental-domain representatives.**
Two points of the half-open unit cube `[0,1)ⁿ = stdFundDomain n` that are congruent
modulo the integer lattice `ℤⁿ` are equal.  This is the heart of sharpness for `k = 1`:
the unit cube — a set of volume exactly `1` — carries no `ℤⁿ`-congruent pair. -/
omit [NeZero n] in
theorem stdFundDomain_congruent_eq {x y : Fin n → ℝ}
    (hx : x ∈ stdFundDomain n) (hy : y ∈ stdFundDomain n)
    (hcong : x - y ∈ (stdLattice n : Set (Fin n → ℝ))) : x = y := by
  -- Points of the fundamental domain are fixed by `fract`.
  have hfx : ZSpan.fract (stdBasis n) x = x := (ZSpan.fract_eq_self (b := stdBasis n)).mpr hx
  have hfy : ZSpan.fract (stdBasis n) y = y := (ZSpan.fract_eq_self (b := stdBasis n)).mpr hy
  -- Congruence `x - y ∈ ℤⁿ` gives equal fractional parts.
  have hmem : -y + x ∈ Submodule.span ℤ (Set.range (stdBasis n)) := by
    have h : x - y ∈ stdLattice n := by simpa using hcong
    rw [neg_add_eq_sub]; exact h
  have hff : ZSpan.fract (stdBasis n) y = ZSpan.fract (stdBasis n) x :=
    (ZSpan.fract_eq_fract (stdBasis n) y x).mpr hmem
  rw [hfx, hfy] at hff
  exact hff.symm

/-- **Sharpness of Blichfeldt's threshold (k = 1).**
There is a measurable set of volume exactly `1` containing no two distinct
`ℤⁿ`-congruent points: the half-open unit cube `[0,1)ⁿ`. -/
theorem blichfeldt_threshold_sharp :
    ∃ S : Set (Fin n → ℝ), MeasurableSet S ∧ volume S = 1 ∧
      ¬ ∃ x y : Fin n → ℝ, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
        x - y ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  refine ⟨stdFundDomain n, stdFundDomain_measurableSet n, stdLattice_covolume n, ?_⟩
  rintro ⟨x, y, hx, hy, hne, hcong⟩
  exact hne (stdFundDomain_congruent_eq n hx hy hcong)

/-- **The hypothesis `1 < volume S` of `blichfeldt_basic` cannot be weakened to
`1 ≤ volume S`.**  The unit cube has volume `1` (so `1 ≤ volume`) yet fails the
Blichfeldt conclusion of a congruent pair. -/
theorem blichfeldt_basic_threshold_not_le :
    ∃ S : Set (Fin n → ℝ), MeasurableSet S ∧ (1 : ENNReal) ≤ volume S ∧
      ¬ ∃ x y : Fin n → ℝ, x ∈ S ∧ y ∈ S ∧ x ≠ y ∧
        x - y ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  obtain ⟨S, hmeas, hvol, hno⟩ := blichfeldt_threshold_sharp n
  exact ⟨S, hmeas, hvol.ge, hno⟩

-- ============================================================
-- PART 2: general k — the box [0,k) × [0,1)ⁿ⁻¹
-- ============================================================

/-- The box `[0,k) × [0,1)ⁿ⁻¹` in `ℝⁿ`: the first coordinate ranges over `[0,k)`,
all other coordinates over `[0,1)`.  Its volume is exactly `k`. -/
def box (k : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (0 : ℝ) (if i = 0 then (k : ℝ) else 1))

theorem box_measurableSet (k : ℕ) : MeasurableSet (box n k) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

/-- The box has volume exactly `k`. -/
theorem volume_box (k : ℕ) : volume (box n k) = (k : ENNReal) := by
  rw [box, volume_pi_pi]
  rw [Finset.prod_eq_single (0 : Fin n)]
  · rw [if_pos rfl, Real.volume_Ico, sub_zero, ENNReal.ofReal_natCast]
  · intro i _ hi
    rw [if_neg hi, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Coordinatewise formula for the `ZSpan` fractional part in the standard basis:
`(fract x) i = Int.fract (x i)`.  (The standard basis `Pi.basisFun` has the identity
`repr`.) -/
omit [NeZero n] in
theorem stdFract_coord (x : Fin n → ℝ) (i : Fin n) :
    ZSpan.fract (stdBasis n) x i = Int.fract (x i) := by
  have h := ZSpan.repr_fract_apply (stdBasis n) x i
  unfold stdBasis at h ⊢
  rwa [Pi.basisFun_repr, Pi.basisFun_repr] at h

/-- Congruent points share their fractional part in every coordinate. -/
theorem congruent_fract_coord {x y : Fin n → ℝ}
    (hcong : x - y ∈ (stdLattice n : Set (Fin n → ℝ))) (i : Fin n) :
    Int.fract (x i) = Int.fract (y i) := by
  have hmem : -y + x ∈ Submodule.span ℤ (Set.range (stdBasis n)) := by
    have h : x - y ∈ stdLattice n := by simpa using hcong
    rw [neg_add_eq_sub]; exact h
  have hff : ZSpan.fract (stdBasis n) y = ZSpan.fract (stdBasis n) x :=
    (ZSpan.fract_eq_fract (stdBasis n) y x).mpr hmem
  have hco := congrFun hff i
  rw [stdFract_coord, stdFract_coord] at hco
  exact hco.symm

/-- **Sharpness of Blichfeldt's threshold (general `k`).**
There is a measurable set of volume exactly `k` for which the Blichfeldt conclusion
fails: no injective family of `k+1` pairwise `ℤⁿ`-congruent points exists in it.
Hence the strict inequality `k < volume S` of `blichfeldt_general` is sharp. -/
theorem blichfeldt_general_threshold_sharp (k : ℕ) :
    ∃ S : Set (Fin n → ℝ), MeasurableSet S ∧ volume S = (k : ENNReal) ∧
      ¬ ∃ pts : Fin (k + 1) → Fin n → ℝ,
          Function.Injective pts ∧ (∀ i, pts i ∈ S) ∧
          ∀ i j, pts i - pts j ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  refine ⟨box n k, box_measurableSet n k, volume_box n k, ?_⟩
  rintro ⟨pts, hinj, hmem, hcong⟩
  -- Coordinate bounds from box membership.
  have hbound : ∀ m : Fin (k + 1), ∀ i : Fin n,
      0 ≤ pts m i ∧ pts m i < (if i = 0 then (k : ℝ) else 1) := by
    intro m i
    have := (Set.mem_univ_pi.mp (hmem m)) i
    rw [Set.mem_Ico] at this
    exact this
  -- The map sending each point to ⌊(coordinate 0)⌋ as an element of `Fin k`.
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- k = 0: box has volume 0, but pts 0 ∈ box forces coordinate 0 ∈ [0,0) = ∅.
      exfalso
      subst hk
      have h2 := (hbound 0 0).2
      rw [if_pos rfl, Nat.cast_zero] at h2
      linarith [(hbound 0 0).1]
    · exact hk
  -- floor of the first coordinate lies in {0, …, k-1}.
  have hfloor_lt : ∀ m : Fin (k + 1), (⌊pts m 0⌋).toNat < k := by
    intro m
    have h0 := hbound m 0
    rw [if_pos rfl] at h0
    have hfl_nonneg : 0 ≤ ⌊pts m 0⌋ := Int.floor_nonneg.mpr h0.1
    have hfl_lt : ⌊pts m 0⌋ < (k : ℤ) := by
      rw [Int.floor_lt]; exact_mod_cast h0.2
    omega
  set g : Fin (k + 1) → Fin k := fun m => ⟨(⌊pts m 0⌋).toNat, hfloor_lt m⟩ with hg
  -- g is injective: a point of the box is determined by ⌊·0⌋ and its (shared) fract.
  have hg_inj : Function.Injective g := by
    intro a b hab
    apply hinj
    -- equal floors in coordinate 0
    have hfloor_eq : ⌊pts a 0⌋ = ⌊pts b 0⌋ := by
      have : (⌊pts a 0⌋).toNat = (⌊pts b 0⌋).toNat := by
        have := congrArg Fin.val hab; simpa [hg] using this
      have ha := (hbound a 0); rw [if_pos rfl] at ha
      have hb := (hbound b 0); rw [if_pos rfl] at hb
      have hna : 0 ≤ ⌊pts a 0⌋ := Int.floor_nonneg.mpr ha.1
      have hnb : 0 ≤ ⌊pts b 0⌋ := Int.floor_nonneg.mpr hb.1
      omega
    -- prove the two points are equal coordinatewise
    funext i
    by_cases hi : i = 0
    · subst hi
      -- coordinate 0: same floor and same fractional part
      have hfr := congruent_fract_coord n (hcong a b) 0
      have ea : (⌊pts a 0⌋ : ℝ) + Int.fract (pts a 0) = pts a 0 := Int.floor_add_fract _
      have eb : (⌊pts b 0⌋ : ℝ) + Int.fract (pts b 0) = pts b 0 := Int.floor_add_fract _
      rw [← ea, ← eb, hfr, hfloor_eq]
    · -- coordinate i ≠ 0: both lie in [0,1), so equal to their (shared) fractional part
      have hfr := congruent_fract_coord n (hcong a b) i
      have ha := hbound a i; rw [if_neg hi] at ha
      have hb := hbound b i; rw [if_neg hi] at hb
      have ea : Int.fract (pts a i) = pts a i := Int.fract_eq_self.mpr ⟨ha.1, ha.2⟩
      have eb : Int.fract (pts b i) = pts b i := Int.fract_eq_self.mpr ⟨hb.1, hb.2⟩
      rw [← ea, ← eb, hfr]
  -- pigeonhole: an injection Fin (k+1) ↪ Fin k is impossible.
  have hcard := Fintype.card_le_of_injective g hg_inj
  simp only [Fintype.card_fin] at hcard
  omega

end BlichfeldtSharpness
