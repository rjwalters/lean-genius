/-
# Erdős Problem 332: Difference Sets and Bounded Gaps

Let `A ⊆ ℕ` and define `D(A)` as the set of integers that occur
infinitely often as `a₁ - a₂` with `a₁, a₂ ∈ A`.

What conditions on `A` are sufficient to ensure `D(A)` has bounded gaps?

A sufficient condition is that `A` has positive upper density (Prikry,
Tijdeman, Stewart).

*Reference:* [erdosproblems.com/332](https://www.erdosproblems.com/332)
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Set
open scoped Classical

/- ## Difference set D(A) -/

/-- The difference set `D(A)`: integers that appear infinitely often
as `a₁ - a₂` with `a₁, a₂ ∈ A`. -/
def diffSet (A : Set ℕ) : Set ℤ :=
    { d : ℤ | Set.Infinite
      { p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ (p.1 : ℤ) - (p.2 : ℤ) = d } }

/- ## Bounded gaps (syndetic sets) -/

/-- A set `S ⊆ ℤ` has bounded gaps (is syndetic) if there exists
`M > 0` such that every interval of length `M` contains an element
of `S`. -/
def HasBoundedGaps (S : Set ℤ) : Prop :=
    ∃ M : ℕ, 0 < M ∧
      ∀ z : ℤ, ∃ s ∈ S, z ≤ s ∧ s < z + (M : ℤ)

/-- The empty set has empty difference set. -/
theorem diffSet_empty : diffSet ∅ = ∅ :=
  diffSet_finite_eq_empty ∅ Set.finite_empty

/- ## Density conditions -/

/-- The counting function: `|A ∩ {1,…,N}|`. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
    (Finset.Icc 1 N |>.filter (· ∈ A)).card

/-- The counting function at zero is zero: `{1,...,0} = ∅`. -/
theorem countingFn_zero (A : Set ℕ) : countingFn A 0 = 0 := by
  simp [countingFn, Finset.Icc_eq_empty (by omega : ¬(1 ≤ 0))]

/-- The counting function is monotone: `N ≤ M → |A ∩ {1,...,N}| ≤ |A ∩ {1,...,M}|`. -/
theorem countingFn_mono (A : Set ℕ) {N M : ℕ} (h : N ≤ M) :
    countingFn A N ≤ countingFn A M := by
  unfold countingFn
  exact Finset.card_le_card (Finset.filter_subset_filter _
    (Finset.Icc_subset_Icc_right h))

/-- `A` has positive upper density: `limsup |A ∩ {1,…,N}| / N > 0`. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
    ∃ δ : ℚ, 0 < δ ∧
      ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
        δ * (N : ℚ) ≤ (countingFn A N : ℚ)

/-- `A` has positive lower density: `liminf |A ∩ {1,…,N}| / N > 0`. -/
def HasPositiveLowerDensity (A : Set ℕ) : Prop :=
    ∃ δ : ℚ, 0 < δ ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        δ * (N : ℚ) ≤ (countingFn A N : ℚ)

/- ## Known results -/

/-- Positive upper density implies `D(A)` has bounded gaps. This is
the known sufficient condition due to Prikry. -/
axiom positive_density_bounded_gaps (A : Set ℕ) :
    HasPositiveUpperDensity A → HasBoundedGaps (diffSet A)

/-- Positive upper density implies `D(A)` has positive density itself. -/
axiom positive_density_diffset_dense (A : Set ℕ) :
    HasPositiveUpperDensity A →
      HasPositiveUpperDensity { n : ℕ | (n : ℤ) ∈ diffSet A }

/-- The difference set is symmetric: `d ∈ D(A)` iff `-d ∈ D(A)`.
    Proof: the swap map `(a₁, a₂) ↦ (a₂, a₁)` sends pairs with
    difference `d` to pairs with difference `-d`, preserving membership. -/
theorem diffSet_symm (A : Set ℕ) (d : ℤ) :
    d ∈ diffSet A ↔ -d ∈ diffSet A := by
  suffices h : ∀ e : ℤ, e ∈ diffSet A → -e ∈ diffSet A from
    ⟨h d, fun hnd => neg_neg d ▸ h (-d) hnd⟩
  intro e he
  simp only [diffSet, Set.mem_setOf_eq] at he ⊢
  -- Set.Infinite = ¬ Set.Finite, so introduce S_{-e}.Finite and derive contradiction
  intro hfin
  -- S_e ⊆ Prod.swap '' S_{-e}, so S_e.Finite follows from S_{-e}.Finite
  exact he ((hfin.image Prod.swap).subset
    (fun ⟨a₁, a₂⟩ ⟨ha₁, ha₂, hd⟩ =>
      ⟨⟨a₂, a₁⟩, ⟨ha₂, ha₁, by push_cast at hd ⊢; linarith⟩, by simp [Prod.swap]⟩))

/-- Zero is always in `D(A)` when `A` is infinite.
    Proof: for each `a ∈ A`, the pair `(a, a)` has difference `0`.
    Since `A` is infinite, there are infinitely many such pairs. -/
theorem zero_mem_diffSet (A : Set ℕ) (hA : Set.Infinite A) :
    (0 : ℤ) ∈ diffSet A := by
  simp only [diffSet, Set.mem_setOf_eq]
  -- Set.Infinite = ¬ Set.Finite, so introduce S₀.Finite and derive contradiction
  intro hfin
  -- A ⊆ Prod.fst '' S₀, so A.Finite follows from S₀.Finite
  exact hA ((hfin.image Prod.fst).subset
    (fun a ha => ⟨⟨a, a⟩, ⟨ha, ha, by push_cast; ring⟩, rfl⟩))

/- ## Structural properties -/

/-- Monotonicity: if `A ⊆ B` then `D(A) ⊆ D(B)`. -/
theorem diffSet_mono (A B : Set ℕ) (h : A ⊆ B) : diffSet A ⊆ diffSet B := by
  intro d hd
  simp only [diffSet, Set.mem_setOf_eq] at hd ⊢
  intro hfin
  exact hd (hfin.subset (fun ⟨a₁, a₂⟩ ⟨ha₁, ha₂, hd⟩ => ⟨h ha₁, h ha₂, hd⟩))

/-- A finite set has empty difference set: no difference can occur
    infinitely often among finitely many pairs. -/
theorem diffSet_finite_eq_empty (A : Set ℕ) (hA : A.Finite) : diffSet A = ∅ := by
  ext d
  simp only [diffSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hinf
  exact hinf ((hA.prod hA).subset (fun ⟨a₁, a₂⟩ ⟨ha₁, ha₂, _⟩ => ⟨ha₁, ha₂⟩))

/-- If `A` is infinite, `D(A)` is nonempty (it contains zero). -/
theorem diffSet_nonempty_of_infinite (A : Set ℕ) (hA : Set.Infinite A) :
    (diffSet A).Nonempty :=
  ⟨0, zero_mem_diffSet A hA⟩

/-- Complete characterization: `0 ∈ D(A)` if and only if `A` is infinite. -/
theorem zero_mem_diffSet_iff (A : Set ℕ) :
    (0 : ℤ) ∈ diffSet A ↔ Set.Infinite A := by
  refine ⟨?_, zero_mem_diffSet A⟩
  intro h0
  by_contra hfin
  rw [Set.not_infinite] at hfin
  rw [diffSet_finite_eq_empty A hfin] at h0
  exact absurd h0 (Set.not_mem_empty 0)

/-- `D(A)` is nonempty if and only if `A` is infinite. -/
theorem diffSet_nonempty_iff (A : Set ℕ) :
    (diffSet A).Nonempty ↔ Set.Infinite A := by
  refine ⟨?_, diffSet_nonempty_of_infinite A⟩
  rintro ⟨d, hd⟩
  by_contra hfin
  rw [Set.not_infinite] at hfin
  rw [diffSet_finite_eq_empty A hfin] at hd
  exact absurd hd (Set.not_mem_empty d)

/-- Positive lower density implies positive upper density. -/
theorem lower_density_implies_upper (A : Set ℕ) :
    HasPositiveLowerDensity A → HasPositiveUpperDensity A := by
  rintro ⟨δ, hδ, N₀, hN₀⟩
  exact ⟨δ, hδ, fun M => ⟨max N₀ M, le_max_right _ _, hN₀ (max N₀ M) (le_max_left _ _)⟩⟩

/-- Positive lower density implies `D(A)` has bounded gaps:
    a corollary combining `lower_density_implies_upper` with the
    Prikry–Tijdeman–Stewart result. -/
theorem positive_lower_density_bounded_gaps (A : Set ℕ) :
    HasPositiveLowerDensity A → HasBoundedGaps (diffSet A) :=
  fun h => positive_density_bounded_gaps A (lower_density_implies_upper A h)

/- ## Additional structural properties -/

/-- D(A) ∪ D(B) ⊆ D(A ∪ B): union of difference sets embeds into
    difference set of the union. -/
theorem diffSet_union_subset (A B : Set ℕ) :
    diffSet A ∪ diffSet B ⊆ diffSet (A ∪ B) :=
  Set.union_subset (diffSet_mono _ _ Set.subset_union_left)
    (diffSet_mono _ _ Set.subset_union_right)

/-- A set with bounded gaps is nonempty. -/
theorem hasBoundedGaps_nonempty (S : Set ℤ) (h : HasBoundedGaps S) : S.Nonempty := by
  obtain ⟨M, _, hz⟩ := h
  obtain ⟨s, hs, _⟩ := hz 0
  exact ⟨s, hs⟩

/-- HasBoundedGaps is upward closed: if S ⊆ T and S has bounded gaps, so does T. -/
theorem hasBoundedGaps_mono {S T : Set ℤ} (h : S ⊆ T) (hs : HasBoundedGaps S) :
    HasBoundedGaps T := by
  obtain ⟨M, hM, hz⟩ := hs
  exact ⟨M, hM, fun z => let ⟨s, hs', hle, hlt⟩ := hz z; ⟨s, h hs', hle, hlt⟩⟩

/-- If D(A) has bounded gaps, then A is infinite. -/
theorem infinite_of_diffSet_bounded_gaps (A : Set ℕ)
    (h : HasBoundedGaps (diffSet A)) : Set.Infinite A := by
  rw [← diffSet_nonempty_iff]
  exact hasBoundedGaps_nonempty _ h

/- ## Main problem -/

/-- Erdős Problem 332: What conditions on `A ⊆ ℕ` are sufficient to
ensure `D(A)` has bounded gaps?

The known sufficient condition is positive upper density. The open
question asks for the weakest possible condition. -/
def ErdosProblem332 : Prop :=
    ∀ (P : Set ℕ → Prop),
      (∀ A : Set ℕ, P A → HasBoundedGaps (diffSet A)) →
        ∀ A : Set ℕ, HasPositiveUpperDensity A → P A

/- ## Related questions -/

/-- Does `∑_{d ∈ D(A)} 1/d = ∞` when `A` has positive upper density? -/
axiom diffSet_harmonic_diverges (A : Set ℕ) :
    HasPositiveUpperDensity A →
      ∀ B : ℚ, ∃ (S : Finset ℕ),
        (∀ n ∈ S, (n : ℤ) ∈ diffSet A) ∧
          B ≤ S.sum (fun n => (1 : ℚ) / (n : ℚ))
