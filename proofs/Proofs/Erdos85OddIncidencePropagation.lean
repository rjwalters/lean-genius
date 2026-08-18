import Mathlib.Algebra.BigOperators.Ring.Nat

namespace Erdos85

open scoped BigOperators

/-- An even finite incidence sum cannot have exactly one odd summand. -/
theorem exists_ne_odd_of_even_sum_of_odd
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) (i : ι)
    (hi : i ∈ s)
    (hsum : Even (∑ j ∈ s, f j))
    (hodd : Odd (f i)) :
    ∃ j ∈ s, j ≠ i ∧ Odd (f j) := by
  by_contra h
  push Not at h
  have hfilter : {j ∈ s | Odd (f j)} = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hji
      exact (h j hj.1 hji) hj.2
    · intro hji
      subst j
      exact ⟨hi, hodd⟩
  have hcard : Even ({j ∈ s | Odd (f j)}.card) :=
    (Finset.even_sum_iff_even_card_odd f).mp hsum
  rw [hfilter] at hcard
  simp at hcard

/-- Type-indexed form of `exists_ne_odd_of_even_sum_of_odd`. -/
theorem exists_ne_odd_of_even_univ_sum_of_odd
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (i : ι)
    (hsum : Even (∑ j, f j))
    (hodd : Odd (f i)) :
    ∃ j, j ≠ i ∧ Odd (f j) := by
  obtain ⟨j, _, hji, hjodd⟩ :=
    exists_ne_odd_of_even_sum_of_odd Finset.univ f i (by simp) hsum hodd
  exact ⟨j, hji, hjodd⟩

/-- For symmetric data stored under canonical unordered keys, parity at one
endpoint propagates past a given odd edge.  An even diagonal rules out the
degenerate choice of the endpoint itself. -/
theorem exists_odd_canonical_neighbor_of_even_incidence
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (m : ι × ι → ℕ) (i k : ι)
    (hsum : Even (∑ j, m (min i j, max i j)))
    (hik : Odd (m (min i k, max i k)))
    (hdiag : Even (m (i, i))) :
    ∃ j, j ≠ i ∧ j ≠ k ∧ Odd (m (min i j, max i j)) := by
  obtain ⟨j, hjk, hjodd⟩ :=
    exists_ne_odd_of_even_univ_sum_of_odd
      (fun j => m (min i j, max i j)) k hsum hik
  refine ⟨j, ?_, hjk, hjodd⟩
  intro hji
  subst j
  simp only [min_self, max_self] at hjodd
  exact (Nat.not_odd_iff_even.mpr hdiag) hjodd

/-- An Eulerian odd-support graph whose color classes have size at most two
either has no edges, has a turn through three colors, or contains the full
four-cycle between two two-point color classes. -/
theorem odd_support_three_color_turn_or_cross
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (color : ι → κ) (m : ι × ι → ℕ)
    (hfiber : ∀ x y z, color x = color y → color x = color z →
      x = y ∨ x = z ∨ y = z)
    (hincidence : ∀ i, Even (∑ j, m (min i j, max i j)))
    (hdiag : ∀ i, Even (m (i, i)))
    (hsame : ∀ a b, color a = color b →
      Even (m (min a b, max a b))) :
    (∀ a b, a ≠ b → Even (m (min a b, max a b))) ∨
      (∃ a b c,
        color a ≠ color b ∧ color b ≠ color c ∧ color a ≠ color c ∧
        Odd (m (min a b, max a b)) ∧
        Odd (m (min b c, max b c))) ∨
      (∃ a b c d,
        a ≠ c ∧ b ≠ d ∧ color a = color c ∧ color b = color d ∧
        color a ≠ color b ∧
        Odd (m (min a b, max a b)) ∧
        Odd (m (min a d, max a d)) ∧
        Odd (m (min c b, max c b)) ∧
        Odd (m (min c d, max c d))) := by
  classical
  by_cases hall : ∀ a b, a ≠ b → Even (m (min a b, max a b))
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨a, b, hab, habNotEven⟩ := hall
  have habOdd : Odd (m (min a b, max a b)) :=
    Nat.not_even_iff_odd.mp habNotEven
  have hcolorAB : color a ≠ color b := by
    intro h
    exact (Nat.not_odd_iff_even.mpr (hsame a b h)) habOdd
  obtain ⟨c, hcb, hca, hbcOdd⟩ :=
    exists_odd_canonical_neighbor_of_even_incidence
      m b a (hincidence b) (by simpa [min_comm, max_comm] using habOdd)
        (hdiag b)
  have hcolorBC : color b ≠ color c := by
    intro h
    exact (Nat.not_odd_iff_even.mpr (hsame b c h)) hbcOdd
  by_cases hcolorAC : color a ≠ color c
  · exact Or.inl ⟨a, b, c, hcolorAB, hcolorBC, hcolorAC,
      habOdd, hbcOdd⟩
  have hcolorACeq : color a = color c := not_ne_iff.mp hcolorAC
  obtain ⟨d, hdc, hdb, hcdOdd⟩ :=
    exists_odd_canonical_neighbor_of_even_incidence
      m c b (hincidence c) (by simpa [min_comm, max_comm] using hbcOdd)
        (hdiag c)
  have hcolorCD : color c ≠ color d := by
    intro h
    exact (Nat.not_odd_iff_even.mpr (hsame c d h)) hcdOdd
  by_cases hcolorBD : color b ≠ color d
  · exact Or.inl ⟨b, c, d, hcolorBC, hcolorCD, hcolorBD,
      hbcOdd, hcdOdd⟩
  have hcolorBDeq : color b = color d := not_ne_iff.mp hcolorBD
  obtain ⟨e, hea, heb, haeOdd⟩ :=
    exists_odd_canonical_neighbor_of_even_incidence
      m a b (hincidence a) habOdd (hdiag a)
  have hcolorAE : color a ≠ color e := by
    intro h
    exact (Nat.not_odd_iff_even.mpr (hsame a e h)) haeOdd
  by_cases hcolorEB : color e ≠ color b
  · exact Or.inl ⟨e, a, b, hcolorAE.symm, hcolorAB, hcolorEB,
      (by simpa [min_comm, max_comm] using haeOdd), habOdd⟩
  have hcolorEBeq : color e = color b := not_ne_iff.mp hcolorEB
  have hed : e = d := by
    rcases hfiber b d e hcolorBDeq hcolorEBeq.symm with hbd | hbe | hde
    · exact (hdb hbd.symm).elim
    · exact (heb hbe.symm).elim
    · exact hde.symm
  subst e
  exact Or.inr ⟨a, b, c, d, hca.symm, hdb.symm, hcolorACeq,
    hcolorBDeq, hcolorAB, habOdd, haeOdd,
    (by simpa [min_comm, max_comm] using hbcOdd), hcdOdd⟩

end Erdos85
