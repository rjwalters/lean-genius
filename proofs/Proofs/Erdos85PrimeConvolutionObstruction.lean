import Proofs.Erdos85CyclicConvolutionParity

/-!
# The three-hole convolution obstruction

This file isolates the finite-group counting calculation needed in the
square-cyclotomic branch.  The parity pattern is the complement of a
three-element set.  Its self-convolution is the group order minus six, plus
the self-convolution of the three-point indicator.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- The integral indicator of a finite subset. -/
def integerIndicator (S : Finset Z) (x : Z) : ℤ :=
  if x ∈ S then 1 else 0

theorem sum_integerIndicator (S : Finset Z) :
    ∑ x, integerIndicator S x = S.card := by
  simp [integerIndicator]

/-- Passing from a three-hole indicator to its complement contributes the
universal `|Z|-6` term.  The statement is kept for arbitrary `S`; the
three-point specialization follows by setting `S.card = 3`. -/
theorem cyclicConvolution_indicator_complement
    (S : Finset Z) (t : Z) :
    cyclicConvolution (fun x ↦ 1 - integerIndicator S x)
        (fun x ↦ 1 - integerIndicator S x) t =
      (Fintype.card Z : ℤ) - 2 * S.card +
        cyclicConvolution (integerIndicator S) (integerIndicator S) t := by
  have hsum : (∑ x, integerIndicator S x) = (S.card : ℤ) :=
    sum_integerIndicator S
  have hshift : (∑ x, integerIndicator S (t - x)) = (S.card : ℤ) := by
    have hcomm := cyclicConvolution_comm (fun _ : Z ↦ (1 : ℤ))
      (integerIndicator S) t
    calc
      (∑ x, integerIndicator S (t - x)) =
          cyclicConvolution (fun _ : Z ↦ (1 : ℤ))
            (integerIndicator S) t := by simp [cyclicConvolution]
      _ = cyclicConvolution (integerIndicator S)
            (fun _ : Z ↦ (1 : ℤ)) t := hcomm
      _ = ∑ x, integerIndicator S x := by simp [cyclicConvolution]
      _ = S.card := hsum
  unfold cyclicConvolution
  calc
    (∑ x, (1 - integerIndicator S x) *
        (1 - integerIndicator S (t - x))) =
      ∑ x, (1 - integerIndicator S x - integerIndicator S (t - x) +
        integerIndicator S x * integerIndicator S (t - x)) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = (Fintype.card Z : ℤ) - 2 * S.card +
        ∑ x, integerIndicator S x * integerIndicator S (t - x) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_const, Finset.card_univ, mul_one]
          rw [hsum, hshift]
          ring

theorem cyclicConvolution_integerIndicator_eq_sum
    (S : Finset Z) (t : Z) :
    cyclicConvolution (integerIndicator S) (integerIndicator S) t =
      ∑ x ∈ S, integerIndicator S (t - x) := by
  unfold cyclicConvolution
  rw [← Finset.sum_subset (Finset.subset_univ S)]
  · apply Finset.sum_congr rfl
    intro x hx
    simp [integerIndicator, hx]
  · intro x _ hx
    simp [integerIndicator, hx]

/-- The three-point indicator has exactly the two evident representations of
`a`, provided the third possible first coordinate does not contribute. -/
theorem cyclicConvolution_threePoint_at_anchor
    (a : Z) (ha0 : a ≠ 0)
    (hfar : a - (-a) ∉ ({0, a, -a} : Finset Z)) :
    cyclicConvolution
        (integerIndicator ({0, a, -a} : Finset Z))
        (integerIndicator ({0, a, -a} : Finset Z)) a = 2 := by
  rw [cyclicConvolution_integerIndicator_eq_sum]
  let S : Finset Z := {0, a, -a}
  have hfilter : S.filter (fun x ↦ a - x ∈ S) = {0, a} := by
    ext x
    simp only [S, Finset.mem_filter, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨(rfl | rfl | rfl), hx⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact False.elim (hfar (by simpa using hx))
    · rintro (rfl | rfl)
      · simp
      · simp
  change ∑ x ∈ S, integerIndicator S (a - x) = 2
  rw [show (∑ x ∈ S, integerIndicator S (a - x)) =
      ((S.filter (fun x ↦ a - x ∈ S)).card : ℤ) by
        simp [integerIndicator]]
  rw [hfilter]
  rw [Finset.card_insert_of_notMem (by simpa using Ne.symm ha0)]
  simp

theorem cyclicConvolution_integerIndicator_eq_zero_of_no_sum
    (S : Finset Z) (g : Z)
    (hno : ∀ x ∈ S, g - x ∉ S) :
    cyclicConvolution (integerIndicator S) (integerIndicator S) g = 0 := by
  rw [cyclicConvolution_integerIndicator_eq_sum]
  apply Finset.sum_eq_zero
  intro x hx
  simp [integerIndicator, hno x hx]

/-- Abstract form of the complete three-hole contradiction.  Its hypotheses
are precisely the two elementary finite-set facts to be supplied for
`ZMod p`: the anchor has two representations and a generic residue has none. -/
theorem false_of_threePoint_parity_pattern
    (c e : Z → ℤ) (a g : Z)
    (S : Finset Z) (hcard : S.card = 3)
    (hanchor : cyclicConvolution (integerIndicator S)
      (integerIndicator S) a = 2)
    (hgeneric : cyclicConvolution (integerIndicator S)
      (integerIndicator S) g = 0)
    (hparity : ∀ x, c x = (1 - integerIndicator S x) + 2 * e x)
    (hconstant : cyclicConvolution c c a = cyclicConvolution c c g) : False := by
  let b : Z → ℤ := fun x ↦ 1 - integerIndicator S x
  have ha : cyclicConvolution b b a = (Fintype.card Z : ℤ) - 4 := by
    rw [cyclicConvolution_indicator_complement, hcard, hanchor]
    ring
  have hg : cyclicConvolution b b g = (Fintype.card Z : ℤ) - 6 := by
    rw [cyclicConvolution_indicator_complement, hcard, hgeneric]
    ring
  exact false_of_cyclicConvolution_constant_and_parity_gap_two
    c b e a g hparity hconstant (Fintype.card Z) ha hg

section ZMod

variable {p : ℕ} [NeZero p]

/-- In a cyclic group of order at least seven, some residue lies outside the
five possible sums of `{0,a,-a}` when `2a=1`. -/
theorem exists_residue_outside_threePoint_sumset
    (hp : 7 ≤ p) (a : ZMod p) (hdouble : a + a = 1) :
    ∃ g : ZMod p, ∀ x ∈ ({0, a, -a} : Finset (ZMod p)),
      g - x ∉ ({0, a, -a} : Finset (ZMod p)) := by
  let F : Finset (ZMod p) := {0, a, -a, 1, -1}
  have hFcard : F.card ≤ 5 := by
    dsimp only [F]
    have h1 : ({-1} : Finset (ZMod p)).card ≤ 1 := by simp
    have h2 : ({1, -1} : Finset (ZMod p)).card ≤ 2 := by
      calc
        ({1, -1} : Finset (ZMod p)).card ≤ ({-1} : Finset (ZMod p)).card + 1 :=
          Finset.card_insert_le _ _
        _ ≤ 2 := by omega
    have h3 : ({-a, 1, -1} : Finset (ZMod p)).card ≤ 3 := by
      calc
        ({-a, 1, -1} : Finset (ZMod p)).card ≤
            ({1, -1} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
        _ ≤ 3 := by omega
    have h4 : ({a, -a, 1, -1} : Finset (ZMod p)).card ≤ 4 := by
      calc
        ({a, -a, 1, -1} : Finset (ZMod p)).card ≤
            ({-a, 1, -1} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
        _ ≤ 4 := by omega
    calc
      ({0, a, -a, 1, -1} : Finset (ZMod p)).card ≤
          ({a, -a, 1, -1} : Finset (ZMod p)).card + 1 := Finset.card_insert_le _ _
      _ ≤ 5 := by omega
  have hex : ∃ g : ZMod p, g ∉ F := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset (ZMod p)) ⊆ F := by
      intro x _
      exact h x
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, ZMod.card] at hc
    omega
  obtain ⟨g, hg⟩ := hex
  refine ⟨g, ?_⟩
  intro x hx hgx
  have hx' : x = 0 ∨ x = a ∨ x = -a := by simpa using hx
  have hy' : g - x = 0 ∨ g - x = a ∨ g - x = -a := by
    simpa using hgx
  apply hg
  have hgadd : g = x + (g - x) := by abel
  rw [hgadd]
  rcases hx' with rfl | rfl | rfl <;>
    rcases hy' with h | h | h <;>
    simp only [h]
  all_goals simp [F, hdouble]
  all_goals rw [show -a + -a = -(a + a) by abel, hdouble]
  all_goals simp [F]

theorem threePoint_card_and_anchor_of_large_modulus
    (hp : 7 ≤ p) (a : ZMod p) (hdouble : a + a = 1) :
    ({0, a, -a} : Finset (ZMod p)).card = 3 ∧
      cyclicConvolution
        (integerIndicator ({0, a, -a} : Finset (ZMod p)))
        (integerIndicator ({0, a, -a} : Finset (ZMod p))) a = 2 := by
  letI : Fact (1 < p) := ⟨by omega⟩
  have hone : (1 : ZMod p) ≠ 0 := one_ne_zero
  have ha0 : a ≠ 0 := by
    intro ha
    rw [ha, zero_add] at hdouble
    exact hone hdouble.symm
  have haneg : a ≠ -a := by
    intro ha
    have hz : a + a = 0 := by
      calc
        a + a = a + (-a) := congrArg (a + ·) ha
        _ = 0 := add_neg_cancel a
    exact hone (hdouble.symm.trans hz)
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h
    have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hd
    omega
  have h1a : (1 : ZMod p) ≠ a := by
    intro h
    have : (1 : ZMod p) + 1 = 1 := by simpa [h] using hdouble
    apply hone
    apply add_left_cancel (a := (1 : ZMod p))
    simpa using this
  have h1nega : (1 : ZMod p) ≠ -a := by
    intro h
    have ha : a = -1 := by
      have := congrArg Neg.neg h
      simpa using this.symm
    rw [ha] at hdouble
    apply hthree
    have : (3 : ZMod p) = 1 + 1 + 1 := by norm_num
    rw [this]
    linear_combination -hdouble
  have hfar : a - (-a) ∉ ({0, a, -a} : Finset (ZMod p)) := by
    rw [show a - (-a) = a + a by abel, hdouble]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hone, h1a, h1nega⟩
  constructor
  · rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem]
      · simp
      · simpa using haneg
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm ha0, Ne.symm (neg_ne_zero.mpr ha0)⟩
  · exact cyclicConvolution_threePoint_at_anchor a ha0 hfar

/-- Fully assembled `p ≥ 7` convolution obstruction.  This is the terminal
lemma consumed by the square Fourier branch: once the projected multiplicity
has the three-hole parity pattern and its self-convolution is constant from
the anchor to every generic residue, contradiction follows uniformly in
`p`. -/
theorem false_of_large_threePoint_convolution_pattern
    (hp : 7 ≤ p) (a : ZMod p) (hdouble : a + a = 1)
    (c e : ZMod p → ℤ)
    (hparity : ∀ x, c x =
      (1 - integerIndicator ({0, a, -a} : Finset (ZMod p)) x) + 2 * e x)
    (hconstant : ∀ g,
      g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution c c a = cyclicConvolution c c g) : False := by
  obtain ⟨g, hgNoSum⟩ :=
    exists_residue_outside_threePoint_sumset hp a hdouble
  have hgOutside :
      g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) := by
    intro hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with h | h | h | h | h
    · exact hgNoSum 0 (by simp) (by simpa [h])
    · exact hgNoSum a (by simp) (by simpa [h])
    · exact hgNoSum (-a) (by simp) (by simpa [h])
    · have : g = a + a := by simpa [hdouble] using h
      exact hgNoSum a (by simp) (by rw [this]; simp)
    · have : g = (-a) + (-a) := by
        rw [show (-a) + (-a) = -(a + a) by abel, hdouble]
        simpa using h
      exact hgNoSum (-a) (by simp) (by rw [this]; simp)
  obtain ⟨hcard, hanchor⟩ :=
    threePoint_card_and_anchor_of_large_modulus hp a hdouble
  have hgeneric := cyclicConvolution_integerIndicator_eq_zero_of_no_sum
    ({0, a, -a} : Finset (ZMod p)) g hgNoSum
  exact false_of_threePoint_parity_pattern c e a g
    ({0, a, -a} : Finset (ZMod p)) hcard hanchor hgeneric
    hparity (hconstant g hgOutside)

end ZMod

end

end Erdos85
