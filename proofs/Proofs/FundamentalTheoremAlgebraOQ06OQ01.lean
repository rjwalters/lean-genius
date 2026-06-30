import Mathlib

/-
# A Real Polynomial Function Is Surjective iff Its Degree Is Odd

## What This Proves
For every `P ∈ ℝ[X]`, the associated polynomial function `x ↦ P.eval x : ℝ → ℝ` is
**surjective if and only if `P.natDegree` is odd**:

  `Function.Surjective (fun x => P.eval x) ↔ Odd P.natDegree`.

This is a sharp characterisation that sits directly on top of the parent entry's
intermediate-value step ("every odd-degree real polynomial has a real root"). The parent
proved that odd degree is *sufficient* for the existence of one root; here we upgrade that
to surjectivity onto all of `ℝ` and, crucially, establish the **converse**: an even-degree
(in particular, a constant) polynomial is never surjective, because it is bounded on one
side. So odd degree is exactly the dividing line for surjectivity of real polynomial maps.

## Approach
- **(odd ⟹ surjective).** Given a target value `y`, the shifted polynomial `P - C y` has the
  *same* degree as `P` (`natDegree_sub_C`), hence is still of odd degree, hence has a real
  root `x` by the parent's odd-degree root theorem (re-derived here so the file is
  self-contained). That root satisfies `P.eval x = y`.
- **(surjective ⟹ odd), i.e. even ⟹ not surjective.** Split on `natDegree`:
  - `natDegree = 0`: `P` is a constant `C c`, whose image is the single point `{c}`; the
    value `c + 1` is never attained.
  - `natDegree` even and positive: the leading term dominates with the *same* sign at both
    `±∞` (an even power does not flip sign), so `P.eval` tends to `+∞` along the whole
    `cocompact ℝ` filter when `leadingCoeff ≥ 0` (and to `−∞` when `leadingCoeff ≤ 0`). The
    extreme value theorem (`Continuous.exists_forall_le`) then gives a global minimum `m`
    (resp. maximum), and `m - 1` (resp. `m + 1`) lies outside the range.

## Mathlib Ingredients
- `Polynomial.natDegree_sub_C`, `Polynomial.eq_C_of_natDegree_eq_zero`
- `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`, `intermediate_value_uIcc`
- `Polynomial.leadingCoeff_comp`, `Polynomial.natDegree_comp`, `Polynomial.eval_comp`
- `cocompact_eq_atBot_atTop`, `Filter.tendsto_neg_atBot_atTop`, `Continuous.exists_forall_le`

The boundedness/extreme-value half is the genuinely new content: it turns the parent's
one-sided existence statement into the two-sided "iff" that pins surjectivity to parity.
-/

open Polynomial Filter Topology

namespace FTAOddDegreeSurjective

/-! ### The odd-degree root theorem (self-contained, after the parent entry) -/

/-- An odd-degree real polynomial takes both a strictly negative and a strictly positive
value: the leading term dominates at `±∞` and an odd power flips sign. -/
theorem exists_neg_and_pos_eval (P : ℝ[X]) (hodd : Odd P.natDegree) :
    (∃ a : ℝ, P.eval a < 0) ∧ (∃ b : ℝ, 0 < P.eval b) := by
  obtain ⟨m, hm⟩ := hodd
  have hpos_deg : 0 < P.natDegree := by omega
  have hdeg : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hpos_deg
  set Q : ℝ[X] := P.comp (-X) with hQ
  have hnd_negX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hlc_negX : (-X : ℝ[X]).leadingCoeff = -1 := by rw [leadingCoeff_neg, leadingCoeff_X]
  have hne : (-X : ℝ[X]).natDegree ≠ 0 := by rw [hnd_negX]; norm_num
  have hQdeg_nd : Q.natDegree = P.natDegree := by rw [hQ, natDegree_comp, hnd_negX, mul_one]
  have hQdeg : 0 < Q.degree := by rw [← natDegree_pos_iff_degree_pos, hQdeg_nd]; exact hpos_deg
  have hQlc : Q.leadingCoeff = -P.leadingCoeff := by
    rw [hQ, leadingCoeff_comp hne, hlc_negX, Odd.neg_one_pow ⟨m, hm⟩]; ring
  have hevalQ : ∀ x : ℝ, Q.eval x = P.eval (-x) := by intro x; rw [hQ, eval_comp]; simp
  rcases le_total 0 P.leadingCoeff with hlc | hlc
  · have hP : Tendsto (fun x => P.eval x) atTop atTop :=
      P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc
    have hb : ∃ b : ℝ, 0 < P.eval b := (hP.eventually (eventually_gt_atTop 0)).exists
    have hQlc_nonpos : Q.leadingCoeff ≤ 0 := by rw [hQlc]; linarith
    have hQt : Tendsto (fun x => Q.eval x) atTop atBot :=
      Q.tendsto_atBot_of_leadingCoeff_nonpos hQdeg hQlc_nonpos
    obtain ⟨x, hx⟩ := (hQt.eventually (eventually_lt_atBot 0)).exists
    rw [hevalQ] at hx
    exact ⟨⟨-x, hx⟩, hb⟩
  · have hP : Tendsto (fun x => P.eval x) atTop atBot :=
      P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc
    have ha : ∃ a : ℝ, P.eval a < 0 := (hP.eventually (eventually_lt_atBot 0)).exists
    have hQlc_nonneg : 0 ≤ Q.leadingCoeff := by rw [hQlc]; linarith
    have hQt : Tendsto (fun x => Q.eval x) atTop atTop :=
      Q.tendsto_atTop_of_leadingCoeff_nonneg hQdeg hQlc_nonneg
    obtain ⟨x, hx⟩ := (hQt.eventually (eventually_gt_atTop 0)).exists
    rw [hevalQ] at hx
    exact ⟨ha, ⟨-x, hx⟩⟩

/-- **Odd-degree real root theorem** (parent result, re-derived). Every real polynomial of
odd degree has a real root. -/
theorem odd_natDegree_has_real_root (P : ℝ[X]) (hodd : Odd P.natDegree) :
    ∃ x : ℝ, P.IsRoot x := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_neg_and_pos_eval P hodd
  have hcont : ContinuousOn (fun x => P.eval x) (Set.uIcc a b) := P.continuousOn
  have h0mem : (0 : ℝ) ∈ Set.uIcc (P.eval a) (P.eval b) := by
    rw [Set.mem_uIcc]; exact Or.inl ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨c, _, hc⟩ := intermediate_value_uIcc hcont h0mem
  exact ⟨c, hc⟩

/-! ### Odd degree ⟹ surjective -/

/-- **Odd degree is sufficient for surjectivity.** Every odd-degree real polynomial function
is surjective: for any target `y`, the polynomial `P - C y` has the same (odd) degree as
`P`, hence has a root, which is a preimage of `y`. -/
theorem eval_surjective_of_odd_natDegree (P : ℝ[X]) (hodd : Odd P.natDegree) :
    Function.Surjective (fun x => P.eval x) := by
  intro y
  have hodd' : Odd (P - C y).natDegree := by rw [natDegree_sub_C]; exact hodd
  obtain ⟨x, hx⟩ := odd_natDegree_has_real_root (P - C y) hodd'
  refine ⟨x, ?_⟩
  have hx' : P.eval x - y = 0 := by
    have := hx; rwa [IsRoot, eval_sub, eval_C] at this
  show P.eval x = y
  linarith

/-! ### Even degree ⟹ bounded ⟹ not surjective -/

/-- An even, positive-degree real polynomial with nonnegative leading coefficient is
**bounded below**: it tends to `+∞` along the whole `cocompact ℝ` filter (an even power keeps
the sign of the leading term at both `±∞`), so the extreme value theorem yields a global
minimum. -/
theorem exists_forall_le_of_even (P : ℝ[X]) (hd : 0 < P.natDegree) (heven : Even P.natDegree)
    (hlc : 0 ≤ P.leadingCoeff) : ∃ m : ℝ, ∀ x : ℝ, m ≤ P.eval x := by
  have hdeg : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hd
  have hatTop : Tendsto (fun x => P.eval x) atTop atTop :=
    P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc
  -- reflected polynomial Q(x) = P(-x)
  set Q : ℝ[X] := P.comp (-X) with hQ
  have hnd_negX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hlc_negX : (-X : ℝ[X]).leadingCoeff = -1 := by rw [leadingCoeff_neg, leadingCoeff_X]
  have hne : (-X : ℝ[X]).natDegree ≠ 0 := by rw [hnd_negX]; norm_num
  have hQdeg_nd : Q.natDegree = P.natDegree := by rw [hQ, natDegree_comp, hnd_negX, mul_one]
  have hQdeg : 0 < Q.degree := by rw [← natDegree_pos_iff_degree_pos, hQdeg_nd]; exact hd
  have hQlc : Q.leadingCoeff = P.leadingCoeff := by
    rw [hQ, leadingCoeff_comp hne, hlc_negX, heven.neg_one_pow]; ring
  have hQlc_nonneg : 0 ≤ Q.leadingCoeff := by rw [hQlc]; exact hlc
  have hQatTop : Tendsto (fun x => Q.eval x) atTop atTop :=
    Q.tendsto_atTop_of_leadingCoeff_nonneg hQdeg hQlc_nonneg
  have hevalQ : ∀ x : ℝ, Q.eval x = P.eval (-x) := by intro x; rw [hQ, eval_comp]; simp
  -- transport Q's behaviour at +∞ to P's behaviour at −∞
  have hatBot : Tendsto (fun x => P.eval x) atBot atTop := by
    have h := hQatTop.comp Filter.tendsto_neg_atBot_atTop
    refine h.congr ?_
    intro x
    show Q.eval (-x) = P.eval x
    rw [hevalQ, neg_neg]
  have hcocompact : Tendsto (fun x => P.eval x) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop, tendsto_sup]; exact ⟨hatBot, hatTop⟩
  obtain ⟨x₀, hx₀⟩ := P.continuous.exists_forall_le hcocompact
  exact ⟨P.eval x₀, hx₀⟩

/-- Dual of `exists_forall_le_of_even`: an even, positive-degree polynomial with nonpositive
leading coefficient is **bounded above** (apply the previous lemma to `-P`). -/
theorem exists_forall_ge_of_even (P : ℝ[X]) (hd : 0 < P.natDegree) (heven : Even P.natDegree)
    (hlc : P.leadingCoeff ≤ 0) : ∃ M : ℝ, ∀ x : ℝ, P.eval x ≤ M := by
  have hd' : 0 < (-P).natDegree := by rwa [natDegree_neg]
  have heven' : Even (-P).natDegree := by rwa [natDegree_neg]
  have hlc' : 0 ≤ (-P).leadingCoeff := by rw [leadingCoeff_neg]; linarith
  obtain ⟨m, hm⟩ := exists_forall_le_of_even (-P) hd' heven' hlc'
  refine ⟨-m, fun x => ?_⟩
  have hx := hm x
  rw [eval_neg] at hx
  linarith

/-- **Even degree is incompatible with surjectivity.** A positive even-degree polynomial is
bounded below or above, so some real value is never attained. -/
theorem not_surjective_of_even_natDegree (P : ℝ[X]) (hd : 0 < P.natDegree)
    (heven : Even P.natDegree) : ¬ Function.Surjective (fun x => P.eval x) := by
  rcases le_total 0 P.leadingCoeff with hlc | hlc
  · obtain ⟨m, hm⟩ := exists_forall_le_of_even P hd heven hlc
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj (m - 1)
    have := hm x
    simp only at hx
    linarith
  · obtain ⟨M, hM⟩ := exists_forall_ge_of_even P hd heven hlc
    intro hsurj
    obtain ⟨x, hx⟩ := hsurj (M + 1)
    have := hM x
    simp only at hx
    linarith

/-! ### The sharp characterisation -/

/-- **Main theorem.** A real polynomial function `x ↦ P.eval x` is surjective onto `ℝ` if and
only if `P` has odd degree. Odd degree forces a root of every shift `P - C y` (surjectivity);
even degree (including the constant case `natDegree = 0`) makes `P` bounded on one side, so it
misses values. -/
theorem eval_surjective_iff_odd_natDegree (P : ℝ[X]) :
    Function.Surjective (fun x => P.eval x) ↔ Odd P.natDegree := by
  constructor
  · intro hsurj
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
    · -- constant polynomial: image is a single point
      set c := P.coeff 0 with hc
      have hPC : P = C c := eq_C_of_natDegree_eq_zero h0
      obtain ⟨x, hx⟩ := hsurj (c + 1)
      simp only [hPC, eval_C] at hx
      linarith
    · exact not_surjective_of_even_natDegree P hpos hodd hsurj
  · exact eval_surjective_of_odd_natDegree P

/-- Range form of the main theorem: an odd-degree real polynomial function has range all of
`ℝ`. -/
theorem range_eval_eq_univ_of_odd (P : ℝ[X]) (hodd : Odd P.natDegree) :
    Set.range (fun x => P.eval x) = Set.univ :=
  (eval_surjective_of_odd_natDegree P hodd).range_eq

end FTAOddDegreeSurjective
