import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev

/-!
# Arithmetic collapse of leakage from the square minimum layer

For coefficient-one minimum components, write `Lᵢ` for quotient row mass
toward larger components, `S = ∑ Lᵢ`, and `k` for the size of the minimum
layer.  Source uniqueness for proper cyclic covers gives `k+S ≤ N`.
Summing the rowwise Cauchy inequalities gives

`(k*d-S)² ≤ k*(k*(s²+p)-S)`.

In the exact-square family these inequalities force `S<k` as soon as
`k≥2`.  Since every positive `Lᵢ` is at least two, a zero-leakage row is
forced.  The zero row then collapses all remaining coefficient mass.
-/

namespace Erdos85

/-- The arithmetic core of the minimum-layer cross-pair argument.

Write `a` for the minimum normalized component order, `u` for the number of
minimum components, `S` for their total quotient mass toward larger
components, and `R` for the (nonnegative) sum of the squared leakages.  The
cross-pair identity is

`u * (N - u*a) * p + R = (2*d - 1) * S`.

If larger targets are incident to at most one minimum component, detailed
balance gives `a*S ≤ N-u*a`.  For `p>d`, these two facts force either the
outside coefficient mass to vanish or both `a` and `u` to equal one. -/
theorem minimumLayer_disjointTarget_collapse
    (d p N a u S R : ℕ)
    (hdp : d < p) (ha : 0 < a) (hu : 0 < u)
    (hua : u * a ≤ N)
    (hS : a * S ≤ N - u * a)
    (hidentity : u * (N - u * a) * p + R = (2 * d - 1) * S) :
    N = u * a ∨ (a = 1 ∧ u = 1) := by
  by_cases hall : N = u * a
  · exact Or.inl hall
  · right
    have houtside : 0 < N - u * a := Nat.sub_pos_of_lt (lt_of_le_of_ne hua (Ne.symm hall))
    have hmain : u * (N - u * a) * p ≤ (2 * d - 1) * S := by
      omega
    have hscaled : (N - u * a) * (a * u * p) ≤
        (N - u * a) * (2 * d - 1) := by
      calc
        (N - u * a) * (a * u * p) = a * (u * (N - u * a) * p) := by ring
        _ ≤ a * ((2 * d - 1) * S) := Nat.mul_le_mul_left a hmain
        _ = (2 * d - 1) * (a * S) := by ring
        _ ≤ (2 * d - 1) * (N - u * a) :=
          Nat.mul_le_mul_left (2 * d - 1) hS
        _ = (N - u * a) * (2 * d - 1) := by ring
    have haup : a * u * p ≤ 2 * d - 1 :=
      Nat.le_of_mul_le_mul_left hscaled houtside
    have hau : a * u = 1 := by
      by_contra hne
      have hau2 : 2 ≤ a * u := by
        have hau0 : 0 < a * u := Nat.mul_pos ha hu
        omega
      have hpLower : d + 1 ≤ p := by omega
      have hcontra : 2 * d + 2 ≤ a * u * p := by
        calc
          2 * d + 2 = 2 * (d + 1) := by ring
          _ ≤ 2 * p := Nat.mul_le_mul_left 2 hpLower
          _ ≤ a * u * p := Nat.mul_le_mul_right p hau2
      omega
    have ha_le : a ≤ 1 := by
      calc
        a = a * 1 := by omega
        _ ≤ a * u := Nat.mul_le_mul_left a (by omega)
        _ = 1 := hau
    have hu_le : u ≤ 1 := by
      calc
        u = 1 * u := by omega
        _ ≤ a * u := Nat.mul_le_mul_right u (by omega)
        _ = 1 := hau
    exact ⟨by omega, by omega⟩

/-- If each target is used by at most one source and a positive incidence
has value equal to the target weight, total incidence mass is bounded by
total target weight. -/
theorem disjoint_target_total_incidence_le_weight
    {I J : Type*} [Fintype I] [Fintype J]
    (q : I → J → ℕ) (w : J → ℕ)
    (hunique : ∀ i₁ i₂ j, 0 < q i₁ j → 0 < q i₂ j → i₁ = i₂)
    (hexact : ∀ i j, 0 < q i j → q i j = w j) :
    ∑ i, ∑ j, q i j ≤ ∑ j, w j := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hnone : ∀ i, q i j = 0
  · simp [hnone]
  · push Not at hnone
    obtain ⟨i, hi⟩ := hnone
    have hipos : 0 < q i j := Nat.pos_of_ne_zero hi
    calc
      ∑ a, q a j = q i j := by
        apply Finset.sum_eq_single i
        · intro b hb hbi
          by_contra hb0
          have hbpos : 0 < q b j := Nat.pos_of_ne_zero hb0
          exact hbi (hunique b i j hbpos hipos)
        · simp
      _ = w j := hexact i j hipos
      _ ≤ w j := le_rfl

/-- Finset form of `disjoint_target_total_incidence_le_weight`. -/
theorem disjoint_target_finset_total_incidence_le_weight
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J) (q : I → J → ℕ) (w : J → ℕ)
    (hunique : ∀ i₁ ∈ S, ∀ i₂ ∈ S, ∀ j ∈ T,
      0 < q i₁ j → 0 < q i₂ j → i₁ = i₂)
    (hexact : ∀ i ∈ S, ∀ j ∈ T, 0 < q i j → q i j = w j) :
    ∑ i ∈ S, ∑ j ∈ T, q i j ≤ ∑ j ∈ T, w j := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hnone : ∀ i ∈ S, q i j = 0
  · have hz : ∑ i ∈ S, q i j = 0 :=
      Finset.sum_eq_zero fun i hi ↦ hnone i hi
    rw [hz]
    exact Nat.zero_le _
  · push Not at hnone
    obtain ⟨i, hiS, hi⟩ := hnone
    have hipos : 0 < q i j := Nat.pos_of_ne_zero hi
    calc
      ∑ a ∈ S, q a j = q i j := by
        apply Finset.sum_eq_single i
        · intro b hb hbi
          by_contra hb0
          have hbpos : 0 < q b j := Nat.pos_of_ne_zero hb0
          exact hbi (hunique b hb i hiS j hj hbpos hipos)
        · intro hiNot
          exact (hiNot hiS).elim
      _ = w j := hexact i hiS j hj hipos
      _ ≤ w j := le_rfl

/-- With unit weight on the source layer, disjoint target incidence is
bounded by the coefficient mass outside that layer. -/
theorem unitLayer_total_incidence_le_outsideWeight
    {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset C) (q : C → C → ℕ) (w : C → ℕ) (N : ℕ)
    (hunit : ∀ i ∈ S, w i = 1)
    (hweight : ∑ i, w i = N)
    (hunique : ∀ i₁ ∈ S, ∀ i₂ ∈ S,
      ∀ j ∈ Finset.univ \ S, 0 < q i₁ j → 0 < q i₂ j → i₁ = i₂)
    (hexact : ∀ i ∈ S, ∀ j ∈ Finset.univ \ S,
      0 < q i j → q i j = w j) :
    ∑ i ∈ S, ∑ j ∈ Finset.univ \ S, q i j ≤ N - S.card := by
  have hinc := disjoint_target_finset_total_incidence_le_weight
    S (Finset.univ \ S) q w hunique hexact
  have hsplit := Finset.sum_sdiff (f := w) (Finset.subset_univ S)
  have hsumS : ∑ i ∈ S, w i = S.card := by
    calc
      _ = ∑ _i ∈ S, 1 := Finset.sum_congr rfl fun i hi ↦ hunit i hi
      _ = S.card := by simp
  rw [hweight, hsumS] at hsplit
  omega

/-- Summing rowwise Cauchy inequalities and applying Cauchy once more across
the rows gives the aggregate inequality used by the leakage terminal. -/
theorem aggregate_minimumLayer_row_cauchy
    {I : Type*} [Fintype I]
    (d C k S : ℚ) (L : I → ℚ)
    (hk : (Fintype.card I : ℚ) = k)
    (hS : ∑ i, L i = S)
    (hrow : ∀ i, (d - L i) ^ 2 ≤ k * (C - L i)) :
    (k * d - S) ^ 2 ≤ k * k * (k * C - S) := by
  have hsum : ∑ i, (d - L i) = k * d - S := by
    rw [Finset.sum_sub_distrib, hS]
    simp [hk]
  have hsq := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset I)) (f := fun i ↦ d - L i)
  have hsumSq : ∑ i, (d - L i) ^ 2 ≤ k * (k * C - S) := by
    calc
      _ ≤ ∑ i, k * (C - L i) :=
        Finset.sum_le_sum fun i _ ↦ hrow i
      _ = k * (k * C - S) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hS]
        simp [hk]
  rw [hsum] at hsq
  have hsq' : (k * d - S) ^ 2 ≤ k * ∑ i, (d - L i) ^ 2 := by
    simpa only [Finset.card_univ, hk] using hsq
  have hk0 : 0 ≤ k := by rw [← hk]; positivity
  have hmul := mul_le_mul_of_nonneg_left hsumSq hk0
  exact hsq'.trans (by simpa [mul_assoc] using hmul)

/-- **Aggregate minimum-layer leakage is smaller than the layer.** -/
theorem square_minimum_totalLeakage_lt_card
    (s d p N k S : ℚ)
    (hs7 : 7 ≤ s) (hk2 : 2 ≤ k) (hS0 : 0 ≤ S)
    (hd : d = s * s + 3) (hp : p = d + s)
    (hN : N = d - s)
    (hmass : k + S ≤ N)
    (hCS : (k * d - S) ^ 2 ≤
      k * k * (k * (s * s + p) - S)) :
    S < k := by
  subst N
  subst p
  subst d
  have hs0 : 0 < s := by linarith
  have hk0 : 0 < k := by linarith
  by_contra hnot
  have hkS : k ≤ S := le_of_not_gt hnot
  let x : ℚ := S / k
  have hkne : k ≠ 0 := ne_of_gt hk0
  have hxdef : k * x = S := by
    dsimp only [x]
    field_simp
  have hx0 : 0 ≤ x := by
    rw [← hxdef] at hS0
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hS0) hk0
  have hx1 : 1 ≤ x := by
    rw [← hxdef] at hkS
    nlinarith
  have hmassX : k * (1 + x) ≤ s * s + 3 - s := by
    nlinarith [hmass, hxdef]
  have hCSx :
      (s * s + 3 - x) ^ 2 ≤
        k * (s * s + (s * s + 3 + s) - x) := by
    have hleft :
        (k * (s * s + 3) - S) ^ 2 =
          k ^ 2 * (s * s + 3 - x) ^ 2 := by
      rw [← hxdef]
      ring
    have hright :
        k * k * (k * (s * s + (s * s + 3 + s)) - S) =
          k ^ 2 * (k * (s * s + (s * s + 3 + s) - x)) := by
      rw [← hxdef]
      ring
    rw [hleft, hright] at hCS
    have hkSqPos : 0 < k ^ 2 := sq_pos_of_pos hk0
    nlinarith
  have hCx : 0 ≤ s * s + (s * s + 3 + s) - x := by
    by_contra hneg
    have : k * (s * s + (s * s + 3 + s) - x) < 0 :=
      mul_neg_of_pos_of_neg hk0 (lt_of_not_ge hneg)
    nlinarith [sq_nonneg (s * s + 3 - x)]
  have hcombined :
      (s * s + 3 - x) ^ 2 * (1 + x) ≤
        (s * s + 3 - s) *
          (s * s + (s * s + 3 + s) - x) := by
    calc
      _ ≤ (k * (s * s + (s * s + 3 + s) - x)) * (1 + x) :=
        mul_le_mul_of_nonneg_right hCSx (by linarith)
      _ = (k * (1 + x)) *
          (s * s + (s * s + 3 + s) - x) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmassX hCx
  have hNltP : s * s + 3 - s < s * s + 3 + s := by linarith
  have htwoX : 2 * (1 + x) ≤ s * s + 3 - s := by
    nlinarith
  have hxp : x + 1 - (s * s + 3 + s) < 0 := by
    nlinarith
  have hquadDiff :
      (x ^ 2 - (s * s + 3 + s) * x + s * s) -
          (1 - (s * s + 3 + s) + s * s) =
        (x - 1) * (x + 1 - (s * s + 3 + s)) := by ring
  have hquadNeg : x ^ 2 - (s * s + 3 + s) * x + s * s < 0 := by
    have hprod :
        (x - 1) * (x + 1 - (s * s + 3 + s)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hxp.le
    nlinarith [hquadDiff]
  have hlinearNeg : -s * s + s + x - 2 < 0 := by
    nlinarith
  have hfactor :
      (s * s + 3 - x) ^ 2 * (1 + x) -
          (s * s + 3 - s) *
            (s * s + (s * s + 3 + s) - x) =
        (-s * s + s + x - 2) *
          (-s * s * x + s * s - s * x + x ^ 2 - 3 * x) := by
    ring
  have hsecond :
      -s * s * x + s * s - s * x + x ^ 2 - 3 * x =
        x ^ 2 - (s * s + 3 + s) * x + s * s := by ring
  rw [hsecond] at hfactor
  have hpositive : 0 <
      (s * s + 3 - x) ^ 2 * (1 + x) -
        (s * s + 3 - s) *
          (s * s + (s * s + 3 + s) - x) := by
    rw [hfactor]
    exact mul_pos_of_neg_of_neg hlinearNeg hquadNeg
  linarith

/-- If positive leakages are at least two and their total is smaller than
the number of rows, at least one row has zero leakage. -/
theorem exists_zero_of_total_lt_card_of_pos_ge_two
    {I : Type*} [Fintype I]
    (L : I → ℕ)
    (hgap : ∀ i, 0 < L i → 2 ≤ L i)
    (hsum : ∑ i, L i < Fintype.card I) :
    ∃ i, L i = 0 := by
  by_contra hnone
  push Not at hnone
  have htwo : ∀ i, 2 ≤ L i := by
    intro i
    exact hgap i (Nat.pos_of_ne_zero (hnone i))
  have hbound : 2 * Fintype.card I ≤ ∑ i, L i := by
    calc
      2 * Fintype.card I = ∑ _i : I, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : I, L i := Finset.sum_le_sum fun i _ ↦ htwo i
  omega

/-- A zero-leakage quotient row forces the outside coefficient mass to
vanish once `p>d`, provided total leakage is bounded by that outside mass. -/
theorem outsideMass_eq_zero_of_zeroLeakage_row
    (p d N k S weighted : ℕ)
    (hdp : d < p) (hkN : k ≤ N)
    (hS : S ≤ N - k)
    (hweighted : weighted ≤ d * S)
    (hrow : weighted = p * (N - k)) :
    N = k := by
  by_contra hne
  have hklt : k < N := lt_of_le_of_ne hkN (Ne.symm hne)
  have hpos : 0 < N - k := Nat.sub_pos_of_lt hklt
  have hpBound : p * (N - k) ≤ d * (N - k) := by
    rw [← hrow]
    exact hweighted.trans (Nat.mul_le_mul_left d hS)
  have := Nat.le_of_mul_le_mul_right hpBound hpos
  omega

/-- Summing the quotient-square equation across a layer from a zero-leakage
row gives the weighted-leakage identity. -/
theorem zeroLeakage_row_weighted_identity
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : Finset C) (Q : C → C → ℕ) (L : C → ℕ)
    (c : C) (d s p : ℕ)
    (hcM : c ∈ M)
    (hrow : ∀ f, ∑ e, Q f e = d)
    (hL : ∀ f, L f = ∑ e ∈ Finset.univ \ M, Q f e)
    (hzero : L c = 0)
    (hsq : ∀ e ∈ M, ∑ f, Q c f * Q f e =
      s * s * (if c = e then 1 else 0) + p) :
    (∑ f ∈ M, Q c f * L f) + s * s + p * M.card = d * d := by
  have hzeroOutside : ∀ f ∈ Finset.univ \ M, Q c f = 0 := by
    intro f hf
    have hsum0 : ∑ e ∈ Finset.univ \ M, Q c e = 0 := by
      rw [← hL c, hzero]
    exact (Finset.sum_eq_zero_iff.mp hsum0) f hf
  have hinside (f : C) : ∑ e ∈ M, Q f e = d - L f := by
    have hsplit := Finset.sum_sdiff (f := fun e ↦ Q f e)
      (Finset.subset_univ M)
    rw [hrow f] at hsplit
    rw [hL f]
    omega
  have hsumSq : (∑ e ∈ M, ∑ f, Q c f * Q f e) =
      s * s + p * M.card := by
    calc
      _ = ∑ e ∈ M, (s * s * (if c = e then 1 else 0) + p) :=
        Finset.sum_congr rfl fun e he ↦ hsq e he
      _ = (∑ e ∈ M, s * s * (if c = e then 1 else 0)) +
          ∑ _e ∈ M, p := by rw [Finset.sum_add_distrib]
      _ = s * s + p * M.card := by
        have hone : (∑ e ∈ M, if c = e then 1 else 0) = 1 := by
          simp [hcM]
        rw [← Finset.mul_sum, hone]
        simp [Nat.mul_comm]
  have hsumPathsAdd :
      (∑ e ∈ M, ∑ f, Q c f * Q f e) +
          ∑ f ∈ M, Q c f * L f = d * d := by
    rw [Finset.sum_comm]
    have hrestrict :
        (∑ f, ∑ e ∈ M, Q c f * Q f e) =
          ∑ f ∈ M, Q c f * (∑ e ∈ M, Q f e) := by
      calc
        (∑ f, ∑ e ∈ M, Q c f * Q f e) =
          ∑ f, Q c f * (∑ e ∈ M, Q f e) := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [Finset.mul_sum]
        _ = ∑ f ∈ M, Q c f * (∑ e ∈ M, Q f e) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ M)
          intro f hfU hfM
          have hfOut : f ∈ Finset.univ \ M :=
            Finset.mem_sdiff.mpr ⟨hfU, hfM⟩
          rw [hzeroOutside f hfOut, zero_mul]
    rw [hrestrict]
    rw [← Finset.sum_add_distrib]
    have hrowc : ∑ f ∈ M, Q c f = d := by
      have hc := hinside c
      rw [hzero, Nat.sub_zero] at hc
      exact hc
    calc
      (∑ f ∈ M,
          (Q c f * (∑ e ∈ M, Q f e) + Q c f * L f)) =
          ∑ f ∈ M, Q c f * d := by
            apply Finset.sum_congr rfl
            intro f hf
            have hLf : L f ≤ d := by
              have hsplit := Finset.sum_sdiff (f := fun e ↦ Q f e)
                (Finset.subset_univ M)
              rw [hrow f, ← hL f] at hsplit
              omega
            rw [hinside f]
            rw [← Nat.mul_add, Nat.sub_add_cancel hLf]
      _ = d * d := by rw [← Finset.sum_mul, hrowc]
  rw [hsumSq] at hsumPathsAdd
  omega

end Erdos85
