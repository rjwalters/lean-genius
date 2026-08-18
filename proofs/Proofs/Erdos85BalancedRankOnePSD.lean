import Proofs.Erdos85OrientedMassBounds

/-!
# The balanced negative rank-one positivity obstruction

Suppose rectangular blocks `A : S × T`, `B : T × S` satisfy a factored
square identity `A·B = a·I + 1·sᵀ` with `a < 0`, positive left weights
`s`, nonnegative right weights `t`, and the detailed-balance relation
`s_i A_{ik} = B_{ki} t_k`.  Then `|S| ≤ 1`: on a vector orthogonal to
`s`, the balanced quadratic form is simultaneously
`a·Σ s_i x_i² < 0` and `Σ_k t_k (Bx)_k² ≥ 0`.

Instantiated with `S` the triangle-free-colored defect components and
`T` the antipodal ones, `a = d - 7` shows that a boundary graph of
degree `4` or `6` has at most one triangle-free-colored component.
-/

namespace Erdos85

noncomputable section

/-- **Balanced negative rank-one positivity.**  A factored square
identity `A·B = a·I + 1·sᵀ` with `a < 0`, positive `s`, nonnegative `t`,
and detailed balance forces the index type `S` to be a singleton or
empty. -/
theorem card_le_one_of_balanced_negative_rankOne
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S]
    (A : Matrix S T ℚ) (B : Matrix T S ℚ)
    (s : S → ℚ) (t : T → ℚ)
    (hs : ∀ i, 0 < s i) (ht : ∀ j, 0 ≤ t j)
    {a : ℚ} (ha : a < 0)
    (hAB : ∀ i j, (A * B) i j = (if i = j then a else 0) + s j)
    (hbal : ∀ i k, s i * A i k = B k i * t k) :
    Fintype.card S ≤ 1 := by
  by_contra hcard
  push_neg at hcard
  obtain ⟨i₀, i₁, hne⟩ := Fintype.exists_pair_of_one_lt_card hcard
  classical
  set x : S → ℚ := fun i ↦
    if i = i₀ then s i₁ else if i = i₁ then -(s i₀) else 0 with hxdef
  have hx0 : x i₀ = s i₁ := by simp [hxdef]
  have hx1 : x i₁ = -(s i₀) := by simp [hxdef, hne.symm]
  have hxs : (∑ j, s j * x j) = 0 := by
    have hsplit : ∀ j, s j * x j =
        (if j = i₀ then s j * s i₁ else 0) +
          (if j = i₁ then s j * -(s i₀) else 0) := by
      intro j
      by_cases h0 : j = i₀
      · subst h0
        simp [hxdef, hne]
      · by_cases h1 : j = i₁
        · subst h1
          simp [hxdef, h0]
        · simp [hxdef, h0, h1]
    rw [Finset.sum_congr rfl fun j _ ↦ hsplit j, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    ring
  have hrow : ∀ i, (∑ j, s i * x i * ((A * B) i j * x j)) =
      s i * x i * (a * x i) + s i * x i * (∑ j, s j * x j) := by
    intro i
    have hterm : ∀ j, s i * x i * ((A * B) i j * x j) =
        s i * x i * ((if i = j then a else 0) * x j) +
          s i * x i * (s j * x j) := by
      intro j
      rw [hAB, add_mul, mul_add]
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_add_distrib]
    congr 1
    · rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_congr rfl fun j _ ↦ by rw [ite_mul, zero_mul],
        Finset.sum_ite_eq]
      simp
    · rw [← Finset.mul_sum]
  have hform : (∑ i, ∑ j, s i * x i * ((A * B) i j * x j)) =
      a * ∑ i, s i * x i ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ ↦ hrow i, Finset.sum_add_distrib]
    have hz : (∑ i, s i * x i * (∑ j, s j * x j)) = 0 := by
      rw [hxs]
      simp
    rw [hz, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hexp : ∀ i j, s i * x i * ((A * B) i j * x j) =
      ∑ k, (s i * A i k * x i) * (B k j * x j) := by
    intro i j
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hform' : (∑ i, ∑ j, s i * x i * ((A * B) i j * x j)) =
      ∑ k, t k * (∑ i, B k i * x i) ^ 2 := by
    calc
      (∑ i, ∑ j, s i * x i * ((A * B) i j * x j)) =
          ∑ i, ∑ j, ∑ k, (s i * A i k * x i) * (B k j * x j) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl
          fun j _ ↦ hexp i j
      _ = ∑ i, ∑ k, ∑ j, (s i * A i k * x i) * (B k j * x j) :=
        Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, (s i * A i k * x i) * (B k j * x j) :=
        Finset.sum_comm
      _ = ∑ k, ∑ i, (s i * A i k * x i) * (∑ j, B k j * x j) := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = ∑ k, (∑ i, s i * A i k * x i) * (∑ j, B k j * x j) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
      _ = ∑ k, (t k * ∑ i, B k i * x i) * (∑ j, B k j * x j) := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        calc
          s i * A i k * x i = (s i * A i k) * x i := by ring
          _ = (B k i * t k) * x i := by rw [hbal i k]
          _ = t k * (B k i * x i) := by ring
      _ = ∑ k, t k * (∑ i, B k i * x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hpos : (0 : ℚ) < ∑ i, s i * x i ^ 2 := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hs i).le (sq_nonneg _)
    · exact ⟨i₀, Finset.mem_univ _, by
        rw [hx0]
        exact mul_pos (hs i₀) (pow_pos (hs i₁) 2)⟩
  have hneg : a * (∑ i, s i * x i ^ 2) < 0 :=
    mul_neg_of_neg_of_pos ha hpos
  have hnonneg : (0 : ℚ) ≤ ∑ k, t k * (∑ i, B k i * x i) ^ 2 :=
    Finset.sum_nonneg fun k _ ↦ mul_nonneg (ht k) (sq_nonneg _)
  have hkey := hform.symm.trans hform'
  linarith

/-- **Positive rank-one factorization bounds the sector.**  When
`A·B = a·I + 1·sᵀ` with `a > 0` and `s ≥ 0`, the right factor is
injective — the perturbed identity kills only constant vectors, and the
positive trace weight kills those — so `|S| ≤ |T|`.  No balance
hypothesis is needed. -/
theorem card_le_card_of_positive_rankOne_factorization
    {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (A : Matrix S T ℚ) (B : Matrix T S ℚ)
    (s : S → ℚ) (hs : ∀ i, 0 ≤ s i)
    {a : ℚ} (ha : 0 < a)
    (hAB : ∀ i j, (A * B) i j = (if i = j then a else 0) + s j) :
    Fintype.card S ≤ Fintype.card T := by
  classical
  have hMx : ∀ x : S → ℚ, B.mulVec x = 0 → x = 0 := by
    intro x hBx
    have hABx : (A * B).mulVec x = 0 := by
      rw [← Matrix.mulVec_mulVec, hBx, Matrix.mulVec_zero]
    have hentry : ∀ i, a * x i + (∑ j, s j * x j) = 0 := by
      intro i
      have h : (∑ j, (A * B) i j * x j) = 0 := congrFun hABx i
      rw [Finset.sum_congr rfl (fun j _ ↦ by
        rw [hAB, add_mul, ite_mul, zero_mul])] at h
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq] at h
      simpa using h
    rcases isEmpty_or_nonempty S with hS | hS
    · funext i
      exact isEmptyElim i
    · obtain ⟨i₀⟩ := hS
      have hconst : ∀ i, x i = x i₀ := by
        intro i
        have h1 := hentry i
        have h2 := hentry i₀
        have h3 : a * x i = a * x i₀ := by linarith
        exact mul_left_cancel₀ (ne_of_gt ha) h3
      have hσc : (∑ j, s j * x j) = (∑ j, s j) * x i₀ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [hconst j]
      have h0 := hentry i₀
      rw [hσc] at h0
      have hx0 : x i₀ = 0 := by
        have hpos : 0 < a + ∑ j, s j := by
          have := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) ↦ hs j
          linarith
        have hzero : (a + ∑ j, s j) * x i₀ = 0 := by
          rw [add_mul]
          exact h0
        exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hpos)
      funext i
      rw [hconst i, hx0]
      rfl
  have hinj : Function.Injective B.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact hMx x (by simpa using hx)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_pi, Module.finrank_pi] at hle

end

end Erdos85
