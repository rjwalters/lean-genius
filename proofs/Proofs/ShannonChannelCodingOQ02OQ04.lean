/-
  Symmetric Channel Capacity: Generalization of BSC Proof

  Open Question 04 (from ShannonChannelCodingOQ02):
  "Extend to general symmetric channels beyond BSC"

  A DMChannel W : α → β → ℝ is symmetric in the relevant sense when:
  (1) Row symmetry: ∃ C : ℝ, ∀ x : α, ∑_y W(x,y)·log(W(x,y)) = C
      (all rows have the same entropy sum, so H(Y|X=x) is constant in x)
  (2) Doubly balanced: ∀ y : β, ∑_x W(x,y) = |α|/|β|
      (uniform input → uniform output, achieving H(Y) = log|β|)
  (3) Positive: W(x,y) > 0 for all x, y

  Main result: channelCapacity ch = log|β| + C = log|β| - H(row)
  where H(row) = -C ≥ 0 is the (common) entropy of any row of W.

  This generalizes the BSC result (C = log 2 - h(p)) to arbitrary
  finite input/output alphabets α, β.

  Proof structure mirrors ShannonChannelCodingOQ02 (BSC case):
  1. Uniform input distribution on general Fintype
  2. Entropy of uniform distribution = log|α|
  3. H(Y|X) = -C for any input distribution (row symmetry + W > 0)
  4. Uniform input gives uniform output (doubly balanced)
  5. Uniform MI = log|β| + C (achievability)
  6. All MI ≤ log|β| + C (converse via chain rule)
  7. Capacity = log|β| + C (main theorem)
  8. BSC verification: BSC satisfies all hypotheses

  Axioms: 4 (inherited from ShannonChannelCoding via import chain)
  Sorries: 0
  Theorems: 8
-/
import Mathlib
import Proofs.ShannonChannelCoding
import Proofs.ShannonChannelCodingOQ02

open Real Finset InformationTheory InformationTheory.ChannelCoding

namespace InformationTheory.ChannelCoding.SymmetricCapacity

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ## Chain rule: MI = H(Y) - H(Y|X) (general version) -/

/-- Mutual information equals output entropy minus conditional output entropy.
    This is a restatement of the chain rule for general joint distributions. -/
private theorem mi_eq_HY_sub_HYgivenX
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    mutualInformation pXY =
    shannonEntropy (fun y => ∑ x : α, pXY (x, y)) -
    conditionalEntropy (transposeJoint pXY) := by
  rw [mutual_info_symm]
  have hp' := transposeJoint_nonneg hp
  have hsum' := transposeJoint_sum hsum
  rw [chain_rule hp' hsum']
  congr 1
  ext y; simp [transposeJoint]

/-! ## Uniform input distribution on a general Fintype -/

/-- Uniform distribution on a nonempty Fintype: assigns weight 1/|α| to each element. -/
noncomputable def uniformDist [Nonempty α] : InputDist α where
  p := fun _ => 1 / (Fintype.card α : ℝ)
  nonneg := fun _ => by positivity
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [(Nat.cast_pos.mpr Fintype.card_pos).ne']

/-- Uniform distribution is strictly positive. -/
lemma uniformDist_pos [Nonempty α] (x : α) : 0 < (uniformDist (α := α)).p x :=
  div_pos one_pos (Nat.cast_pos.mpr Fintype.card_pos)

/-! ## Entropy of the uniform distribution -/

/-- Shannon entropy of the uniform distribution on α equals log|α|. -/
theorem entropy_uniform_fintype [Nonempty α] :
    shannonEntropy (uniformDist (α := α)).p = Real.log (Fintype.card α) := by
  have hcard : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hne : (1 : ℝ) / Fintype.card α ≠ 0 := div_ne_zero one_ne_zero hcard.ne'
  simp only [shannonEntropy, uniformDist, if_neg hne,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- After simp: -(↑|α| * (1/↑|α| * log(1/↑|α|))) = log ↑|α|
  have h1 : (Fintype.card α : ℝ) * (1 / (Fintype.card α : ℝ) *
      Real.log (1 / (Fintype.card α : ℝ))) = Real.log (1 / (Fintype.card α : ℝ)) := by
    field_simp [hcard.ne']
  rw [h1, show (1 : ℝ) / (Fintype.card α : ℝ) = ((Fintype.card α : ℝ))⁻¹ from one_div _,
      Real.log_inv, neg_neg]

/-! ## H(Y|X) = -C for symmetric channels -/

/-- For a channel where all rows have the same entropy sum C and all transition
    probabilities are positive, the conditional output entropy equals -C regardless
    of the input distribution.

    Proof: Unfold conditionalEntropy on transposeJoint(jointDist). The denominator
    ∑_{y'} p(x)·W(x,y') = p(x) cancels. When p(x) = 0, terms vanish. When p(x) > 0,
    simplification gives p(x)·W(x,y)·log(W(x,y)). Summing: ∑_x p(x)·∑_y W(x,y)·log(W(x,y))
    = ∑_x p(x)·C = C, so the conditional entropy is -C. -/
theorem sym_conditional_output_entropy
    (ch : DMChannel α β) (inp : InputDist α)
    (hW : ∀ x y, 0 < ch.W x y)
    {C : ℝ} (hrow : ∀ x : α, ∑ y : β, ch.W x y * Real.log (ch.W x y) = C) :
    conditionalEntropy (transposeJoint (jointDist ch inp)) = -C := by
  unfold conditionalEntropy transposeJoint jointDist
  dsimp only
  -- Denominator for each input x: ∑_{y':β} p(x)·W(x,y') = p(x)
  have hden : ∀ x : α, ∑ y' : β, inp.p x * ch.W x y' = inp.p x :=
    fun x => by rw [← Finset.mul_sum, ch.sum_one, mul_one]
  -- Simplify each term: two cases (p(x) = 0 or p(x) > 0)
  have hterm : ∀ (y : β) (x : α),
      (if inp.p x * ch.W x y = 0 then (0 : ℝ)
       else inp.p x * ch.W x y *
         Real.log (inp.p x * ch.W x y / (∑ y' : β, inp.p x * ch.W x y'))) =
      inp.p x * (ch.W x y * Real.log (ch.W x y)) := by
    intro y x
    rcases (inp.nonneg x).eq_or_gt with ha | ha
    · simp [ha.symm]
    · have hne : inp.p x * ch.W x y ≠ 0 := (mul_pos ha (hW x y)).ne'
      rw [if_neg hne, hden x, mul_div_cancel_left₀ _ ha.ne']
      ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hrow]
  congr 1
  rw [← Finset.sum_mul, inp.sum_one, one_mul]

/-! ## Doubly balanced: uniform input → uniform output -/

/-- For a doubly balanced channel (column sums = |α|/|β|), the uniform input
    distribution produces a uniform output distribution with weight 1/|β|. -/
lemma sym_uniform_ymarg [Nonempty α]
    (ch : DMChannel α β)
    (hbal : ∀ y : β, ∑ x : α, ch.W x y = (Fintype.card α : ℝ) / Fintype.card β)
    (y : β) :
    ∑ x : α, jointDist ch (uniformDist (α := α)) (x, y) = 1 / Fintype.card β := by
  simp only [jointDist, uniformDist]
  rw [← Finset.mul_sum, hbal y]
  have hα : (Fintype.card α : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  field_simp [hα]

/-! ## Mutual information for uniform input -/

/-- For a symmetric channel, the uniform input achieves MI = log|β| + C.
    This is the achievability direction: uniform input gives H(Y) = log|β|
    (doubly balanced) and H(Y|X) = -C (row symmetry). -/
theorem sym_uniform_mi [Nonempty α] [Nonempty β]
    (ch : DMChannel α β)
    (hW : ∀ x y, 0 < ch.W x y)
    {C : ℝ} (hrow : ∀ x : α, ∑ y : β, ch.W x y * Real.log (ch.W x y) = C)
    (hbal : ∀ y : β, ∑ x : α, ch.W x y = (Fintype.card α : ℝ) / Fintype.card β) :
    channelMI ch (uniformDist (α := α)) = Real.log (Fintype.card β) + C := by
  unfold channelMI
  have hjoint_nn : ∀ xy, 0 ≤ jointDist ch (uniformDist (α := α)) xy :=
    fun xy => le_of_lt (mul_pos (uniformDist_pos xy.1) (hW xy.1 xy.2))
  have hjoint_sum := jointDist_sum_one ch (uniformDist (α := α))
  rw [mi_eq_HY_sub_HYgivenX hjoint_nn hjoint_sum]
  rw [sym_conditional_output_entropy ch (uniformDist (α := α)) hW hrow]
  -- Y-marginal under uniform input is uniform (by doubly balanced)
  have hymarg : (fun y => ∑ x : α, jointDist ch (uniformDist (α := α)) (x, y)) =
      fun _ : β => (1 : ℝ) / Fintype.card β :=
    funext (sym_uniform_ymarg ch hbal)
  rw [hymarg]
  -- Entropy of uniform distribution on β = log|β|
  have heq : (fun (_ : β) => (1 : ℝ) / Fintype.card β) = (uniformDist (α := β)).p := rfl
  rw [heq, entropy_uniform_fintype (α := β)]
  ring

/-! ## MI upper bound for all inputs -/

/-- For a symmetric channel, MI(X;Y) ≤ log|β| + C for all input distributions.
    Proof: MI = H(Y) - H(Y|X) = H(Y) + C ≤ log|β| + C by entropy maximality. -/
theorem sym_mi_le
    (ch : DMChannel α β) (inp : InputDist α)
    (hW : ∀ x y, 0 < ch.W x y)
    {C : ℝ} (hrow : ∀ x : α, ∑ y : β, ch.W x y * Real.log (ch.W x y) = C) :
    channelMI ch inp ≤ Real.log (Fintype.card β) + C := by
  unfold channelMI
  have hjoint_nn : ∀ xy, 0 ≤ jointDist ch inp xy :=
    fun xy => mul_nonneg (inp.nonneg xy.1) (le_of_lt (hW xy.1 xy.2))
  have hjoint_sum := jointDist_sum_one ch inp
  rw [mi_eq_HY_sub_HYgivenX hjoint_nn hjoint_sum,
      sym_conditional_output_entropy ch inp hW hrow]
  -- Suffices: H(Y-marginal) ≤ log|β|
  have hymarg_nn : ∀ y : β, 0 ≤ ∑ x, jointDist ch inp (x, y) :=
    fun y => Finset.sum_nonneg (fun x _ => hjoint_nn (x, y))
  have hymarg_sum : ∑ y : β, (∑ x, jointDist ch inp (x, y)) = 1 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact hjoint_sum
  linarith [entropy_le_log_card hymarg_nn hymarg_sum]

/-! ## Main theorem: Symmetric channel capacity -/

/-- **Symmetric Channel Capacity Theorem**.
    For a channel that is row-symmetric (all rows have the same entropy C)
    and doubly balanced (uniform input → uniform output) with positive
    transition probabilities, the channel capacity equals log|β| + C.

    Upper bound: For all inputs, MI ≤ H(Y) + C ≤ log|β| + C (chain rule + entropy bound).
    Achievability: Uniform input achieves MI = log|β| + C (by double balance + row symmetry).

    Setting C = -h(p) and α = β = Bool recovers the BSC capacity log 2 - h(p). -/
theorem sym_channel_capacity [Nonempty α] [Nonempty β]
    (ch : DMChannel α β)
    (hW : ∀ x y, 0 < ch.W x y)
    {C : ℝ} (hrow : ∀ x : α, ∑ y : β, ch.W x y * Real.log (ch.W x y) = C)
    (hbal : ∀ y : β, ∑ x : α, ch.W x y = (Fintype.card α : ℝ) / Fintype.card β) :
    channelCapacity ch = Real.log (Fintype.card β) + C := by
  unfold channelCapacity
  apply le_antisymm
  · -- Upper bound: sSup ≤ log|β| + C
    apply csSup_le
    · exact ⟨_, uniformDist (α := α), rfl⟩
    · rintro r ⟨inp, rfl⟩
      exact sym_mi_le ch inp hW hrow
  · -- Lower bound: log|β| + C ≤ sSup (achieved by uniform input)
    apply le_csSup
    · -- BddAbove: each MI ≤ log|β| ≤ log|β| + ... (use log|β| as upper bound)
      exact ⟨Real.log (Fintype.card β), fun _ ⟨inp, hr⟩ => hr ▸ channelMI_le_log_card ch inp⟩
    · exact ⟨uniformDist (α := α), sym_uniform_mi ch hW hrow hbal⟩

/-! ## Examples: BSC satisfies the hypotheses -/

/-- The BSC satisfies the row symmetry hypothesis with C = p·log(p) + (1-p)·log(1-p). -/
theorem bsc_row_symmetric {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ x : Bool, ∑ y : Bool, (bsc p (le_of_lt hp0) (le_of_lt hp1)).W x y *
      Real.log ((bsc p (le_of_lt hp0) (le_of_lt hp1)).W x y) =
    p * Real.log p + (1 - p) * Real.log (1 - p) := by
  intro x; simp only [Fintype.sum_bool, bsc]; cases x <;> simp <;> ring

/-- BSC is doubly balanced: column sums = |Bool|/|Bool| = 1. -/
theorem bsc_doubly_balanced {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∀ y : Bool, ∑ x : Bool, (bsc p (le_of_lt hp0) (le_of_lt hp1)).W x y =
    (Fintype.card Bool : ℝ) / Fintype.card Bool := by
  intro y; simp only [Fintype.sum_bool, bsc, Fintype.card_bool, Nat.cast_ofNat]
  cases y <;> simp <;> ring

/-- BSC capacity recovered from the symmetric channel theorem:
    C(BSC(p)) = log 2 + (p·log p + (1-p)·log(1-p)) = log 2 - h(p). -/
theorem bsc_capacity_from_symmetric {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (bsc p (le_of_lt hp0) (le_of_lt hp1)) =
    Real.log 2 + (p * Real.log p + (1 - p) * Real.log (1 - p)) :=
  sym_channel_capacity (bsc p (le_of_lt hp0) (le_of_lt hp1))
    (fun x y => by simp only [bsc]; split_ifs <;> linarith)
    (bsc_row_symmetric hp0 hp1)
    (bsc_doubly_balanced hp0 hp1)

end InformationTheory.ChannelCoding.SymmetricCapacity
