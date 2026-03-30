/-
  BSC Capacity Proof and Random Coding Foundation

  Open Question 02: Shannon random coding argument via Mathlib probability

  Main result: BSC(p) capacity = log 2 - h(p), proving the parent file's
  bsc_capacity_eq axiom from first principles.

  The proof proceeds by:
  1. Proving H(Y|X) = h(p) for BSC with any positive input distribution
  2. Using the chain rule: MI(X;Y) = H(Y) - H(Y|X) = H(Y) - h(p)
  3. Upper bound: H(Y) ≤ log|Bool| = log 2, so MI ≤ log 2 - h(p) for all inputs
  4. Achievability: uniform Bernoulli(1/2) input gives H(Y) = log 2
     (BSC is doubly stochastic, so uniform input → uniform output)
  5. Capacity = sSup = log 2 - h(p)

  Axioms: 0
  Sorries: 0
  Theorems: bsc_capacity_proved + 10 supporting lemmas
-/
import Mathlib
import Proofs.ShannonChannelCoding
import Proofs.ShannonChannelCodingOQ04

open Real Finset InformationTheory InformationTheory.ChannelCoding
open InformationTheory.BinaryEntropy

namespace InformationTheory.ChannelCoding.BSCCapacity

/-! ## Uniform input distribution on Bool -/

/-- The uniform distribution on Bool: Bernoulli(1/2). -/
noncomputable def uniformBool : InputDist Bool where
  p := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by simp [Fintype.sum_bool]; ring

/-- Uniform input on Bool is strictly positive. -/
lemma uniformBool_pos (b : Bool) : 0 < uniformBool.p b := by
  simp [uniformBool]; norm_num

/-! ## BSC properties for 0 < p < 1 -/

/-- BSC transition probabilities are positive for 0 < p < 1. -/
lemma bsc_W_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x y : Bool) :
    0 < (bsc p (le_of_lt hp0) (le_of_lt hp1)).W x y := by
  simp only [bsc]
  split_ifs <;> linarith

/-! ## Channel marginal distributions -/

/-- The X-marginal of a channel joint distribution equals the input distribution.
    ∑_y P(X=x,Y=y) = p(x) · ∑_y W(x,y) = p(x). -/
lemma channel_xmarg {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) (inp : InputDist α) (x : α) :
    ∑ y : β, jointDist ch inp (x, y) = inp.p x := by
  simp only [jointDist, ← Finset.mul_sum]
  rw [ch.sum_one x, mul_one]

/-- The Y-marginal for BSC + uniform input equals 1/2.
    BSC is doubly stochastic (column sums = 1), so uniform input → uniform output. -/
lemma bsc_uniform_ymarg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : Bool) :
    ∑ x : Bool, jointDist (bsc p hp0 hp1) uniformBool (x, y) = 1 / 2 := by
  simp only [jointDist, uniformBool, Fintype.sum_bool, bsc]
  cases y <;> simp <;> ring

/-! ## BSC output entropy per input symbol -/

/-- For BSC, the entropy of the output conditioned on a specific input x is the same
    for all x. Specifically, ∑_y W(x,y)·log W(x,y) = p·log(p) + (1-p)·log(1-p)
    regardless of x. This is because BSC treats true and false symmetrically. -/
lemma bsc_output_entropy_per_input {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (x : Bool) :
    ∑ y : Bool, (bsc p (le_of_lt hp0) (le_of_lt hp1)).W x y *
      Real.log ((bsc p (le_of_lt hp0) (le_of_lt hp1)).W x y) =
    p * Real.log p + (1 - p) * Real.log (1 - p) := by
  simp only [Fintype.sum_bool, bsc]
  cases x <;> simp <;> ring

/-! ## Chain rule: MI = H(Y) - H(Y|X) -/

/-- Chain rule in the H(Y) - H(Y|X) direction.
    Combines mutual_info_symm with chain_rule on the transposed distribution. -/
theorem mi_eq_hY_sub_hYgivenX {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
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

/-! ## BSC conditional output entropy H(Y|X) = h(p) -/

/-- **H(Y|X) = h(p) for BSC with any positive input distribution.**
    The conditional output entropy of a BSC depends only on the crossover
    probability, not on the input distribution. This is because BSC is
    a symmetric channel: H(Y|X=x) = h(p) for every input symbol x.

    Proof: Unfold conditionalEntropy on the transposed joint distribution.
    Since all joint probabilities are positive, the if-branches vanish.
    The denominator ∑_y' p(x)·W(x,y') = p(x) cancels, leaving
    ∑_x p(x) · ∑_y W(x,y)·log(W(x,y)). By BSC symmetry, the inner
    sum is p·log(p)+(1-p)·log(1-p) = -h(p) for all x, giving h(p). -/
theorem bsc_conditional_output_entropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (inp : InputDist Bool) (hinp : ∀ b, 0 < inp.p b) :
    conditionalEntropy (transposeJoint (jointDist (bsc p (le_of_lt hp0) (le_of_lt hp1)) inp)) =
    BinaryEntropy.h p := by
  set ch := bsc p (le_of_lt hp0) (le_of_lt hp1) with hch_def
  unfold conditionalEntropy transposeJoint jointDist
  dsimp only
  -- After dsimp, the goal has the form:
  -- -(∑ a : Bool, ∑ b : Bool, if inp.p b * ch.W b a = 0 then 0
  --    else inp.p b * ch.W b a * log(inp.p b * ch.W b a / ∑ a', inp.p b * ch.W b a'))
  -- = h p
  --
  -- Here a ranges over the first type of the transposed distribution (output)
  -- and b ranges over the second type (input).
  -- All joint probabilities inp.p(b) * ch.W(b,a) are positive.
  have hne : ∀ (b a : Bool), inp.p b * ch.W b a ≠ 0 :=
    fun b a => ne_of_gt (mul_pos (hinp b) (bsc_W_pos hp0 hp1 b a))
  -- The denominator: ∑ a', inp.p(b) * ch.W(b, a') = inp.p(b)
  have hden : ∀ b : Bool, ∑ a' : Bool, inp.p b * ch.W b a' = inp.p b :=
    fun b => by rw [← Finset.mul_sum, ch.sum_one, mul_one]
  -- Rewrite each summand to remove if-then-else and simplify
  have hterm : ∀ (a b : Bool),
      (if inp.p b * ch.W b a = 0 then (0 : ℝ)
       else inp.p b * ch.W b a *
         Real.log (inp.p b * ch.W b a / (∑ a' : Bool, inp.p b * ch.W b a'))) =
      inp.p b * (ch.W b a * Real.log (ch.W b a)) := by
    intro a b
    rw [if_neg (hne b a), hden b, mul_div_cancel_left₀ _ (ne_of_gt (hinp b))]
    ring
  simp_rw [hterm]
  -- Swap sums: ∑ a ∑ b → ∑ b ∑ a
  rw [Finset.sum_comm]
  -- Factor out inp.p(b): ∑ b, ∑ a, inp.p(b) * (...) = ∑ b, inp.p(b) * ∑ a, (...)
  simp_rw [← Finset.mul_sum]
  -- Use BSC symmetry: ∑ a, ch.W(b,a) * log(ch.W(b,a)) is constant for all b
  simp_rw [bsc_output_entropy_per_input hp0 hp1]
  -- Factor: ∑ b, inp.p(b) * c = c * ∑ b, inp.p(b) = c * 1 = c
  rw [← Finset.sum_mul, inp.sum_one, one_mul]
  -- Goal: -(p * log p + (1-p) * log(1-p)) = h p
  simp only [BinaryEntropy.h]

/-! ## Shannon entropy of uniform distribution on Bool -/

/-- Shannon entropy of the uniform distribution on Bool equals log 2.
    Both outcomes have probability 1/2, so H = -2·(1/2)·log(1/2) = log 2. -/
theorem entropy_uniform_bool :
    shannonEntropy (fun (_ : Bool) => (1 : ℝ) / 2) = Real.log 2 := by
  unfold shannonEntropy
  simp only [Fintype.sum_bool]
  have hne : ¬((1 : ℝ) / 2 = 0) := by norm_num
  rw [if_neg hne, if_neg hne]
  -- Goal: -(1/2 * log(1/2) + 1/2 * log(1/2)) = log 2
  have h1 : (1 : ℝ) / 2 * Real.log (1 / 2) + 1 / 2 * Real.log (1 / 2) =
      Real.log (1 / 2) := by ring
  rw [h1, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ from by norm_num, Real.log_inv, neg_neg]

/-! ## MI computations for BSC -/

/-- MI for BSC + uniform input = log 2 - h(p).
    Achieves the capacity: uniform input maximizes mutual information for BSC. -/
theorem bsc_uniform_mi {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelMI (bsc p (le_of_lt hp0) (le_of_lt hp1)) uniformBool =
    Real.log 2 - BinaryEntropy.h p := by
  set ch := bsc p (le_of_lt hp0) (le_of_lt hp1) with hch_def
  unfold channelMI
  have hjoint_nn : ∀ xy, 0 ≤ jointDist ch uniformBool xy :=
    fun xy => le_of_lt (mul_pos (uniformBool_pos xy.1) (bsc_W_pos hp0 hp1 xy.1 xy.2))
  have hjoint_sum : ∑ xy : Bool × Bool, jointDist ch uniformBool xy = 1 :=
    jointDist_sum_one ch uniformBool
  -- MI = H(Y) - H(Y|X)
  rw [mi_eq_hY_sub_hYgivenX hjoint_nn hjoint_sum]
  -- H(Y|X) = h(p) for BSC
  rw [bsc_conditional_output_entropy hp0 hp1 uniformBool uniformBool_pos]
  -- Y-marginal for BSC + uniform is uniform: each y gets probability 1/2
  have hymarg : (fun y => ∑ x : Bool, jointDist ch uniformBool (x, y)) =
      fun _ => (1 : ℝ) / 2 := by
    ext y; exact bsc_uniform_ymarg (le_of_lt hp0) (le_of_lt hp1) y
  -- H(uniform on Bool) = log 2
  rw [hymarg, entropy_uniform_bool]

/-- MI for BSC ≤ log 2 - h(p) for any input distribution with positive weights.
    Uses H(Y) ≤ log|Bool| = log 2 and the chain rule MI = H(Y) - h(p). -/
theorem bsc_mi_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (inp : InputDist Bool) (hinp : ∀ b, 0 < inp.p b) :
    channelMI (bsc p (le_of_lt hp0) (le_of_lt hp1)) inp ≤
    Real.log 2 - BinaryEntropy.h p := by
  set ch := bsc p (le_of_lt hp0) (le_of_lt hp1)
  unfold channelMI
  have hjoint_nn : ∀ xy, 0 ≤ jointDist ch inp xy :=
    fun xy => le_of_lt (mul_pos (hinp xy.1) (bsc_W_pos hp0 hp1 xy.1 xy.2))
  have hjoint_sum := jointDist_sum_one ch inp
  -- MI = H(Y) - H(Y|X) = H(Y) - h(p)
  rw [mi_eq_hY_sub_hYgivenX hjoint_nn hjoint_sum,
      bsc_conditional_output_entropy hp0 hp1 inp hinp]
  -- Suffices: H(Y-marginal) ≤ log 2
  have hymarg_nn : ∀ y : Bool, 0 ≤ ∑ x : Bool, jointDist ch inp (x, y) :=
    fun y => Finset.sum_nonneg (fun x _ => hjoint_nn (x, y))
  have hymarg_sum : ∑ y : Bool, (∑ x : Bool, jointDist ch inp (x, y)) = 1 := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]; exact hjoint_sum
  have hle := entropy_le_log_card hymarg_nn hymarg_sum
  -- entropy_le_log_card gives ≤ log(Fintype.card Bool) = log 2
  simp only [Fintype.card_bool, Nat.cast_ofNat] at hle
  linarith

/-- MI for BSC ≤ log 2 - h(p) for ALL input distributions (including degenerate).
    When some input probability is 0 (point mass), MI = 0 ≤ log 2 - h(p). -/
theorem bsc_mi_le_general {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (inp : InputDist Bool) :
    channelMI (bsc p (le_of_lt hp0) (le_of_lt hp1)) inp ≤
    Real.log 2 - BinaryEntropy.h p := by
  by_cases h : ∀ b, 0 < inp.p b
  · exact bsc_mi_le hp0 hp1 inp h
  · -- Some input prob is 0 → input is point mass on Bool → H(X) = 0 → MI ≤ 0
    push_neg at h
    obtain ⟨b₀, hb₀⟩ := h
    have hb₀_eq : inp.p b₀ = 0 := le_antisymm (not_lt.mp hb₀) (inp.nonneg b₀)
    set ch := bsc p (le_of_lt hp0) (le_of_lt hp1)
    have hjoint_nn : ∀ xy, 0 ≤ jointDist ch inp xy :=
      fun xy => mul_nonneg (inp.nonneg xy.1) (ch.nonneg xy.1 xy.2)
    have hjoint_sum := jointDist_sum_one ch inp
    -- MI ≤ H(X) by chain rule: MI = H(X) - H(X|Y) and H(X|Y) ≥ 0
    have hMI_le_HX : mutualInformation (jointDist ch inp) ≤
        shannonEntropy (fun x => ∑ y : Bool, jointDist ch inp (x, y)) := by
      have hchain := chain_rule hjoint_nn hjoint_sum
      have hcond := conditionalEntropy_nonneg hjoint_nn hjoint_sum
      linarith
    -- X-marginal = inp.p
    have hxmarg : (fun x => ∑ y : Bool, jointDist ch inp (x, y)) = inp.p := by
      ext x; exact channel_xmarg ch inp x
    rw [hxmarg] at hMI_le_HX
    -- H(inp.p) = 0 since inp.p is a point mass at !b₀
    have hpoint : ∀ x : Bool, x ≠ !b₀ → inp.p x = 0 := by
      intro x hx; cases b₀ <;> cases x <;> simp_all
    have hent_zero : shannonEntropy inp.p = 0 :=
      entropy_point_mass inp.nonneg inp.sum_one hpoint
    rw [hent_zero] at hMI_le_HX
    -- MI ≤ 0 ≤ log 2 - h(p)
    unfold channelMI
    linarith [BinaryEntropy.h_le_log_two (le_of_lt hp0) (le_of_lt hp1)]

/-! ## BSC capacity theorem -/

/-- **BSC capacity = log 2 - h(p).**
    This proves the parent file's `bsc_capacity_eq` axiom from first principles.

    Upper bound: For all input distributions, MI(X;Y) ≤ log 2 - h(p).
    Achievability: The uniform input distribution achieves MI = log 2 - h(p).
    Therefore the supremum (channel capacity) equals log 2 - h(p). -/
theorem bsc_capacity_proved {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (bsc p (le_of_lt hp0) (le_of_lt hp1)) =
    Real.log 2 - BinaryEntropy.h p := by
  unfold channelCapacity
  apply le_antisymm
  · -- Upper bound: sSup ≤ log 2 - h(p)
    apply csSup_le
    · exact ⟨_, uniformBool, rfl⟩
    · intro r ⟨inp, hr⟩; rw [← hr]; exact bsc_mi_le_general hp0 hp1 inp
  · -- Lower bound: log 2 - h(p) ≤ sSup (achieved by uniform)
    apply le_csSup
    · exact ⟨Real.log (Fintype.card Bool), fun _ ⟨inp, hr⟩ =>
        hr ▸ channelMI_le_log_card _ _⟩
    · exact ⟨uniformBool, bsc_uniform_mi hp0 hp1⟩

/-! ## Random coding existence lemma -/

/-- **Random coding existence (probabilistic method).**
    If the average value of a function over a finite nonempty index set is at most ε,
    then some specific index achieves a value ≤ ε.

    This is the core non-constructive step in Shannon's achievability proof:
    pick codewords independently from the capacity-achieving distribution,
    show the expected error is small by the joint AEP, then conclude a
    good deterministic code exists by this lemma. -/
theorem random_coding_existence {ι : Type*} [Fintype ι] [Nonempty ι]
    (error : ι → ℝ) {ε : ℝ} (hε : 0 < ε)
    (avg_bound : (∑ i : ι, error i) / Fintype.card ι ≤ ε) :
    ∃ i : ι, error i ≤ ε := by
  by_contra h
  push_neg at h
  have hcard_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have : ε * Fintype.card ι < ∑ i : ι, error i :=
    calc ε * Fintype.card ι
        = ∑ _ : ι, ε := by rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
      _ < ∑ i : ι, error i :=
        Finset.sum_lt_sum (fun i _ => le_of_lt (h i))
          ⟨Classical.arbitrary ι, Finset.mem_univ _, h _⟩
  linarith [div_le_iff hcard_pos |>.mpr (le_of_lt this)]

end InformationTheory.ChannelCoding.BSCCapacity
