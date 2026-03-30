/-
  Shannon Noisy Channel Coding Theorem

  Reliable communication is possible at any rate below channel capacity
  C = max_{p(x)} I(X;Y). The central result of information theory.

  Achievability via random coding; converse via Fano's inequality.

  Claude Shannon (1948)

  Axioms: 4 (fano_inequality, channel_coding_achievability,
    channel_coding_converse, bsc_capacity_eq)
  Theorems: 8 (jointDist_nonneg, jointDist_sum_one, channelMI_nonneg,
    channelMI_le_log_card, capacity_nonneg, rate_of_code_pos,
    bsc_capacity_le_one, bsc_capacity_nonneg)
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonEntropy

open Real Finset InformationTheory

namespace InformationTheory.ChannelCoding

/- ## Discrete Memoryless Channel -/

/-- A discrete memoryless channel is specified by a transition matrix
    W : α → β → ℝ where W x y = P(Y = y | X = x).
    Valid channels have non-negative probabilities summing to 1
    for each input. -/
structure DMChannel (α β : Type*) [Fintype α] [Fintype β] where
  W : α → β → ℝ
  nonneg : ∀ x y, 0 ≤ W x y
  sum_one : ∀ x, ∑ y, W x y = 1

/-- A valid input distribution for a channel. -/
structure InputDist (α : Type*) [Fintype α] where
  p : α → ℝ
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x, p x = 1

/-- The joint distribution induced by input distribution p and channel W:
    P(X=x, Y=y) = p(x) · W(x, y). -/
noncomputable def jointDist {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) (inp : InputDist α) : α × β → ℝ :=
  fun ⟨x, y⟩ => inp.p x * ch.W x y

/-- Mutual information for an input distribution and channel:
    I(X;Y) = I(p, W) computed from the joint distribution p(x)·W(x|y). -/
noncomputable def channelMI {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) (inp : InputDist α) : ℝ :=
  mutualInformation (jointDist ch inp)

/-- Channel capacity: C = sup over input distributions of I(X;Y).
    For finite alphabets, the supremum is achieved (compactness). -/
noncomputable def channelCapacity {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) : ℝ :=
  sSup { r : ℝ | ∃ inp : InputDist α, channelMI ch inp = r }

/- ## Joint distribution properties -/

/-- Joint distribution is non-negative. -/
theorem jointDist_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) (inp : InputDist α) (xy : α × β) :
    0 ≤ jointDist ch inp xy :=
  mul_nonneg (inp.nonneg xy.1) (ch.nonneg xy.1 xy.2)

/-- Joint distribution sums to 1. -/
theorem jointDist_sum_one {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) (inp : InputDist α) :
    ∑ xy : α × β, jointDist ch inp xy = 1 := by
  simp only [jointDist, Fintype.sum_prod_type]
  conv_lhs => arg 2; ext x; rw [← Finset.mul_sum]
  rw [show ∀ x, ∑ y : β, ch.W x y = 1 from fun x => ch.sum_one x]
  simp [inp.sum_one]

/-- Channel mutual information is non-negative. -/
theorem channelMI_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) (inp : InputDist α) : 0 ≤ channelMI ch inp :=
  mutual_info_nonneg (jointDist_nonneg ch inp) (jointDist_sum_one ch inp)

/- ## Channel capacity is non-negative -/

/-- Mutual information is bounded by log of the output alphabet size.
    I(X;Y) ≤ H(Y) ≤ log|β|. Proof uses chain rule and entropy_le_log_card. -/
theorem channelMI_le_log_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) (inp : InputDist α) :
    channelMI ch inp ≤ Real.log (Fintype.card β) := by
  -- channelMI ch inp = mutualInformation (jointDist ch inp)
  unfold channelMI
  -- I(X;Y) ≤ H(Y) ≤ log|β|
  calc mutualInformation (jointDist ch inp)
      ≤ shannonEntropy (fun y => ∑ x : α, jointDist ch inp (x, y)) :=
        mutual_info_le_entropy_snd (jointDist_nonneg ch inp) (jointDist_sum_one ch inp)
    _ ≤ Real.log (Fintype.card β) := by
        -- The Y-marginal sums to 1
        have hmarg_sum : ∑ y : β, (∑ x : α, jointDist ch inp (x, y)) = 1 := by
          rw [Finset.sum_comm, ← Fintype.sum_prod_type]
          exact jointDist_sum_one ch inp
        have hmarg_nn : ∀ y : β, 0 ≤ ∑ x : α, jointDist ch inp (x, y) :=
          fun y => Finset.sum_nonneg (fun x _ => jointDist_nonneg ch inp (x, y))
        exact entropy_le_log_card hmarg_nn hmarg_sum

/-- Channel capacity is non-negative: I(X;Y) ≥ 0 for all input distributions,
    and the supremum over a non-empty set of non-negatives is non-negative. -/
theorem capacity_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (ch : DMChannel α β) : 0 ≤ channelCapacity ch := by
  unfold channelCapacity
  have ⟨a⟩ := ‹Nonempty α›
  let inp₀ : InputDist α :=
    { p := fun x => if x = a then 1 else 0
      nonneg := fun x => by split_ifs <;> norm_num
      sum_one := by simp [Finset.sum_ite_eq', Finset.mem_univ] }
  apply le_csSup_of_le
  · exact ⟨Real.log (Fintype.card β), fun _ ⟨inp, hr⟩ =>
      hr ▸ channelMI_le_log_card ch inp⟩
  · exact ⟨inp₀, rfl⟩
  · exact channelMI_nonneg ch inp₀

/- ## Block codes -/

/-- A block code of length n with M codewords over alphabet α. -/
structure BlockCode (α : Type*) (n : ℕ) where
  M : ℕ
  hM : 0 < M
  encode : Fin M → Fin n → α

/-- The rate of a block code: R = log(M) / n (in nats). -/
noncomputable def rate_of_code {α : Type*} {n : ℕ} (hn : 0 < n)
    (code : BlockCode α n) : ℝ :=
  Real.log code.M / n

/-- Code rate is non-negative when M ≥ 1 and n ≥ 1. -/
theorem rate_of_code_pos {α : Type*} {n : ℕ} (hn : 0 < n)
    (code : BlockCode α n) : 0 ≤ rate_of_code hn code := by
  unfold rate_of_code
  apply div_nonneg
  · exact Real.log_nonneg (by exact_mod_cast code.hM)
  · exact Nat.cast_nonneg n

/- ## Fano's inequality -/

/-- **Fano's inequality**: H(X|Y) ≤ h(P_e) + P_e · log(|X| - 1)
    where h is binary entropy and P_e is the error probability.

    This bounds conditional entropy in terms of error probability,
    and is the key tool for the converse of the channel coding theorem. -/
axiom fano_inequality {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let pX : α → ℝ := fun x => ∑ y : β, pXY (x, y)
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    conditionalEntropy pXY ≤
      InformationTheory.BinaryEntropy.h P_e +
        P_e * Real.log (Fintype.card α - 1)

/- ## Main theorems -/

/-- **Channel coding theorem (achievability).**
    For any rate R below channel capacity, there exist block codes of
    rate R with error probability vanishing as block length → ∞.

    Shannon's proof uses random coding: a random codebook achieves the bound
    in expectation, hence a good deterministic code exists. -/
axiom channel_coding_achievability {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) {R : ℝ} (hR : 0 < R)
    (hR_cap : R < channelCapacity ch) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in Filter.atTop,
      ∃ (code : BlockCode α n) (decoder : (Fin n → β) → Fin code.M),
        R ≤ rate_of_code (by omega : 0 < n) code ∧
        -- Average error probability < ε
        (∑ i : Fin code.M, (1 - ∑ y : Fin n → β,
          (∏ j : Fin n, ch.W (code.encode i j) (y j)) *
            if decoder y = i then (1 : ℝ) else 0)) / code.M < ε

/-- **Channel coding theorem (converse).**
    For any rate R above channel capacity, the error probability
    is bounded away from 0 for all sufficiently long codes.

    Proof via Fano's inequality: if the error probability is small,
    then I(X;Y) ≈ R per channel use, but I(X;Y) ≤ C. -/
axiom channel_coding_converse {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) {R : ℝ} (hR : 0 < R)
    (hR_cap : channelCapacity ch < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (hn : 0 < n)
      (code : BlockCode α n) (decoder : (Fin n → β) → Fin code.M),
        R ≤ rate_of_code hn code →
        δ ≤ (∑ i : Fin code.M, (1 - ∑ y : Fin n → β,
          (∏ j : Fin n, ch.W (code.encode i j) (y j)) *
            if decoder y = i then (1 : ℝ) else 0)) / code.M

/- ## Binary symmetric channel -/

/-- The binary symmetric channel BSC(p): flips each bit independently
    with probability p. Requires 0 ≤ p ≤ 1. -/
noncomputable def bsc (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : DMChannel Bool Bool where
  W := fun x y => if x = y then 1 - p else p
  nonneg := fun x y => by split_ifs <;> linarith
  sum_one := fun x => by
    simp only [Fintype.sum_bool]
    split_ifs with h <;> ring

/-- BSC capacity = 1 - h(p) bits = log 2 - h(p) nats.
    The capacity-achieving input is uniform Bernoulli(1/2). -/
axiom bsc_capacity_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (bsc p (le_of_lt hp0) (le_of_lt hp1)) =
      Real.log 2 - InformationTheory.BinaryEntropy.h p

/-- BSC capacity is at most log 2 (= 1 bit). -/
theorem bsc_capacity_le_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (bsc p (le_of_lt hp0) (le_of_lt hp1)) ≤ Real.log 2 := by
  rw [bsc_capacity_eq hp0 hp1]
  linarith [InformationTheory.BinaryEntropy.h_nonneg (le_of_lt hp0) (le_of_lt hp1)]

/-- BSC capacity is non-negative for 0 < p < 1. -/
theorem bsc_capacity_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ channelCapacity (bsc p (le_of_lt hp0) (le_of_lt hp1)) := by
  rw [bsc_capacity_eq hp0 hp1]
  linarith [InformationTheory.BinaryEntropy.h_le_log_two (le_of_lt hp0) (le_of_lt hp1)]

end InformationTheory.ChannelCoding
