/-
  Shannon Noisy Channel Coding Theorem

  Reliable communication is possible at any rate below channel capacity
  C = max_{p(x)} I(X;Y). The central result of information theory.

  Achievability via random coding; converse via Fano's inequality.

  Claude Shannon (1948)

  Axioms: 3 (channel_coding_achievability, channel_coding_converse,
    bsc_capacity_eq)
  Theorems: 13 (jointDist_nonneg, jointDist_sum_one, channelMI_nonneg,
    channelMI_le_log_card, capacity_nonneg, channelMI_le_capacity,
    capacity_le_log_card, rate_of_code_pos, fano_inequality,
    fano_converse_step, fano_converse_capacity,
    bsc_capacity_le_one, bsc_capacity_nonneg)
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonEntropy
import Proofs.ShannonChannelCodingOQ02OQ01

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
  simp only [jointDist, Fintype.sum_prod_type, ← Finset.mul_sum, ch.sum_one, mul_one]
  exact inp.sum_one

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

/-- **Single-letter capacity upper bound.** For every input distribution `inp`,
    the mutual information `I(X;Y)` is bounded by the channel capacity.

    This is the immediate consequence of `channelCapacity` being defined as a
    supremum over input distributions: any particular `inp` sits below the sup.
    `BddAbove` is witnessed by `log |β|` via `channelMI_le_log_card`.

    This lemma is the single-letter ingredient used in the converse direction
    of the channel coding theorem (Fano's inequality + this bound rearrange
    into `(1 - P_e) log M ≤ I(X;Y) + h(P_e) ≤ C + h(P_e)`). -/
theorem channelMI_le_capacity {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) (inp : InputDist α) :
    channelMI ch inp ≤ channelCapacity ch := by
  unfold channelCapacity
  apply le_csSup
  · exact ⟨Real.log (Fintype.card β), fun _ ⟨inp', hr⟩ =>
      hr ▸ channelMI_le_log_card ch inp'⟩
  · exact ⟨inp, rfl⟩

/-- **Capacity upper bound by output alphabet.** Channel capacity is at most
    `log |β|`. Combined with `capacity_nonneg`, this localises the capacity
    of every DMChannel `α → β` to `[0, log |β|]`.

    Immediate from `channelMI_le_log_card` and the supremum definition of
    `channelCapacity`. Used downstream in the bsc analysis to bound the
    capacity-achieving rate `1 - h(p)` from above. -/
theorem capacity_le_log_card {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (ch : DMChannel α β) :
    channelCapacity ch ≤ Real.log (Fintype.card β) := by
  unfold channelCapacity
  have ⟨a⟩ := ‹Nonempty α›
  let inp₀ : InputDist α :=
    { p := fun x => if x = a then 1 else 0
      nonneg := fun x => by split_ifs <;> norm_num
      sum_one := by simp [Finset.sum_ite_eq', Finset.mem_univ] }
  apply csSup_le
  · exact ⟨channelMI ch inp₀, inp₀, rfl⟩
  · rintro r ⟨inp, rfl⟩
    exact channelMI_le_log_card ch inp

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
    and is the key tool for the converse of the channel coding theorem.

    Discharged via `FanoFromConditionalEntropy.fano_inequality_proved` in
    `Proofs.ShannonChannelCodingOQ02OQ01`. -/
theorem fano_inequality {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let pX : α → ℝ := fun x => ∑ y : β, pXY (x, y)
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    conditionalEntropy pXY ≤
      InformationTheory.BinaryEntropy.h P_e +
        P_e * Real.log (Fintype.card α - 1) :=
  FanoFromConditionalEntropy.fano_inequality_proved pXY hp hsum

/-- **Fano-form converse intermediate identity** (single-letter form).

    For any joint distribution `pXY : α × β → ℝ` whose X-marginal achieves the
    maximum-entropy bound `H(X) = log |α|` (i.e., X is uniform on α),

    `log |α| ≤ I(X;Y) + h(P_e) + P_e · log(|α| - 1)`

    where `P_e := 1 - ∑ y, ∑ x, pXY(x,y)² / pY(y)` is the Fano error term.

    Equivalently, `log |α| - h(P_e) - P_e · log(|α| - 1) ≤ I(X;Y)`. Combined
    with `channelMI_le_capacity` (which gives `I(X;Y) ≤ channelCapacity ch`),
    this yields the canonical single-letter converse
    `(1 − P_e) · log |α| ≤ channelCapacity ch + h(P_e)` (after rearranging
    `P_e · log(|α| / (|α| − 1)) ≥ 0` for `|α| ≥ 2`).

    The proof is a single `linarith` step on:
    * `chain_rule pXY`  — `I(X;Y) = H(X-marginal) − H(X|Y)`
    * `h_uniform`       — `H(X-marginal) = log |α|`  (hypothesis)
    * `fano_inequality pXY` — `H(X|Y) ≤ h(P_e) + P_e · log(|α| - 1)`

    The `h_uniform` hypothesis is satisfied for uniform X via
    `entropy_of_uniform_eq_log_card` (in `ShannonEntropy.lean`); stating it
    abstractly here keeps the lemma applicable to any X-marginal achieving
    the max-entropy bound, and avoids importing additional uniform-distribution
    plumbing into this file. -/
theorem fano_converse_step {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1)
    (h_uniform : shannonEntropy (fun x : α => ∑ y : β, pXY (x, y)) =
                 Real.log (Fintype.card α)) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    Real.log (Fintype.card α) ≤
      mutualInformation pXY +
      InformationTheory.BinaryEntropy.h P_e +
      P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  intro P_e
  -- I(X;Y) = H(X) - H(X|Y); with h_uniform: H(X) = log |α|,
  -- this gives mutualInformation pXY = log |α| - conditionalEntropy pXY.
  have hchain : mutualInformation pXY =
      shannonEntropy (fun x : α => ∑ y : β, pXY (x, y)) -
        conditionalEntropy pXY := chain_rule hp hsum
  rw [h_uniform] at hchain
  -- Fano: H(X|Y) ≤ h(P_e) + P_e · log(|α| - 1).
  have hfano := fano_inequality pXY hp hsum
  -- Combine algebraically.
  linarith

/-- **Fano-form converse single-letter bound with channel capacity.**

    For a channel `ch : DMChannel α β` and a uniform input distribution
    `inp : InputDist α` (i.e., `inp.p ≡ (Fintype.card α)⁻¹`),

    `log |α| ≤ channelCapacity ch + h(P_e) + P_e · log(|α| - 1)`

    where `P_e` is the Fano error term for the joint distribution
    `jointDist ch inp`.

    This is the canonical "uniform-input single-letter converse": for
    the worst-case (uniform) codebook over `|α|` codewords, the
    log-cardinality is bounded by `channelCapacity ch` plus the Fano
    error penalty. Rearranges to `(1 - P_e) · log |α| ≤
    channelCapacity ch + h(P_e)` once one absorbs the always-nonneg
    correction `P_e · log(|α| / (|α| - 1)) ≥ 0` (for `|α| ≥ 2`); the
    bare form stated here is the single-letter ingredient that block-
    coding arguments invoke at each channel use of an `n`-block code.

    The proof combines three ingredients:
    * `fano_converse_step` (this file) — the abstract single-letter
      identity under explicit uniform-entropy hypothesis;
    * `entropy_of_uniform_eq_log_card` (`ShannonEntropy.lean`) —
      discharges the uniform-entropy hypothesis;
    * `channelMI_le_capacity` (this file, line 137) — replaces
      `mutualInformation (jointDist ch inp)` with `channelCapacity ch`.

    The X-marginal of `jointDist ch inp` is `inp.p`, since each row
    `∑ y, ch.W x y = 1` (channel rows are probability distributions);
    this is the bridge that lets `entropy_of_uniform_eq_log_card`
    apply to the joint-distribution marginal. -/
theorem fano_converse_capacity {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (ch : DMChannel α β) (inp : InputDist α)
    (h_inp_uniform : ∀ x : α, inp.p x = (Fintype.card α : ℝ)⁻¹) :
    let P_e := 1 - ∑ y : β, ∑ x : α,
                 jointDist ch inp (x, y) ^ 2 /
                   (∑ x' : α, jointDist ch inp (x', y))
    Real.log (Fintype.card α) ≤
      channelCapacity ch +
      InformationTheory.BinaryEntropy.h P_e +
      P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  intro P_e
  -- The X-marginal of `jointDist ch inp` equals `inp.p`,
  -- since `∑ y, ch.W x y = 1` (channel rows are probability distributions).
  have h_marg : (fun x : α => ∑ y : β, jointDist ch inp (x, y)) = inp.p := by
    funext x
    show ∑ y : β, inp.p x * ch.W x y = inp.p x
    rw [← Finset.mul_sum, ch.sum_one, mul_one]
  -- The hypothesis `h_inp_uniform` says `inp.p` is the uniform constant.
  have h_inp_eq : inp.p = fun _ : α => (Fintype.card α : ℝ)⁻¹ := funext h_inp_uniform
  -- Discharge the `h_uniform` hypothesis of `fano_converse_step` using
  -- `entropy_of_uniform_eq_log_card` (in `ShannonEntropy.lean`).
  have h_uniform :
      shannonEntropy (fun x : α => ∑ y : β, jointDist ch inp (x, y)) =
        Real.log (Fintype.card α) := by
    rw [h_marg, h_inp_eq]
    exact entropy_of_uniform_eq_log_card
  -- Apply `fano_converse_step` to the joint distribution.
  have hfano_step :=
    fano_converse_step (jointDist ch inp)
      (jointDist_nonneg ch inp) (jointDist_sum_one ch inp) h_uniform
  -- `mutualInformation (jointDist ch inp) = channelMI ch inp` by definition.
  have hcap : mutualInformation (jointDist ch inp) ≤ channelCapacity ch := by
    show channelMI ch inp ≤ channelCapacity ch
    exact channelMI_le_capacity ch inp
  -- Combine the two bounds.
  linarith

/-- **Shannon-form converse (S7, this iteration).**
    For any DM channel `ch` with input alphabet of size `≥ 2` and any uniform
    input distribution `inp`, the rate is bounded by capacity plus the binary
    entropy of the error probability:

    `(1 - P_e) · log |α| ≤ channelCapacity ch + h(P_e)`

    where `P_e` is the Fano error term from `fano_converse_capacity`. This is
    the canonical "Shannon-form" converse bound that appears in standard
    information-theory textbooks (Cover-Thomas §7.9 eq. 7.150, MacKay §10.4).

    The proof is a one-step rearrangement of `fano_converse_capacity`:
    absorb the always-nonneg slack `P_e · log(|α| - 1) ≤ P_e · log |α|`
    (using `log_le_log` on `|α| - 1 ≤ |α|` for `|α| ≥ 2`), then rearrange
    `log |α| ≤ C + h(P_e) + P_e · log |α|` into the displayed form.

    Downstream this is the cleanest entry-point for asymptotic
    block-coding converse arguments: combined with the per-letter
    chain-rule `I(X^n; Y^n) ≤ n · C`, the standard rearrangement gives
    `P_e ≥ 1 - C / log|α| - 1 / log|α|` for any rate-`R` block code
    with `R > C`. -/
theorem fano_converse_shannon_form {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (ch : DMChannel α β) (inp : InputDist α)
    (h_inp_uniform : ∀ x : α, inp.p x = (Fintype.card α : ℝ)⁻¹)
    (h_card : 2 ≤ Fintype.card α) :
    let P_e := 1 - ∑ y : β, ∑ x : α,
                 jointDist ch inp (x, y) ^ 2 /
                   (∑ x' : α, jointDist ch inp (x', y))
    0 ≤ P_e →
    (1 - P_e) * Real.log (Fintype.card α) ≤
      channelCapacity ch + InformationTheory.BinaryEntropy.h P_e := by
  intro P_e h_pe_nn
  -- Bring in the S6 bound `log |α| ≤ C + h(P_e) + P_e · log(|α| - 1)`.
  have hS6 := fano_converse_capacity ch inp h_inp_uniform
  -- Absorb the `log(|α| - 1) ≤ log |α|` slack.
  have h_card_real : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast h_card
  have h_card_pos : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by linarith
  have h_sub_le : (Fintype.card α : ℝ) - 1 ≤ (Fintype.card α : ℝ) := by linarith
  have hlog_le : Real.log ((Fintype.card α : ℝ) - 1) ≤ Real.log (Fintype.card α) :=
    Real.log_le_log h_card_pos h_sub_le
  have h_pe_log :
      P_e * Real.log ((Fintype.card α : ℝ) - 1) ≤
        P_e * Real.log (Fintype.card α) :=
    mul_le_mul_of_nonneg_left hlog_le h_pe_nn
  -- Rearrange `log |α| ≤ C + h(P_e) + P_e · log |α|` into the displayed form.
  nlinarith [hS6, h_pe_log]

/-- **Fano-form marginal-entropy converse (S10, this iteration).**

    Generalisation of `fano_converse_step` to arbitrary (not necessarily
    uniform) X-marginals. For any joint distribution `pXY : α × β → ℝ`,

    `H(p_X) ≤ I(X;Y) + h(P_e) + P_e · log(|α| - 1)`

    where `p_X x := ∑ y, pXY (x, y)` is the X-marginal and `P_e` is the
    Fano error term. The proof drops the `h_uniform` hypothesis from
    `fano_converse_step`: instead of rewriting `H(p_X) ↦ log |α|`, the
    chain rule's `H(p_X)` term is carried through directly.

    Specialising via `entropy_of_uniform_eq_log_card` recovers
    `fano_converse_step` when the X-marginal is uniform. Combined with
    `entropy_lt_log_card_iff_non_uniform` (S9), it gives a strict-slack
    interpretation: for any non-uniform X-marginal, `H(p_X) < log |α|`,
    so this LHS is strictly below the (uniform-input) `log |α|` LHS of
    `fano_converse_step` — quantifying the entropy gap as a lower bound
    on the slack in the single-letter converse. -/
theorem fano_converse_step_marginal {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    shannonEntropy (fun x : α => ∑ y : β, pXY (x, y)) ≤
      mutualInformation pXY +
      InformationTheory.BinaryEntropy.h P_e +
      P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  intro P_e
  -- I(X;Y) = H(X-marginal) - H(X|Y); no uniform hypothesis, so H(X-marginal) stays.
  have hchain : mutualInformation pXY =
      shannonEntropy (fun x : α => ∑ y : β, pXY (x, y)) -
        conditionalEntropy pXY := chain_rule hp hsum
  -- Fano: H(X|Y) ≤ h(P_e) + P_e · log(|α| - 1).
  have hfano := fano_inequality pXY hp hsum
  -- Combine algebraically.
  linarith

/-- **Marginal-entropy single-letter converse with channel capacity (S10).**

    For a channel `ch : DMChannel α β` and any input distribution `inp`,

    `H(inp.p) ≤ channelCapacity ch + h(P_e) + P_e · log(|α| - 1)`

    where `P_e` is the Fano error term for `jointDist ch inp`. This is
    the non-uniform-input generalisation of `fano_converse_capacity`:
    `log |α|` on the LHS is replaced by the actual input marginal
    entropy `H(inp.p)`. Both sides reduce to `fano_converse_capacity`
    when `inp` is uniform, via `entropy_of_uniform_eq_log_card`.

    The proof composes `fano_converse_step_marginal` (this file,
    abstract joint-distribution form) with `channelMI_le_capacity` (this
    file, line 138), using the X-marginal identity
    `(fun x => ∑ y, jointDist ch inp (x, y)) = inp.p` — which follows
    from `∑ y, ch.W x y = 1` (channel rows are probability
    distributions).

    Quantitatively, by S9 (`entropy_lt_log_card_iff_non_uniform`),
    `H(inp.p) < log |α|` whenever `inp.p` is non-uniform; the gap
    `log |α| - H(inp.p) > 0` is the strict slack between this
    non-uniform-input bound and the worst-case uniform-input bound
    `fano_converse_capacity`. -/
theorem fano_converse_marginal {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (ch : DMChannel α β) (inp : InputDist α) :
    let P_e := 1 - ∑ y : β, ∑ x : α,
                 jointDist ch inp (x, y) ^ 2 /
                   (∑ x' : α, jointDist ch inp (x', y))
    shannonEntropy inp.p ≤
      channelCapacity ch +
      InformationTheory.BinaryEntropy.h P_e +
      P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  intro P_e
  -- The X-marginal of `jointDist ch inp` equals `inp.p`,
  -- since `∑ y, ch.W x y = 1` (channel rows are probability distributions).
  have h_marg : (fun x : α => ∑ y : β, jointDist ch inp (x, y)) = inp.p := by
    funext x
    show ∑ y : β, inp.p x * ch.W x y = inp.p x
    rw [← Finset.mul_sum, ch.sum_one, mul_one]
  -- Apply the abstract marginal-form converse step to the joint distribution.
  have hstep := fano_converse_step_marginal (jointDist ch inp)
    (jointDist_nonneg ch inp) (jointDist_sum_one ch inp)
  rw [h_marg] at hstep
  -- Replace mutualInformation with channelCapacity via channelMI_le_capacity.
  have hcap : mutualInformation (jointDist ch inp) ≤ channelCapacity ch := by
    show channelMI ch inp ≤ channelCapacity ch
    exact channelMI_le_capacity ch inp
  -- Combine the two bounds.
  linarith

/- ## Capacity-achieving inputs for weakly symmetric channels (S18 ACT, scoped) -/

/-- A DMChannel is **weakly symmetric** iff every pair of rows of `W` are
    related by a permutation of the output alphabet, AND each column of `W`
    sums to the same constant.

    This is the Cover-Thomas (Elements of Information Theory, §7.2)
    definition. It is the minimal property needed for the forward
    direction "uniform input achieves capacity"; the substantive proof
    `uniform_input_achieves_capacity_of_weakly_symmetric` is deferred
    to S18c (see research/problems/shannon-channel-coding-oq-02-oq-01-oq-01/
    sessions/2026-05-16-s17-prep-symmetric-channel-audit.md §6.2).

    The first conjunct (row permutation) implies the row entropy
    `H(W(·|x))` is independent of `x` (S18b lemma).
    The second conjunct (column constancy) implies that uniform input
    yields uniform output marginal (S18a-2 lemma).
    Together they give `I(X;Y) = log|β| − H_row` achieved by uniform input. -/
def DMChannel.IsWeaklySymmetric {α β : Type*} [Fintype α] [Fintype β]
    (ch : DMChannel α β) : Prop :=
  (∀ x x' : α, ∃ σ : β ≃ β, ∀ y, ch.W x y = ch.W x' (σ y)) ∧
  (∀ y y' : β, ∑ x : α, ch.W x y = ∑ x : α, ch.W x y')

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
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (hn : 0 < n),
      ∃ (code : BlockCode α n) (decoder : (Fin n → β) → Fin code.M),
        R ≤ rate_of_code hn code ∧
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
  sum_one := fun x => by cases x <;> simp

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
