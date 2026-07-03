/-
  Binary Erasure Channel (BEC) Capacity

  Open Question 01: concrete channel capacities beyond placeholders.
  The BSC capacity = log 2 - h(p) is already proven in
  ShannonChannelCodingOQ02 (`bsc_capacity_proved`, 0 axioms). The remaining
  open item is the binary erasure channel.

  Main result: BEC(p) capacity = (1 - p) · log 2, proven from first principles
  (0 axioms, 0 sorries).

  The binary erasure channel BEC(p) has input `Bool` and output `Option Bool`,
  where `none` denotes an erasure. Each transmitted bit is erased with
  probability `p` and received correctly with probability `1 - p`:

      W x (some y) = if x = y then 1 - p else 0
      W x none     = p

  Capacity proof (clean single identity):
  1. For ANY input distribution, the conditional entropy of the input given the
     output is `H(X|Y) = p · H(X)` (BEC erases with probability `p`; when not
     erased the input is determined exactly).
  2. By the chain rule `I(X;Y) = H(X) - H(X|Y) = (1 - p) · H(X)`.
  3. Converse: `H(X) ≤ log|Bool| = log 2`, so `I(X;Y) ≤ (1 - p) · log 2`.
  4. Achievability: the uniform Bernoulli(1/2) input gives `H(X) = log 2`.
  5. Capacity = sSup over inputs = `(1 - p) · log 2`.

  Unlike the BSC, the BEC is not weakly symmetric (its erasure column sums to
  `2p`, the others to `1 - p`), so the symmetric-channel machinery does not
  apply; the `H(X|Y) = p·H(X)` identity is the right engine instead.

  Claude Shannon (1948)

  Axioms: 0
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonChannelCoding
import Proofs.ShannonChannelCodingOQ02
import Proofs.ShannonChannelCodingOQ04

open Real Finset InformationTheory InformationTheory.ChannelCoding
open InformationTheory.BinaryEntropy

namespace InformationTheory.ChannelCoding.BEC

/-! ## The binary erasure channel -/

/-- The binary erasure channel `BEC(p)`: input `Bool`, output `Option Bool`
    (`none` = erasure). Each bit is erased with probability `p` and otherwise
    received correctly. Requires `0 ≤ p ≤ 1`. -/
noncomputable def bec (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    DMChannel Bool (Option Bool) where
  W := fun x o =>
    match o with
    | none => p
    | some y => if x = y then 1 - p else 0
  nonneg := fun x o => by
    cases o with
    | none => exact hp0
    | some y => dsimp only; split_ifs <;> linarith
  sum_one := fun x => by
    rw [Fintype.sum_option, Fintype.sum_bool]
    cases x <;> simp

@[simp] lemma bec_W_none {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : Bool) :
    (bec p hp0 hp1).W x none = p := rfl

@[simp] lemma bec_W_some {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : Bool) :
    (bec p hp0 hp1).W x (some y) = if x = y then 1 - p else 0 := rfl

/-! ## Output marginals -/

/-- The `none` (erasure) output marginal equals `p` regardless of the input
    distribution: every input symbol is erased with probability `p`. -/
lemma bec_ymarg_none {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (inp : InputDist Bool) :
    (∑ x' : Bool, jointDist (bec p hp0 hp1) inp (x', none)) = p := by
  simp only [jointDist, bec_W_none]
  rw [← Finset.sum_mul, inp.sum_one, one_mul]

/-- The `some y` output marginal equals `inp.p y · (1 - p)`: the symbol `y` is
    received un-erased only when `y` was sent (probability `inp.p y`) and not
    erased (probability `1 - p`). -/
lemma bec_ymarg_some {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (inp : InputDist Bool)
    (y : Bool) :
    (∑ x' : Bool, jointDist (bec p hp0 hp1) inp (x', some y)) = inp.p y * (1 - p) := by
  simp only [jointDist, bec_W_some]
  rw [Fintype.sum_bool]
  cases y <;> simp

/-! ## Conditional entropy `H(X|Y) = p · H(X)` -/

/-- **The BEC erasure identity.** For any input distribution, the entropy of the
    input given the output is `H(X|Y) = p · H(X)`.

    Intuition: with probability `1 - p` the output is the un-erased symbol, which
    determines the input exactly (zero residual entropy); with probability `p`
    the output is an erasure, leaving the full input entropy `H(X)`. -/
theorem bec_conditional_entropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (inp : InputDist Bool) :
    conditionalEntropy (jointDist (bec p hp0.le hp1.le) inp)
      = p * shannonEntropy inp.p := by
  -- Each `some y` summand vanishes: when `x ≠ y` the joint prob is 0;
  -- when `x = y` the conditional probability is 1 (log 1 = 0).
  have hsome_zero : ∀ (x y : Bool),
      (if jointDist (bec p hp0.le hp1.le) inp (x, some y) = 0 then (0 : ℝ)
       else jointDist (bec p hp0.le hp1.le) inp (x, some y) *
         Real.log (jointDist (bec p hp0.le hp1.le) inp (x, some y) /
           (∑ x' : Bool, jointDist (bec p hp0.le hp1.le) inp (x', some y)))) = 0 := by
    intro x y
    rw [bec_ymarg_some hp0.le hp1.le inp y]
    by_cases hxy : x = y
    · subst hxy
      have hJ : jointDist (bec p hp0.le hp1.le) inp (x, some x) = inp.p x * (1 - p) := by
        simp [jointDist]
      rw [hJ]
      by_cases hz : inp.p x * (1 - p) = 0
      · rw [if_pos hz]
      · rw [if_neg hz, div_self hz, Real.log_one, mul_zero]
    · have hJ : jointDist (bec p hp0.le hp1.le) inp (x, some y) = 0 := by
        simp [jointDist, hxy]
      rw [hJ]; simp
  -- The `none` summand reduces to the binary-entropy term scaled by `p`.
  have hnone : ∀ x : Bool,
      (if jointDist (bec p hp0.le hp1.le) inp (x, none) = 0 then (0 : ℝ)
       else jointDist (bec p hp0.le hp1.le) inp (x, none) *
         Real.log (jointDist (bec p hp0.le hp1.le) inp (x, none) /
           (∑ x' : Bool, jointDist (bec p hp0.le hp1.le) inp (x', none))))
      = (if inp.p x = 0 then 0 else inp.p x * p * Real.log (inp.p x)) := by
    intro x
    have hJ : jointDist (bec p hp0.le hp1.le) inp (x, none) = inp.p x * p := by
      simp [jointDist]
    rw [hJ, bec_ymarg_none hp0.le hp1.le inp]
    by_cases hx : inp.p x = 0
    · rw [if_pos (by rw [hx, zero_mul]), if_pos hx]
    · rw [if_neg (mul_ne_zero hx hp0.ne'), if_neg hx,
          mul_div_assoc, div_self hp0.ne', mul_one]
  -- Assemble: the per-input inner sum collapses to the `none` term.
  have hinner : ∀ x : Bool,
      (∑ o : Option Bool,
        if jointDist (bec p hp0.le hp1.le) inp (x, o) = 0 then (0 : ℝ)
        else jointDist (bec p hp0.le hp1.le) inp (x, o) *
          Real.log (jointDist (bec p hp0.le hp1.le) inp (x, o) /
            (∑ x' : Bool, jointDist (bec p hp0.le hp1.le) inp (x', o))))
      = (if inp.p x = 0 then 0 else inp.p x * p * Real.log (inp.p x)) := by
    intro x
    -- Apply `hnone` BEFORE expanding any Bool sum, so the `∑ x'` denominator in the
    -- `none` term still matches `hnone`'s LHS; then collapse the `some` sum to 0.
    rw [Fintype.sum_option, hnone x,
        Finset.sum_eq_zero (fun i _ => hsome_zero x i), add_zero]
  -- Sum over inputs, factor out `p`, and recognise `-H(X)`.
  unfold conditionalEntropy
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  have hfactor : ∀ x : Bool,
      (if inp.p x = 0 then (0 : ℝ) else inp.p x * p * Real.log (inp.p x))
      = p * (if inp.p x = 0 then 0 else inp.p x * Real.log (inp.p x)) := by
    intro x; by_cases hx : inp.p x = 0 <;> simp [hx] <;> ring
  rw [Finset.sum_congr rfl (fun x _ => hfactor x), ← Finset.mul_sum,
      show shannonEntropy inp.p
        = -∑ x : Bool, if inp.p x = 0 then (0 : ℝ) else inp.p x * Real.log (inp.p x) from rfl]
  ring

/-! ## Mutual information `I(X;Y) = (1 - p) · H(X)` -/

/-- **The BEC mutual information identity.** For any input distribution,
    `I(X;Y) = (1 - p) · H(X)`. Immediate from the chain rule
    `I = H(X) - H(X|Y)` and `H(X|Y) = p · H(X)`. -/
theorem bec_mi_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (inp : InputDist Bool) :
    channelMI (bec p hp0.le hp1.le) inp = (1 - p) * shannonEntropy inp.p := by
  unfold channelMI
  have hnn : ∀ xy, 0 ≤ jointDist (bec p hp0.le hp1.le) inp xy :=
    fun xy => jointDist_nonneg _ inp xy
  have hsum : ∑ xy : Bool × Option Bool, jointDist (bec p hp0.le hp1.le) inp xy = 1 :=
    jointDist_sum_one _ inp
  rw [chain_rule hnn hsum]
  -- X-marginal of the joint equals the input distribution.
  have hxmarg : (fun x => ∑ y : Option Bool, jointDist (bec p hp0.le hp1.le) inp (x, y))
      = inp.p := by
    ext x
    simp only [jointDist, ← Finset.mul_sum, (bec p hp0.le hp1.le).sum_one, mul_one]
  rw [hxmarg, bec_conditional_entropy hp0 hp1 inp]
  ring

/-! ## Capacity = (1 - p) · log 2 -/

/-- Uniform input achieves `I(X;Y) = (1 - p) · log 2`. -/
theorem bec_uniform_mi {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelMI (bec p hp0.le hp1.le) BSCCapacity.uniformBool = (1 - p) * Real.log 2 := by
  rw [bec_mi_eq hp0 hp1]
  have h : BSCCapacity.uniformBool.p = (fun (_ : Bool) => (1 : ℝ) / 2) := rfl
  rw [h, BSCCapacity.entropy_uniform_bool]

/-- For any input, `I(X;Y) ≤ (1 - p) · log 2` (the converse bound). -/
theorem bec_mi_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (inp : InputDist Bool) :
    channelMI (bec p hp0.le hp1.le) inp ≤ (1 - p) * Real.log 2 := by
  rw [bec_mi_eq hp0 hp1]
  have hHX : shannonEntropy inp.p ≤ Real.log 2 := by
    have h := entropy_le_log_card inp.nonneg inp.sum_one
    simp only [Fintype.card_bool, Nat.cast_ofNat] at h
    exact h
  have h1p : 0 ≤ 1 - p := by linarith
  exact mul_le_mul_of_nonneg_left hHX h1p

/-- **BEC capacity = (1 - p) · log 2.**
    The binary erasure channel `BEC(p)` has capacity `(1 - p) · log 2` nats
    (equivalently `1 - p` bits). Proven from first principles with no axioms:
    every input distribution gives `I(X;Y) = (1 - p)·H(X) ≤ (1 - p)·log 2`,
    and the uniform input achieves the bound. -/
theorem bec_capacity {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (bec p hp0.le hp1.le) = (1 - p) * Real.log 2 := by
  unfold channelCapacity
  apply le_antisymm
  · -- sSup ≤ (1 - p) · log 2
    apply csSup_le
    · exact ⟨_, BSCCapacity.uniformBool, rfl⟩
    · rintro r ⟨inp, rfl⟩; exact bec_mi_le hp0 hp1 inp
  · -- (1 - p) · log 2 ≤ sSup (achieved by uniform)
    apply le_csSup
    · exact ⟨Real.log (Fintype.card (Option Bool)),
        fun _ ⟨inp, hr⟩ => hr ▸ channelMI_le_log_card _ _⟩
    · exact ⟨BSCCapacity.uniformBool, bec_uniform_mi hp0 hp1⟩

/-- BEC capacity in bits: `C₂(BEC(p)) = 1 - p`. -/
theorem bec_capacity_bits {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (bec p hp0.le hp1.le) / Real.log 2 = 1 - p := by
  rw [bec_capacity hp0 hp1, mul_div_assoc,
    div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one]

/-- BEC capacity is non-negative. -/
theorem bec_capacity_nonneg {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ channelCapacity (bec p hp0.le hp1.le) := by
  rw [bec_capacity hp0 hp1]
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- BEC capacity is at most `log 2` (= 1 bit), with equality only as `p → 0`. -/
theorem bec_capacity_le_log_two {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (bec p hp0.le hp1.le) ≤ Real.log 2 := by
  rw [bec_capacity hp0 hp1]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith [mul_nonneg hp0.le hlog]

/-! ## Operational converse via Fano's inequality

  The information capacity `C = (1 - p)·log 2` computed above is the *value* the
  operational converse bounds against. The single-letter converse ingredient is
  Fano's inequality, packaged in `ShannonChannelCoding.lean` as the proved
  (axiom-free) theorem `fano_converse_capacity`:

      log |α| ≤ channelCapacity ch + h(P_e) + P_e · log(|α| - 1)

  for a uniform input, where `P_e` is the Fano error term of the joint
  distribution. Specialising this to the BEC is unusually clean: the input
  alphabet is `Bool`, so `|α| = 2` and the correction `P_e · log(|α| - 1) =
  P_e · log 1 = 0` vanishes identically. Substituting the computed capacity
  `C = (1 - p)·log 2` (`bec_capacity`) collapses the general single-letter
  converse to the sharp BEC statement below — no `channel_coding_converse`
  axiom is invoked. -/

/-- **BEC single-letter Fano converse.** For the uniform (rate = 1 bit) input on
    `BEC(p)`, the log-alphabet size is bounded by the capacity plus the binary
    entropy of the Fano error term:

      `log 2 ≤ (1 - p)·log 2 + h(P_e)`.

    This is `fano_converse_capacity` specialised to `α = Bool`: the general
    `P_e · log(|α| - 1)` correction is `P_e · log 1 = 0` for a binary input, and
    `channelCapacity (bec p) = (1 - p)·log 2` by `bec_capacity`. Axiom-free. -/
theorem bec_fano_converse {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    let P_e := 1 - ∑ y : Option Bool, ∑ x : Bool,
                 jointDist (bec p hp0.le hp1.le) BSCCapacity.uniformBool (x, y) ^ 2 /
                   (∑ x' : Bool, jointDist (bec p hp0.le hp1.le) BSCCapacity.uniformBool (x', y))
    Real.log 2 ≤ (1 - p) * Real.log 2 + InformationTheory.BinaryEntropy.h P_e := by
  intro P_e
  -- The uniform Bool input is the constant `|α|⁻¹ = 1/2`.
  have h_uniform : ∀ x : Bool,
      BSCCapacity.uniformBool.p x = (Fintype.card Bool : ℝ)⁻¹ := by
    intro x
    simp only [BSCCapacity.uniformBool, Fintype.card_bool, Nat.cast_ofNat]
    norm_num
  -- Instantiate the proved single-letter Fano converse at the BEC.
  have hfc :
      Real.log (Fintype.card Bool) ≤
        channelCapacity (bec p hp0.le hp1.le) +
        InformationTheory.BinaryEntropy.h P_e +
        P_e * Real.log ((Fintype.card Bool : ℝ) - 1) :=
    fano_converse_capacity (bec p hp0.le hp1.le) BSCCapacity.uniformBool h_uniform
  -- `|Bool| = 2`, so the log-cardinality is `log 2` and the correction vanishes.
  have hcard : (Fintype.card Bool : ℝ) = 2 := by norm_num [Fintype.card_bool]
  rw [hcard, bec_capacity hp0 hp1] at hfc
  have h1 : ((2 : ℝ) - 1) = 1 := by norm_num
  rw [h1, Real.log_one, mul_zero, add_zero] at hfc
  exact hfc

/-- **BEC Fano error lower bound.** Rearranging `bec_fano_converse`: for the
    uniform (1-bit) input on `BEC(p)`, the binary entropy of the Fano error term
    is at least `p·log 2`:

      `p·log 2 ≤ h(P_e)`.

    Operational reading: at the maximal input rate of one bit per channel use, a
    fraction `p` of that bit is erased, and no single-letter decoding can drive
    the residual error entropy below `p·log 2`. This is the sharp form of the
    BEC converse — the capacity gap `log 2 - C = p·log 2` is exactly the floor on
    `h(P_e)`. Axiom-free. -/
theorem bec_fano_error_lower {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    let P_e := 1 - ∑ y : Option Bool, ∑ x : Bool,
                 jointDist (bec p hp0.le hp1.le) BSCCapacity.uniformBool (x, y) ^ 2 /
                   (∑ x' : Bool, jointDist (bec p hp0.le hp1.le) BSCCapacity.uniformBool (x', y))
    p * Real.log 2 ≤ InformationTheory.BinaryEntropy.h P_e := by
  intro P_e
  have hb : Real.log 2 ≤ (1 - p) * Real.log 2 + InformationTheory.BinaryEntropy.h P_e :=
    bec_fano_converse hp0 hp1
  have hexp : (1 - p) * Real.log 2 = Real.log 2 - p * Real.log 2 := by ring
  linarith [hb, hexp]

end InformationTheory.ChannelCoding.BEC
