/-
  q-ary Erasure Channel (QEC) Capacity

  Open Question 01 of the BEC entry (`shannon-channel-coding-bec`): generalize
  the binary erasure channel to an arbitrary input alphabet of size `q`.

  Main result: the q-ary erasure channel `QEC(p)` over a finite input type `α`
  with `Fintype.card α = q` has capacity

      C(QEC(p)) = (1 - p) · log q   (nats)

  proven from first principles (0 axioms, 0 sorries). The binary erasure
  channel is the special case `α = Bool` (`q = 2`), where the channel transition
  kernel coincides on the nose with `bec` (`qec_eq_bec`) and the capacity
  specializes to `(1 - p) · log 2`.

  The QEC over input type `α` has output `Option α` (`none` = erasure). Each
  symbol is erased with probability `p` and received correctly with probability
  `1 - p`:

      W x (some y) = if x = y then 1 - p else 0
      W x none     = p

  Capacity proof (the same single identity as the binary case, with `Bool`
  replaced by `α`):
  1. For ANY input distribution, the entropy of the input given the output is
     `H(X|Y) = p · H(X)` (erasure with probability `p`; otherwise the input is
     determined exactly).
  2. Chain rule: `I(X;Y) = H(X) - H(X|Y) = (1 - p) · H(X)`.
  3. Converse: `H(X) ≤ log|α| = log q`, so `I(X;Y) ≤ (1 - p) · log q`.
  4. Achievability: the uniform input gives `H(X) = log q`.
  5. Capacity = sSup over inputs = `(1 - p) · log q`.

  The erasure decomposition `H(X|Y) = p·H(X)` uses nothing about `q`; the only
  alphabet-specific ingredient is the maximum-entropy value `log q`, supplied by
  `entropy_of_uniform_eq_log_card`.

  Claude Shannon (1948)

  Axioms: 0
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonChannelCoding
import Proofs.ShannonEntropy
import Proofs.ShannonChannelCodingBEC

open Real Finset InformationTheory InformationTheory.ChannelCoding

namespace InformationTheory.ChannelCoding.QEC

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The q-ary erasure channel -/

/-- The q-ary erasure channel `QEC(p)`: input `α`, output `Option α`
    (`none` = erasure). Each symbol is erased with probability `p` and otherwise
    received correctly. Requires `0 ≤ p ≤ 1`. -/
noncomputable def qec (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    DMChannel α (Option α) where
  W := fun x o =>
    match o with
    | none => p
    | some y => if x = y then 1 - p else 0
  nonneg := fun x o => by
    cases o with
    | none => exact hp0
    | some y => dsimp only; split_ifs <;> linarith
  sum_one := fun x => by
    rw [Fintype.sum_option]
    show p + ∑ y : α, (if x = y then 1 - p else 0) = 1
    rw [Finset.sum_ite_eq Finset.univ x (fun _ => (1 : ℝ) - p),
        if_pos (Finset.mem_univ x)]
    ring

@[simp] lemma qec_W_none {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : α) :
    (qec p hp0 hp1).W x none = p := rfl

@[simp] lemma qec_W_some {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x y : α) :
    (qec p hp0 hp1).W x (some y) = if x = y then 1 - p else 0 := rfl

/-! ## Output marginals -/

/-- The `none` (erasure) output marginal equals `p` regardless of the input
    distribution: every input symbol is erased with probability `p`. -/
lemma qec_ymarg_none {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (inp : InputDist α) :
    (∑ x' : α, jointDist (qec p hp0 hp1) inp (x', none)) = p := by
  simp only [jointDist, qec_W_none]
  rw [← Finset.sum_mul, inp.sum_one, one_mul]

/-- The `some y` output marginal equals `inp.p y · (1 - p)`: the symbol `y` is
    received un-erased only when `y` was sent (probability `inp.p y`) and not
    erased (probability `1 - p`). -/
lemma qec_ymarg_some {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (inp : InputDist α)
    (y : α) :
    (∑ x' : α, jointDist (qec p hp0 hp1) inp (x', some y)) = inp.p y * (1 - p) := by
  simp only [jointDist, qec_W_some]
  rw [Finset.sum_eq_single y
        (fun b _ hby => by rw [if_neg hby, mul_zero])
        (fun h => absurd (Finset.mem_univ y) h),
      if_pos rfl]

/-! ## Conditional entropy `H(X|Y) = p · H(X)` -/

/-- **The QEC erasure identity.** For any input distribution, the entropy of the
    input given the output is `H(X|Y) = p · H(X)`.

    With probability `1 - p` the output is the un-erased symbol, which determines
    the input exactly (zero residual entropy); with probability `p` the output is
    an erasure, leaving the full input entropy `H(X)`. -/
theorem qec_conditional_entropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (inp : InputDist α) :
    conditionalEntropy (jointDist (qec p hp0.le hp1.le) inp)
      = p * shannonEntropy inp.p := by
  -- Each `some y` summand vanishes: when `x ≠ y` the joint prob is 0;
  -- when `x = y` the conditional probability is 1 (log 1 = 0).
  have hsome_zero : ∀ (x y : α),
      (if jointDist (qec p hp0.le hp1.le) inp (x, some y) = 0 then (0 : ℝ)
       else jointDist (qec p hp0.le hp1.le) inp (x, some y) *
         Real.log (jointDist (qec p hp0.le hp1.le) inp (x, some y) /
           (∑ x' : α, jointDist (qec p hp0.le hp1.le) inp (x', some y)))) = 0 := by
    intro x y
    rw [qec_ymarg_some hp0.le hp1.le inp y]
    by_cases hxy : x = y
    · subst hxy
      have hJ : jointDist (qec p hp0.le hp1.le) inp (x, some x) = inp.p x * (1 - p) := by
        simp [jointDist]
      rw [hJ]
      by_cases hz : inp.p x * (1 - p) = 0
      · rw [if_pos hz]
      · rw [if_neg hz, div_self hz, Real.log_one, mul_zero]
    · have hJ : jointDist (qec p hp0.le hp1.le) inp (x, some y) = 0 := by
        simp [jointDist, hxy]
      rw [hJ]; simp
  -- The `none` summand reduces to the entropy term scaled by `p`.
  have hnone : ∀ x : α,
      (if jointDist (qec p hp0.le hp1.le) inp (x, none) = 0 then (0 : ℝ)
       else jointDist (qec p hp0.le hp1.le) inp (x, none) *
         Real.log (jointDist (qec p hp0.le hp1.le) inp (x, none) /
           (∑ x' : α, jointDist (qec p hp0.le hp1.le) inp (x', none))))
      = (if inp.p x = 0 then 0 else inp.p x * p * Real.log (inp.p x)) := by
    intro x
    have hJ : jointDist (qec p hp0.le hp1.le) inp (x, none) = inp.p x * p := by
      simp [jointDist]
    rw [hJ, qec_ymarg_none hp0.le hp1.le inp]
    by_cases hx : inp.p x = 0
    · rw [if_pos (by rw [hx, zero_mul]), if_pos hx]
    · rw [if_neg (mul_ne_zero hx hp0.ne'), if_neg hx,
          mul_div_assoc, div_self hp0.ne', mul_one]
  -- Assemble: the per-input inner sum collapses to the `none` term.
  have hinner : ∀ x : α,
      (∑ o : Option α,
        if jointDist (qec p hp0.le hp1.le) inp (x, o) = 0 then (0 : ℝ)
        else jointDist (qec p hp0.le hp1.le) inp (x, o) *
          Real.log (jointDist (qec p hp0.le hp1.le) inp (x, o) /
            (∑ x' : α, jointDist (qec p hp0.le hp1.le) inp (x', o))))
      = (if inp.p x = 0 then 0 else inp.p x * p * Real.log (inp.p x)) := by
    intro x
    rw [Fintype.sum_option, hnone x,
        Finset.sum_eq_zero (fun i _ => hsome_zero x i), add_zero]
  -- Sum over inputs, factor out `p`, and recognise `-H(X)`.
  unfold conditionalEntropy
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  have hfactor : ∀ x : α,
      (if inp.p x = 0 then (0 : ℝ) else inp.p x * p * Real.log (inp.p x))
      = p * (if inp.p x = 0 then 0 else inp.p x * Real.log (inp.p x)) := by
    intro x; by_cases hx : inp.p x = 0 <;> simp [hx] <;> ring
  rw [Finset.sum_congr rfl (fun x _ => hfactor x), ← Finset.mul_sum,
      show shannonEntropy inp.p
        = -∑ x : α, if inp.p x = 0 then (0 : ℝ) else inp.p x * Real.log (inp.p x) from rfl]
  ring

/-! ## Mutual information `I(X;Y) = (1 - p) · H(X)` -/

/-- **The QEC mutual information identity.** For any input distribution,
    `I(X;Y) = (1 - p) · H(X)`. Immediate from the chain rule
    `I = H(X) - H(X|Y)` and `H(X|Y) = p · H(X)`. -/
theorem qec_mi_eq {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (inp : InputDist α) :
    channelMI (qec p hp0.le hp1.le) inp = (1 - p) * shannonEntropy inp.p := by
  unfold channelMI
  have hnn : ∀ xy, 0 ≤ jointDist (qec p hp0.le hp1.le) inp xy :=
    fun xy => jointDist_nonneg _ inp xy
  have hsum : ∑ xy : α × Option α, jointDist (qec p hp0.le hp1.le) inp xy = 1 :=
    jointDist_sum_one _ inp
  rw [chain_rule hnn hsum]
  -- X-marginal of the joint equals the input distribution.
  have hxmarg : (fun x => ∑ y : Option α, jointDist (qec p hp0.le hp1.le) inp (x, y))
      = inp.p := by
    ext x
    simp only [jointDist, ← Finset.mul_sum, (qec p hp0.le hp1.le).sum_one, mul_one]
  rw [hxmarg, qec_conditional_entropy hp0 hp1 inp]
  ring

/-! ## Uniform input and capacity = (1 - p) · log q -/

/-- The uniform input distribution on `α`: `p(x) = 1/|α|`. -/
noncomputable def uniformInput [Nonempty α] : InputDist α where
  p := fun _ => (Fintype.card α : ℝ)⁻¹
  nonneg := fun _ => by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)]

/-- Uniform input achieves `I(X;Y) = (1 - p) · log q`. -/
theorem qec_uniform_mi [Nonempty α] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelMI (qec p hp0.le hp1.le) (uniformInput (α := α))
      = (1 - p) * Real.log (Fintype.card α) := by
  rw [qec_mi_eq hp0 hp1]
  have h : (uniformInput (α := α)).p = (fun _ => (Fintype.card α : ℝ)⁻¹) := rfl
  rw [h, entropy_of_uniform_eq_log_card]

/-- For any input, `I(X;Y) ≤ (1 - p) · log q` (the converse bound). -/
theorem qec_mi_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (inp : InputDist α) :
    channelMI (qec p hp0.le hp1.le) inp ≤ (1 - p) * Real.log (Fintype.card α) := by
  rw [qec_mi_eq hp0 hp1]
  have hHX : shannonEntropy inp.p ≤ Real.log (Fintype.card α) :=
    entropy_le_log_card inp.nonneg inp.sum_one
  have h1p : 0 ≤ 1 - p := by linarith
  exact mul_le_mul_of_nonneg_left hHX h1p

/-- **QEC capacity = (1 - p) · log q.**
    The q-ary erasure channel `QEC(p)` over a finite input type `α` has capacity
    `(1 - p) · log|α|` nats. Proven from first principles with no axioms: every
    input distribution gives `I(X;Y) = (1 - p)·H(X) ≤ (1 - p)·log|α|`, and the
    uniform input achieves the bound. -/
theorem qec_capacity [Nonempty α] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (qec (α := α) p hp0.le hp1.le)
      = (1 - p) * Real.log (Fintype.card α) := by
  unfold channelCapacity
  apply le_antisymm
  · -- sSup ≤ (1 - p) · log q
    apply csSup_le
    · exact ⟨_, uniformInput (α := α), rfl⟩
    · rintro r ⟨inp, rfl⟩; exact qec_mi_le hp0 hp1 inp
  · -- (1 - p) · log q ≤ sSup (achieved by uniform)
    apply le_csSup
    · exact ⟨Real.log (Fintype.card (Option α)),
        fun _ ⟨inp, hr⟩ => hr ▸ channelMI_le_log_card _ _⟩
    · exact ⟨uniformInput (α := α), qec_uniform_mi hp0 hp1⟩

/-- **QEC capacity in terms of the alphabet size `q`.** If `|α| = q`, the
    capacity is `(1 - p) · log q`. -/
theorem qec_capacity_card [Nonempty α] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {q : ℕ} (hq : Fintype.card α = q) :
    channelCapacity (qec (α := α) p hp0.le hp1.le) = (1 - p) * Real.log q := by
  rw [qec_capacity hp0 hp1, hq]

/-- QEC capacity is non-negative. -/
theorem qec_capacity_nonneg [Nonempty α] {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ channelCapacity (qec (α := α) p hp0.le hp1.le) := by
  rw [qec_capacity hp0 hp1]
  have h1p : 0 ≤ 1 - p := by linarith
  have hlog : 0 ≤ Real.log (Fintype.card α) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  exact mul_nonneg h1p hlog

/-! ## The binary erasure channel as the `q = 2` special case -/

/-- The QEC transition kernel over `Bool` coincides on the nose with the binary
    erasure channel `bec`: the BEC is literally the `q = 2` instance of the QEC. -/
theorem qec_eq_bec {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (qec (α := Bool) p hp0 hp1).W = (BEC.bec p hp0 hp1).W := by
  funext x o; cases o <;> rfl

/-- The `q = 2` capacity specializes to `(1 - p) · log 2`, recovering the BEC. -/
theorem qec_capacity_bool {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (qec (α := Bool) p hp0.le hp1.le) = (1 - p) * Real.log 2 := by
  rw [qec_capacity hp0 hp1, Fintype.card_bool, Nat.cast_ofNat]

/-- BEC capacity in bits: `C₂(QEC(p) over Bool) = 1 - p`, matching the parent
    `bec_capacity_bits`. -/
theorem qec_capacity_bool_bits {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    channelCapacity (qec (α := Bool) p hp0.le hp1.le) / Real.log 2 = 1 - p := by
  rw [qec_capacity_bool hp0 hp1, mul_div_assoc,
    div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne', mul_one]

end InformationTheory.ChannelCoding.QEC
