/-
  Binary Error-and-Erasure Channel (BEEC) Capacity

  Open question (shannon-channel-coding-bec OQ-04): extend the binary erasure
  channel to a channel with **both erasures and errors** — the binary
  error-and-erasure channel BEEC(ε, q).

  Model.  Input `Bool`, output `Option Bool` (`none` = erasure). Each symbol is
  erased with probability `ε`; if it is *not* erased (probability `1 - ε`) it is
  transmitted through a binary symmetric channel with crossover probability `q`
  (flipped with probability `q`, correct with probability `1 - q`):

      W x none        = ε
      W x (some x)    = (1 - ε)·(1 - q)          -- delivered, correct
      W x (some ¬x)   = (1 - ε)·q                -- delivered, flipped

  This is the natural common generalisation of the two channels already in the
  gallery:

    * `q = 0` (no errors)     →  BEEC = BEC,  capacity `(1 - ε)·log 2`
      (`ShannonChannelCodingBEC.bec_capacity`).
    * `ε = 0` (no erasures)   →  BEEC = BSC,  capacity `log 2 - h(q)`
      (`ShannonChannelCodingOQ02.bsc_capacity_proved`).

  **Main result** (`beec_capacity`, 0 axioms, 0 sorries):

      C(BEEC(ε, q)) = (1 - ε)·(log 2 - h(q))   nats.

  Proof engine, following the BSC development:
  1.  `H(Y|X) = h(ε) + (1 - ε)·h(q)` for *every* input distribution
      (`beec_conditional_output_entropy`): the per-input output law
      `(ε, (1-ε)(1-q), (1-ε)q)` is the same for both inputs.
  2.  Chain rule `I(X;Y) = H(Y) - H(Y|X)` (`mi_eq_hY_sub_hYgivenX`).
  3.  Achievability: the uniform input gives `H(Y) = h(ε) + (1-ε)·log 2`, hence
      `I = (1-ε)(log 2 - h(q))` (`beec_uniform_mi`).
  4.  Converse: for *any* input the output marginal has a fixed erasure mass `ε`,
      so `H(Y) = h(ε) + (1-ε)·H₂(·) ≤ h(ε) + (1-ε)·log 2`
      (`beec_ymarg_entropy_le`, via the grouping bound `mul_log_pair_ge`).

  Both degenerations `q → 0` and `ε → 0` of the capacity formula are recorded as
  `beec_capacity_eq_bec_formula` / `beec_capacity_eq_bsc_formula`.

  Claude Shannon (1948).

  Axioms: 0
  Sorries: 0
-/
import Mathlib
import Proofs.ShannonChannelCoding
import Proofs.ShannonChannelCodingOQ02
import Proofs.ShannonChannelCodingOQ04
import Proofs.ShannonChannelCodingBEC

open Real Finset InformationTheory InformationTheory.ChannelCoding
open InformationTheory.BinaryEntropy

namespace InformationTheory.ChannelCoding.BEEC

/-! ## An elementary two-point log inequality (grouping bound engine)

For positive `a, b`, the "pooled" term `(a+b)·log((a+b)/2)` is a lower bound for
`a·log a + b·log b`. Equivalently, the binary entropy of the split `(a, b)` is at
most `log 2`. This is the only inequality needed for the converse. -/

/-- **Two-point log bound.** For `a, b > 0`,
`(a + b)·log((a+b)/2) ≤ a·log a + b·log b`.
Rearranged, this says the binary entropy `H₂(a/(a+b)) ≤ log 2`. -/
lemma mul_log_pair_ge {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a + b) * Real.log ((a + b) / 2) ≤ a * Real.log a + b * Real.log b := by
  have hs : (0 : ℝ) < a + b := by linarith
  have hne : a + b ≠ 0 := hs.ne'
  have hu0 : 0 < a / (a + b) := div_pos ha hs
  have hu1 : a / (a + b) < 1 := (div_lt_one hs).mpr (by linarith)
  have h1u : 1 - a / (a + b) = b / (a + b) := by
    rw [← div_self hne, div_sub_div_same]; congr 1; ring
  have hh : InformationTheory.BinaryEntropy.h (a / (a + b)) ≤ Real.log 2 :=
    InformationTheory.BinaryEntropy.h_le_log_two hu0.le hu1.le
  have hlu : Real.log (a / (a + b)) = Real.log a - Real.log (a + b) :=
    Real.log_div ha.ne' hne
  have hl1u : Real.log (b / (a + b)) = Real.log b - Real.log (a + b) :=
    Real.log_div hb.ne' hne
  -- Recast `a log a + b log b` through the binary entropy of the split.
  have key : a * Real.log a + b * Real.log b
      = (a + b) * Real.log (a + b)
        - (a + b) * InformationTheory.BinaryEntropy.h (a / (a + b)) := by
    rw [InformationTheory.BinaryEntropy.h, h1u, hlu, hl1u]
    field_simp
    ring
  have hls2 : Real.log ((a + b) / 2) = Real.log (a + b) - Real.log 2 :=
    Real.log_div hne (by norm_num)
  rw [key, hls2]
  nlinarith [mul_le_mul_of_nonneg_left hh hs.le]

/-! ## The binary error-and-erasure channel -/

/-- The binary error-and-erasure channel `BEEC(ε, q)`: input `Bool`, output
    `Option Bool` (`none` = erasure). Erased with probability `ε`; otherwise
    passed through a BSC with crossover probability `q`. -/
noncomputable def beec (ε q : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : DMChannel Bool (Option Bool) where
  W := fun x o =>
    match o with
    | none => ε
    | some y => if x = y then (1 - ε) * (1 - q) else (1 - ε) * q
  nonneg := fun x o => by
    cases o with
    | none => exact hε0
    | some y =>
        dsimp only
        split_ifs <;> exact mul_nonneg (by linarith) (by linarith)
  sum_one := fun x => by
    rw [Fintype.sum_option, Fintype.sum_bool]
    cases x <;> · dsimp only; simp only [reduceIte, reduceCtorEq]; ring

@[simp] lemma beec_W_none {ε q : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x : Bool) :
    (beec ε q hε0 hε1 hq0 hq1).W x none = ε := rfl

@[simp] lemma beec_W_some {ε q : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x y : Bool) :
    (beec ε q hε0 hε1 hq0 hq1).W x (some y)
      = if x = y then (1 - ε) * (1 - q) else (1 - ε) * q := rfl

/-- Every transition probability is strictly positive for `0 < ε < 1`,
    `0 < q < 1`. -/
lemma beec_W_pos {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (x : Bool) (o : Option Bool) :
    0 < (beec ε q hε0.le hε1.le hq0.le hq1.le).W x o := by
  cases o with
  | none => exact hε0
  | some y =>
      simp only [beec_W_some]
      split_ifs <;> exact mul_pos (by linarith) (by linarith)

/-! ## Output marginals -/

/-- The erasure (`none`) output marginal is `ε` for every input distribution. -/
lemma beec_ymarg_none {ε q : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (inp : InputDist Bool) :
    (∑ x' : Bool, jointDist (beec ε q hε0 hε1 hq0 hq1) inp (x', none)) = ε := by
  simp only [jointDist, beec_W_none]
  rw [← Finset.sum_mul, inp.sum_one, one_mul]

/-- The un-erased marginal `P(Y = some y) = (1 - ε)·(p(y)(1-q) + p(¬y) q)`. -/
lemma beec_ymarg_some {ε q : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (inp : InputDist Bool) (y : Bool) :
    (∑ x' : Bool, jointDist (beec ε q hε0 hε1 hq0 hq1) inp (x', some y))
      = (1 - ε) * (inp.p y * (1 - q) + inp.p (!y) * q) := by
  simp only [jointDist, beec_W_some]
  rw [Fintype.sum_bool]
  cases y <;> · simp <;> ring

/-! ## Conditional output entropy `H(Y|X) = h(ε) + (1-ε)·h(q)` -/

/-- The per-input output "energy" `∑_o W(x,o)·log W(x,o)` is the same for both
    inputs and equals `ε·log ε + (1-ε)(1-q)·log((1-ε)(1-q)) + (1-ε)q·log((1-ε)q)`. -/
lemma beec_output_entropy_per_input {ε q : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (x : Bool) :
    ∑ o : Option Bool, (beec ε q hε0 hε1 hq0 hq1).W x o *
        Real.log ((beec ε q hε0 hε1 hq0 hq1).W x o)
      = ε * Real.log ε
        + (1 - ε) * (1 - q) * Real.log ((1 - ε) * (1 - q))
        + (1 - ε) * q * Real.log ((1 - ε) * q) := by
  rw [Fintype.sum_option, Fintype.sum_bool]
  simp only [beec_W_none, beec_W_some]
  cases x <;> · simp only [if_true, if_false, Bool.true_eq_false, Bool.false_eq_true,
    reduceCtorEq]; ring

/-- The negated per-input energy is exactly `h(ε) + (1-ε)·h(q)`. -/
lemma neg_output_energy_eq {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    -(ε * Real.log ε
        + (1 - ε) * (1 - q) * Real.log ((1 - ε) * (1 - q))
        + (1 - ε) * q * Real.log ((1 - ε) * q))
      = InformationTheory.BinaryEntropy.h ε
        + (1 - ε) * InformationTheory.BinaryEntropy.h q := by
  have h1e : (0 : ℝ) < 1 - ε := by linarith
  have h1q : (0 : ℝ) < 1 - q := by linarith
  rw [Real.log_mul h1e.ne' h1q.ne', Real.log_mul h1e.ne' hq0.ne']
  simp only [InformationTheory.BinaryEntropy.h]
  ring

/-- **H(Y|X) = h(ε) + (1-ε)·h(q)** for any positive input distribution.
    Mirrors `bsc_conditional_output_entropy`. -/
theorem beec_conditional_output_entropy {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (inp : InputDist Bool) (hinp : ∀ b, 0 < inp.p b) :
    conditionalEntropy
        (transposeJoint (jointDist (beec ε q hε0.le hε1.le hq0.le hq1.le) inp))
      = InformationTheory.BinaryEntropy.h ε
        + (1 - ε) * InformationTheory.BinaryEntropy.h q := by
  set ch := beec ε q hε0.le hε1.le hq0.le hq1.le with hch_def
  unfold conditionalEntropy transposeJoint jointDist
  dsimp only
  have hne : ∀ (b : Bool) (a : Option Bool), inp.p b * ch.W b a ≠ 0 :=
    fun b a => ne_of_gt (mul_pos (hinp b) (beec_W_pos hε0 hε1 hq0 hq1 b a))
  have hden : ∀ b : Bool, ∑ a' : Option Bool, inp.p b * ch.W b a' = inp.p b :=
    fun b => by rw [← Finset.mul_sum, ch.sum_one, mul_one]
  have hterm : ∀ (a : Option Bool) (b : Bool),
      (if inp.p b * ch.W b a = 0 then (0 : ℝ)
       else inp.p b * ch.W b a *
         Real.log (inp.p b * ch.W b a / (∑ a' : Option Bool, inp.p b * ch.W b a'))) =
      inp.p b * (ch.W b a * Real.log (ch.W b a)) := by
    intro a b
    rw [if_neg (hne b a), hden b, mul_div_cancel_left₀ _ (ne_of_gt (hinp b))]
    ring
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [hch_def, beec_output_entropy_per_input hε0.le hε1.le hq0.le hq1.le]
  rw [← Finset.sum_mul, inp.sum_one, one_mul]
  exact neg_output_energy_eq hε0 hε1 hq0 hq1

/-! ## Mutual information -/

/-- **Achievability.** The uniform input yields
    `I(X;Y) = (1 - ε)·(log 2 - h(q))`. -/
theorem beec_uniform_mi {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    channelMI (beec ε q hε0.le hε1.le hq0.le hq1.le) BSCCapacity.uniformBool
      = (1 - ε) * (Real.log 2 - InformationTheory.BinaryEntropy.h q) := by
  set ch := beec ε q hε0.le hε1.le hq0.le hq1.le with hch_def
  unfold channelMI
  have hjoint_nn : ∀ xy, 0 ≤ jointDist ch BSCCapacity.uniformBool xy :=
    fun xy => le_of_lt (mul_pos (BSCCapacity.uniformBool_pos xy.1)
      (beec_W_pos hε0 hε1 hq0 hq1 xy.1 xy.2))
  have hjoint_sum := jointDist_sum_one ch BSCCapacity.uniformBool
  rw [BSCCapacity.mi_eq_hY_sub_hYgivenX hjoint_nn hjoint_sum,
      beec_conditional_output_entropy hε0 hε1 hq0 hq1 BSCCapacity.uniformBool
        BSCCapacity.uniformBool_pos]
  have h1e : (0 : ℝ) < 1 - ε := by linarith
  have hhalf : (1 - ε) / 2 ≠ 0 := by positivity
  have huni : BSCCapacity.uniformBool.p = fun _ => (1 : ℝ) / 2 := rfl
  have e_none : (∑ x : Bool, jointDist ch BSCCapacity.uniformBool (x, none)) = ε :=
    beec_ymarg_none hε0.le hε1.le hq0.le hq1.le BSCCapacity.uniformBool
  have e_false : (∑ x : Bool, jointDist ch BSCCapacity.uniformBool (x, some false)) = (1 - ε) / 2 := by
    rw [beec_ymarg_some hε0.le hε1.le hq0.le hq1.le BSCCapacity.uniformBool false, huni]; ring
  have e_true : (∑ x : Bool, jointDist ch BSCCapacity.uniformBool (x, some true)) = (1 - ε) / 2 := by
    rw [beec_ymarg_some hε0.le hε1.le hq0.le hq1.le BSCCapacity.uniformBool true, huni]; ring
  have hls2 : Real.log ((1 - ε) / 2) = Real.log (1 - ε) - Real.log 2 :=
    Real.log_div h1e.ne' (by norm_num)
  -- Compute `H(Y) = h(ε) + (1-ε)·log 2` for the uniform marginal.
  have hHY : shannonEntropy (fun o => ∑ x : Bool, jointDist ch BSCCapacity.uniformBool (x, o))
      = InformationTheory.BinaryEntropy.h ε + (1 - ε) * Real.log 2 := by
    unfold shannonEntropy
    rw [Fintype.sum_option, Fintype.sum_bool]
    dsimp only
    rw [e_none, e_false, e_true, if_neg hε0.ne', if_neg hhalf, hls2]
    simp only [InformationTheory.BinaryEntropy.h]
    ring
  rw [hHY]
  ring

/-- **Converse (positive input).** For any input with full support,
    `I(X;Y) ≤ (1 - ε)·(log 2 - h(q))`. -/
theorem beec_mi_le {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (inp : InputDist Bool) (hinp : ∀ b, 0 < inp.p b) :
    channelMI (beec ε q hε0.le hε1.le hq0.le hq1.le) inp
      ≤ (1 - ε) * (Real.log 2 - InformationTheory.BinaryEntropy.h q) := by
  set ch := beec ε q hε0.le hε1.le hq0.le hq1.le with hch_def
  unfold channelMI
  have hjoint_nn : ∀ xy, 0 ≤ jointDist ch inp xy :=
    fun xy => le_of_lt (mul_pos (hinp xy.1) (beec_W_pos hε0 hε1 hq0 hq1 xy.1 xy.2))
  have hjoint_sum := jointDist_sum_one ch inp
  rw [BSCCapacity.mi_eq_hY_sub_hYgivenX hjoint_nn hjoint_sum,
      beec_conditional_output_entropy hε0 hε1 hq0 hq1 inp hinp]
  have h1e : (0 : ℝ) < 1 - ε := by linarith
  have h1q : (0 : ℝ) < 1 - q := by linarith
  -- Abbreviations for the un-erased marginals.
  set a := (1 - ε) * (inp.p true * (1 - q) + inp.p false * q) with ha_def
  set b := (1 - ε) * (inp.p false * (1 - q) + inp.p true * q) with hb_def
  have hapos : 0 < a := by
    rw [ha_def]; exact mul_pos h1e (by nlinarith [hinp true, hinp false])
  have hbpos : 0 < b := by
    rw [hb_def]; exact mul_pos h1e (by nlinarith [hinp true, hinp false])
  have e_none : (∑ x : Bool, jointDist ch inp (x, none)) = ε :=
    beec_ymarg_none hε0.le hε1.le hq0.le hq1.le inp
  have e_false : (∑ x : Bool, jointDist ch inp (x, some false)) = b := by
    rw [beec_ymarg_some hε0.le hε1.le hq0.le hq1.le inp false, hb_def]; simp
  have e_true : (∑ x : Bool, jointDist ch inp (x, some true)) = a := by
    rw [beec_ymarg_some hε0.le hε1.le hq0.le hq1.le inp true, ha_def]; simp
  -- Total mass: `ε + a + b = 1`, hence `a + b = 1 - ε`.
  have hsum : a + b = 1 - ε := by
    have h := inp.sum_one
    rw [Fintype.sum_bool] at h
    rw [ha_def, hb_def]; nlinarith [h]
  -- `H(Y) = -(ε log ε + b log b + a log a)`.
  have hHY : shannonEntropy (fun o => ∑ x : Bool, jointDist ch inp (x, o))
      = -(ε * Real.log ε + (b * Real.log b + a * Real.log a)) := by
    unfold shannonEntropy
    rw [Fintype.sum_option, Fintype.sum_bool]
    dsimp only
    rw [e_none, e_false, e_true, if_neg hε0.ne', if_neg hbpos.ne', if_neg hapos.ne']
    ring
  -- Converse bound `H(Y) ≤ h(ε) + (1-ε) log 2` via the grouping inequality.
  have hHY_le : shannonEntropy (fun o => ∑ x : Bool, jointDist ch inp (x, o))
      ≤ InformationTheory.BinaryEntropy.h ε + (1 - ε) * Real.log 2 := by
    rw [hHY]
    have hgroup := mul_log_pair_ge hapos hbpos
    rw [hsum] at hgroup
    have hls2 : Real.log ((1 - ε) / 2) = Real.log (1 - ε) - Real.log 2 :=
      Real.log_div h1e.ne' (by norm_num)
    rw [hls2] at hgroup
    simp only [InformationTheory.BinaryEntropy.h]
    nlinarith [hgroup]
  rw [show (1 - ε) * (Real.log 2 - InformationTheory.BinaryEntropy.h q)
        = (1 - ε) * Real.log 2 - (1 - ε) * InformationTheory.BinaryEntropy.h q from by ring]
  linarith [hHY_le]

/-- **Converse (all inputs).** `I(X;Y) ≤ (1 - ε)·(log 2 - h(q))` for every input
    distribution, including degenerate (point-mass) ones. -/
theorem beec_mi_le_general {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 < q) (hq1 : q < 1) (inp : InputDist Bool) :
    channelMI (beec ε q hε0.le hε1.le hq0.le hq1.le) inp
      ≤ (1 - ε) * (Real.log 2 - InformationTheory.BinaryEntropy.h q) := by
  by_cases h : ∀ b, 0 < inp.p b
  · exact beec_mi_le hε0 hε1 hq0 hq1 inp h
  · push_neg at h
    obtain ⟨b₀, hb₀⟩ := h
    have hb₀_eq : inp.p b₀ = 0 := le_antisymm hb₀ (inp.nonneg b₀)
    set ch := beec ε q hε0.le hε1.le hq0.le hq1.le
    have hjoint_nn : ∀ xy, 0 ≤ jointDist ch inp xy :=
      fun xy => mul_nonneg (inp.nonneg xy.1) (ch.nonneg xy.1 xy.2)
    have hjoint_sum := jointDist_sum_one ch inp
    -- MI ≤ H(X) by the chain rule, and H(X) = 0 for a point mass.
    have hMI_le_HX : mutualInformation (jointDist ch inp) ≤
        shannonEntropy (fun x => ∑ y : Option Bool, jointDist ch inp (x, y)) := by
      have hchain := chain_rule hjoint_nn hjoint_sum
      have hcond := conditionalEntropy_nonneg hjoint_nn hjoint_sum
      linarith
    have hxmarg : (fun x => ∑ y : Option Bool, jointDist ch inp (x, y)) = inp.p := by
      ext x
      simp only [jointDist, ← Finset.mul_sum, ch.sum_one, mul_one]
    rw [hxmarg] at hMI_le_HX
    have hpoint : ∀ x : Bool, x ≠ !b₀ → inp.p x = 0 := by
      intro x hx; cases b₀ <;> cases x <;> simp_all
    have hent_zero : shannonEntropy inp.p = 0 :=
      entropy_point_mass inp.nonneg inp.sum_one hpoint
    rw [hent_zero] at hMI_le_HX
    unfold channelMI
    have hqle : InformationTheory.BinaryEntropy.h q ≤ Real.log 2 :=
      InformationTheory.BinaryEntropy.h_le_log_two hq0.le hq1.le
    have h1e : (0 : ℝ) ≤ 1 - ε := by linarith
    nlinarith [hMI_le_HX, mul_nonneg h1e (sub_nonneg.mpr hqle)]

/-! ## Capacity -/

/-- **BEEC capacity = (1 - ε)·(log 2 - h(q)).**
    The binary error-and-erasure channel `BEEC(ε, q)` has capacity
    `(1 - ε)·(log 2 - h(q))` nats, proven from first principles with no axioms.
    Every input gives `I ≤ (1-ε)(log 2 - h(q))`, and the uniform input attains
    the bound. -/
theorem beec_capacity {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    channelCapacity (beec ε q hε0.le hε1.le hq0.le hq1.le)
      = (1 - ε) * (Real.log 2 - InformationTheory.BinaryEntropy.h q) := by
  unfold channelCapacity
  apply le_antisymm
  · apply csSup_le
    · exact ⟨_, BSCCapacity.uniformBool, rfl⟩
    · rintro r ⟨inp, rfl⟩; exact beec_mi_le_general hε0 hε1 hq0 hq1 inp
  · apply le_csSup
    · exact ⟨Real.log (Fintype.card (Option Bool)),
        fun _ ⟨inp, hr⟩ => hr ▸ channelMI_le_log_card _ _⟩
    · exact ⟨BSCCapacity.uniformBool, beec_uniform_mi hε0 hε1 hq0 hq1⟩

/-- BEEC capacity in bits: `C₂(BEEC(ε, q)) = (1 - ε)·(1 - h₂(q))`. -/
theorem beec_capacity_bits {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hq0 : 0 < q) (hq1 : q < 1) :
    channelCapacity (beec ε q hε0.le hε1.le hq0.le hq1.le) / Real.log 2
      = (1 - ε) * (1 - InformationTheory.BinaryEntropy.h q / Real.log 2) := by
  rw [beec_capacity hε0 hε1 hq0 hq1]
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [mul_div_assoc]
  congr 1
  rw [sub_div, div_self hlog2]

/-- BEEC capacity is non-negative. -/
theorem beec_capacity_nonneg {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    0 ≤ channelCapacity (beec ε q hε0.le hε1.le hq0.le hq1.le) := by
  rw [beec_capacity hε0 hε1 hq0 hq1]
  have hqle : InformationTheory.BinaryEntropy.h q ≤ Real.log 2 :=
    InformationTheory.BinaryEntropy.h_le_log_two hq0.le hq1.le
  have h1e : (0 : ℝ) ≤ 1 - ε := by linarith
  exact mul_nonneg h1e (by linarith)

/-- BEEC capacity is at most `(1 - ε)·log 2` (the BEC capacity): adding errors
    can only reduce capacity relative to pure erasures. -/
theorem beec_capacity_le_bec {ε q : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    channelCapacity (beec ε q hε0.le hε1.le hq0.le hq1.le) ≤ (1 - ε) * Real.log 2 := by
  rw [beec_capacity hε0 hε1 hq0 hq1]
  have hqnn : 0 ≤ InformationTheory.BinaryEntropy.h q :=
    InformationTheory.BinaryEntropy.h_nonneg hq0.le hq1.le
  have h1e : (0 : ℝ) ≤ 1 - ε := by linarith
  nlinarith [mul_nonneg h1e hqnn]

/-! ## Unification with the BEC and BSC capacities

The capacity formula degenerates to the two channels already in the gallery.
These are the *formula-level* limits (the channels `beec ε 0 _` and `beec 0 q _`
lie on the boundary of the strict-parameter regime, so we record the algebraic
identity of the capacity expressions). -/

/-- **No-error limit `q → 0`:** the BEEC capacity formula becomes the BEC formula
    `(1 - ε)·log 2` (cf. `ShannonChannelCodingBEC.bec_capacity`). -/
theorem beec_capacity_eq_bec_formula (ε : ℝ) :
    (1 - ε) * (Real.log 2 - InformationTheory.BinaryEntropy.h 0) = (1 - ε) * Real.log 2 := by
  rw [InformationTheory.BinaryEntropy.h_zero]; ring

/-- **No-erasure limit `ε → 0`:** the BEEC capacity formula becomes the BSC
    formula `log 2 - h(q)` (cf. `ShannonChannelCodingOQ02.bsc_capacity_proved`). -/
theorem beec_capacity_eq_bsc_formula (q : ℝ) :
    (1 - 0) * (Real.log 2 - InformationTheory.BinaryEntropy.h q)
      = Real.log 2 - InformationTheory.BinaryEntropy.h q := by
  ring

/-- **Useless-BSC limit `q → 1/2`:** when the un-erased sub-channel is a fair coin
    the whole channel carries no information: capacity `= 0`. -/
theorem beec_capacity_eq_zero_at_half (ε : ℝ) :
    (1 - ε) * (Real.log 2 - InformationTheory.BinaryEntropy.h (1 / 2)) = 0 := by
  rw [InformationTheory.BinaryEntropy.h_half]; ring

-- Axiom audit: the BEEC capacity result is proved from first principles.
-- (The parent `ShannonChannelCoding` import carries `channel_coding_achievability`
-- and `channel_coding_converse` in scope, but the capacity value below does not
-- invoke them.)
#print axioms beec_capacity
#print axioms beec_uniform_mi
#print axioms beec_mi_le_general

end InformationTheory.ChannelCoding.BEEC
