/-
  Jensen's Diamond Principle implies the Continuum Hypothesis
  (`Proofs/DiamondImpliesCH.lean`, slug `fodor-pressing-down-oq-02`)

  This entry answers the open-question follow-up of `fodor-pressing-down`:
  *what does the combinatorial guessing principle `◇` (diamond) buy us?*  The
  classical answer is **`◇ ⟹ CH`**: a single guessing sequence on `ω₁` already
  forces `2^{ℵ₀} ≤ ℵ₁`.

  `◇` (Jensen, 1972) postulates a sequence `⟨A_α : α < ω₁⟩` with `A_α ⊆ α`
  such that for *every* `X ⊆ ω₁` the *guessing set*
  `{α < ω₁ | X ∩ α = A_α}` is **stationary** in `ω₁`.  We take `◇` itself as
  the hypothesis (constructing such a sequence requires `V = L`, which is a
  *consistency* statement, not a theorem of `ZFC`); the implication
  `◇ ⟹ CH` below is a genuine, assumption-free theorem of `ZFC`.

  ## Proof outline

  1. `isClubBelow_Ioo_omega`: the tail `{β | ω < β < ω₁}` is a club below `ω₁`.
     (Closed: an accumulation point of the tail lies above some tail member,
     hence above `ω`.  Unbounded: `max α ω + 1` works.)
  2. `IsDiamondSeq.guesses`: for any `X ⊆ Iio ω`, the guessing set is
     stationary, hence meets the tail club, producing an `α` with `ω < α` and
     `seq α = X`.  (Here `X ∩ Iio α = X` because `X ⊆ Iio ω ⊆ Iio α`.)
  3. `IsDiamondSeq.powerset_omega_inj`: `X ↦ (chosen α)` injects
     `𝒫(Iio ω)` into `Iio ω₁` (distinct `X` give distinct `seq α`, hence
     distinct `α`).
  4. `diamond_continuum_le`: cardinal bookkeeping turns the injection into
     `𝔠 = 2^{ℵ₀} ≤ ℵ₁` (working one universe up — sets of ordinals live in
     `Type 1` — and descending with `Cardinal.lift_le`).
  5. `diamond_CH`: combined with the `ZFC` theorem `ℵ₁ ≤ 𝔠` we get `𝔠 = ℵ₁`.

  ## Status

  - 0 sorries, 0 `axiom` declarations, 0 structure-encoded assumptions.
  - `◇` is a *hypothesis* (`IsDiamondSeq seq`), not an axiom: the theorems are
    implications, fully machine-checked over Mathlib.
-/

import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic
import Proofs.Club.Basic

open Cardinal Ordinal Set
open scoped Cardinal Ordinal

namespace DiamondImpliesCH

/-! ### The Diamond principle as a hypothesis -/

/-- A `◇`-sequence on `ω₁`: a family `seq α ⊆ α` such that every subset `X` of
`ω₁` is *guessed* on a stationary set, i.e. `{α < ω₁ | X ∩ α = seq α}` is
stationary below `ω₁`.  This is Jensen's combinatorial principle `◇`. -/
def IsDiamondSeq (seq : Ordinal.{0} → Set Ordinal.{0}) : Prop :=
  (∀ α, seq α ⊆ Iio α) ∧
    ∀ X : Set Ordinal.{0}, X ⊆ Iio ω₁ →
      IsStationaryBelow {α | α < ω₁ ∧ X ∩ Iio α = seq α} ω₁

/-! ### The tail club `{β | ω < β < ω₁}` -/

/-- The ordinals strictly between `ω` and `ω₁` form a club below `ω₁`.  We use
this to upgrade "stationary" (meets every club) into "contains an ordinal
above `ω`", which is what is needed to guess countable sets. -/
theorem isClubBelow_Ioo_omega :
    IsClubBelow {β : Ordinal.{0} | ω < β ∧ β < ω₁} ω₁ where
  subset_Iio := fun _ hβ => hβ.2
  closed := by
    rw [isClosedBelow_iff]
    intro p hp hAcc
    refine ⟨?_, hp⟩
    obtain ⟨s, hsmem, _, hsp⟩ := hAcc.forall_lt 0 hAcc.pos
    exact hsmem.1.trans hsp
  unbounded := by
    intro α hα
    refine ⟨max α ω + 1, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact lt_of_le_of_lt (le_max_right α ω) (lt_add_one _)
    · exact (isSuccLimit_omega 1).succ_lt (max_lt hα omega0_lt_omega1)
    · exact lt_of_le_of_lt (le_max_left α ω) (lt_add_one _)
    · exact (isSuccLimit_omega 1).succ_lt (max_lt hα omega0_lt_omega1)

/-! ### The guessing lemma -/

/-- **Guessing of countable sets.**  A `◇`-sequence guesses every `X ⊆ Iio ω`:
there is some `α` with `ω < α < ω₁` and `seq α = X`.  This is the heart of the
argument — the guessing happens above `ω`, so `X ∩ Iio α = X`. -/
theorem IsDiamondSeq.guesses {seq : Ordinal → Set Ordinal} (h : IsDiamondSeq seq)
    {X : Set Ordinal.{0}} (hX : X ⊆ Iio ω) : ∃ α, ω < α ∧ α < ω₁ ∧ seq α = X := by
  have hXω₁ : X ⊆ Iio ω₁ := hX.trans (Iio_subset_Iio omega0_lt_omega1.le)
  obtain ⟨α, hαS, hαC⟩ := h.2 X hXω₁ _ isClubBelow_Ioo_omega
  obtain ⟨hαω₁, hαeq⟩ := hαS
  obtain ⟨hωα, _⟩ := hαC
  refine ⟨α, hωα, hαω₁, ?_⟩
  have hXsub : X ⊆ Iio α := hX.trans (Iio_subset_Iio hωα.le)
  rw [← hαeq, Set.inter_eq_left.mpr hXsub]

/-! ### The injection `𝒫(Iio ω) ↪ Iio ω₁` -/

/-- For `X ⊆ Iio ω`, the chosen ordinal `< ω₁` that the sequence uses to guess
`X`.  Packaged as an element of the subtype `Iio ω₁`. -/
noncomputable def IsDiamondSeq.guessIndex {seq : Ordinal → Set Ordinal}
    (h : IsDiamondSeq seq) (X : ↥(𝒫 (Iio (ω : Ordinal.{0})))) : ↥(Iio ω₁) :=
  ⟨Classical.choose (h.guesses X.2), (Classical.choose_spec (h.guesses X.2)).2.1⟩

/-- The guessing index is injective: distinct subsets of `Iio ω` are guessed at
distinct ordinals, because `seq` recovers the subset from the ordinal. -/
theorem IsDiamondSeq.guessIndex_injective {seq : Ordinal → Set Ordinal}
    (h : IsDiamondSeq seq) : Function.Injective h.guessIndex := by
  intro X Y hXY
  have hX := (Classical.choose_spec (h.guesses X.2)).2.2
  have hY := (Classical.choose_spec (h.guesses Y.2)).2.2
  have hαeq : Classical.choose (h.guesses X.2) = Classical.choose (h.guesses Y.2) :=
    Subtype.ext_iff.mp hXY
  apply Subtype.ext
  rw [← hX, ← hY, hαeq]

/-- Cardinal form of the injection: `#𝒫(Iio ω) ≤ #(Iio ω₁)`. -/
theorem IsDiamondSeq.mk_powerset_le {seq : Ordinal → Set Ordinal}
    (h : IsDiamondSeq seq) :
    #(↥(𝒫 (Iio (ω : Ordinal.{0})))) ≤ #(↥(Iio (ω₁ : Ordinal.{0}))) :=
  Cardinal.mk_le_of_injective h.guessIndex_injective

/-! ### Cardinal bookkeeping: `◇ ⟹ CH` -/

/-- `#(Iio ω) = lift ℵ₀`: there are countably many ordinals below `ω`. -/
theorem mk_Iio_omega : #(↥(Iio (ω : Ordinal.{0}))) = Cardinal.lift.{1, 0} ℵ₀ := by
  rw [mk_Iio_ordinal, card_omega0]

/-- `#(Iio ω₁) = lift ℵ₁`: there are `ℵ₁`-many ordinals below `ω₁`. -/
theorem mk_Iio_omega1 : #(↥(Iio (ω₁ : Ordinal.{0}))) = Cardinal.lift.{1, 0} ℵ₁ := by
  rw [mk_Iio_ordinal, card_omega]

/-- **Diamond implies the continuum bound.**  If a `◇`-sequence exists then
`𝔠 ≤ ℵ₁`, i.e. there are at most `ℵ₁` subsets of `ℕ`. -/
theorem diamond_continuum_le {seq : Ordinal → Set Ordinal} (h : IsDiamondSeq seq) :
    (𝔠 : Cardinal.{0}) ≤ ℵ₁ := by
  -- The injection lives one universe up; lift the target inequality back down.
  have key := h.mk_powerset_le
  rw [Cardinal.mk_powerset, mk_Iio_omega, mk_Iio_omega1, ← Cardinal.lift_two_power,
    two_power_aleph0] at key
  exact Cardinal.lift_le.mp key

/-- **Diamond implies the Continuum Hypothesis.**  If a `◇`-sequence exists then
`𝔠 = ℵ₁`: the cardinality of the continuum is exactly the first uncountable
cardinal.  (`ℵ₁ ≤ 𝔠` is a theorem of `ZFC`; `◇` supplies the reverse bound.) -/
theorem diamond_CH {seq : Ordinal → Set Ordinal} (h : IsDiamondSeq seq) :
    (𝔠 : Cardinal.{0}) = ℵ₁ :=
  le_antisymm (diamond_continuum_le h) aleph_one_le_continuum

/-- Restatement: under `◇`, every uncountable set of reals has size `ℵ₁`
(equivalently, `CH` holds in the form `2^{ℵ₀} = ℵ₁`). -/
theorem diamond_two_pow_aleph0 {seq : Ordinal → Set Ordinal} (h : IsDiamondSeq seq) :
    (2 : Cardinal.{0}) ^ ℵ₀ = ℵ₁ := by
  rw [two_power_aleph0]; exact diamond_CH h

end DiamondImpliesCH
