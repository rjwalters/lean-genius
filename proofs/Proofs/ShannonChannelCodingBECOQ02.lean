/-
  Operational coding theorem for the Binary Erasure Channel
  (open question shannon-channel-coding-bec-oq-02)

  The base entry `Proofs.ShannonChannelCodingBEC` establishes the
  *information-theoretic* capacity of the binary erasure channel from first
  principles, axiom-free:

        channelCapacity (bec p) = (1 - p) · log 2 nats   (= 1 - p bits).

  That is a statement about a supremum of mutual informations over input
  distributions — it says nothing yet about *codes*.  The open question asks to
  bridge that information-theoretic supremum to the *operational* layer: rates
  that are actually achievable by block codes with vanishing error, and a
  matching converse forbidding reliable communication above capacity.

  The gallery's discrete-memoryless channel framework already provides Shannon's
  two operational theorems as the named results
  `InformationTheory.ChannelCoding.channel_coding_achievability` and
  `…channel_coding_converse` (both stated for an arbitrary `DMChannel` in terms
  of its `channelCapacity`).  In this gallery those two theorems are *axioms* —
  the deep random-coding / Fano arguments are taken as given at the abstract
  level — so any operational statement derived from them is, honestly,
  axiomatized.  What this file contributes is the *specialisation* to the
  concrete BEC: feeding the proved capacity value `(1 - p)·log 2` through the
  abstract operational theorems gives the BEC's operational coding theorem with
  an explicit numerical threshold.

  Results (all by substituting `bec_capacity` into the abstract operational
  theorems):

    * `bec_coding_achievability`       — any rate `0 < R < (1-p)·log 2` (nats) is
                                         achievable: for every `ε > 0`, all long
                                         enough block lengths admit a code of rate
                                         `≥ R` with average error `< ε`.
    * `bec_coding_achievability_bits`  — the textbook form: any bit-rate
                                         `0 < R₂ < 1 - p` is achievable.
    * `bec_coding_converse`            — any rate `R > (1-p)·log 2` is *not*
                                         achievable: the average error is bounded
                                         below by a fixed `δ > 0` for every code.
    * `bec_coding_converse_bits`       — bit-rate form of the converse.

  Together these pin the BEC's *operational* capacity to exactly the
  information-theoretic value `(1-p)·log 2`, closing the loop the open question
  asks for.

  Status: 0 sorries.  Honestly *axiomatized*: every result here inherits
  `channel_coding_achievability` and/or `channel_coding_converse` from the base
  channel-coding framework (plus the ordinary `propext / Classical.choice /
  Quot.sound`).  The BEC capacity value itself (`bec_capacity`) is axiom-free.
-/
import Mathlib
import Proofs.ShannonChannelCodingBEC

namespace InformationTheory.ChannelCoding.BEC

open Filter

variable {p : ℝ}

/-- **Operational achievability for the BEC.**
For any rate `0 < R < (1 - p)·log 2` (in nats), reliable communication is
possible: for every target error `ε > 0`, all sufficiently long block lengths
`n` admit a block code of rate `≥ R` together with a decoder whose average error
probability is `< ε`.

This is the gallery's abstract `channel_coding_achievability` applied to the
binary erasure channel, with the capacity hypothesis discharged by the proved
value `bec_capacity : channelCapacity (bec p) = (1 - p)·log 2`. -/
theorem bec_coding_achievability (hp0 : 0 < p) (hp1 : p < 1)
    {R : ℝ} (hR : 0 < R) (hR_cap : R < (1 - p) * Real.log 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (hn : 0 < n),
      ∃ (code : BlockCode Bool n) (decoder : (Fin n → Option Bool) → Fin code.M),
        R ≤ rate_of_code hn code ∧
        (∑ i : Fin code.M, (1 - ∑ y : Fin n → Option Bool,
          (∏ j : Fin n, (bec p hp0.le hp1.le).W (code.encode i j) (y j)) *
            if decoder y = i then (1 : ℝ) else 0)) / code.M < ε :=
  channel_coding_achievability (bec p hp0.le hp1.le) hR
    (by rw [bec_capacity hp0 hp1]; exact hR_cap)

/-- **Operational converse for the BEC.**
For any rate `R > (1 - p)·log 2` (in nats), reliable communication is impossible:
there is a fixed `δ > 0` such that *every* block code of rate `≥ R` (at every
length) has average error probability `≥ δ`.

This is the gallery's abstract `channel_coding_converse` applied to the BEC, with
the capacity hypothesis discharged by `bec_capacity`. -/
theorem bec_coding_converse (hp0 : 0 < p) (hp1 : p < 1)
    {R : ℝ} (hR : 0 < R) (hR_cap : (1 - p) * Real.log 2 < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (hn : 0 < n)
      (code : BlockCode Bool n) (decoder : (Fin n → Option Bool) → Fin code.M),
        R ≤ rate_of_code hn code →
        δ ≤ (∑ i : Fin code.M, (1 - ∑ y : Fin n → Option Bool,
          (∏ j : Fin n, (bec p hp0.le hp1.le).W (code.encode i j) (y j)) *
            if decoder y = i then (1 : ℝ) else 0)) / code.M :=
  channel_coding_converse (bec p hp0.le hp1.le) hR
    (by rw [bec_capacity hp0 hp1]; exact hR_cap)

/-- **Achievability in bits — the textbook headline.**
Any bit-rate `0 < R₂ < 1 - p` is achievable on the BEC.  Equivalent to
`bec_coding_achievability` with the nat-rate `R = R₂ · log 2`; the rate guarantee
`R₂ · log 2 ≤ rate_of_code` says exactly that the code's bit-rate
`rate_of_code / log 2` is at least `R₂`. -/
theorem bec_coding_achievability_bits (hp0 : 0 < p) (hp1 : p < 1)
    {R₂ : ℝ} (hR : 0 < R₂) (hR_cap : R₂ < 1 - p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in Filter.atTop, ∀ (hn : 0 < n),
      ∃ (code : BlockCode Bool n) (decoder : (Fin n → Option Bool) → Fin code.M),
        R₂ * Real.log 2 ≤ rate_of_code hn code ∧
        (∑ i : Fin code.M, (1 - ∑ y : Fin n → Option Bool,
          (∏ j : Fin n, (bec p hp0.le hp1.le).W (code.encode i j) (y j)) *
            if decoder y = i then (1 : ℝ) else 0)) / code.M < ε := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine bec_coding_achievability hp0 hp1 (by positivity) ?_
  -- R₂ · log 2 < (1 - p) · log 2 since R₂ < 1 - p and log 2 > 0.
  exact mul_lt_mul_of_pos_right hR_cap hlog2

/-- **Converse in bits.**
No bit-rate `R₂ > 1 - p` is achievable on the BEC: a fixed `δ > 0` lower-bounds
the average error of every code whose nat-rate is `≥ R₂ · log 2` (i.e. whose
bit-rate is `≥ R₂`). -/
theorem bec_coding_converse_bits (hp0 : 0 < p) (hp1 : p < 1)
    {R₂ : ℝ} (hR : 0 < R₂) (hR_cap : 1 - p < R₂) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (hn : 0 < n)
      (code : BlockCode Bool n) (decoder : (Fin n → Option Bool) → Fin code.M),
        R₂ * Real.log 2 ≤ rate_of_code hn code →
        δ ≤ (∑ i : Fin code.M, (1 - ∑ y : Fin n → Option Bool,
          (∏ j : Fin n, (bec p hp0.le hp1.le).W (code.encode i j) (y j)) *
            if decoder y = i then (1 : ℝ) else 0)) / code.M := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine bec_coding_converse hp0 hp1 (by positivity) ?_
  -- (1 - p) · log 2 < R₂ · log 2 since 1 - p < R₂ and log 2 > 0.
  exact mul_lt_mul_of_pos_right hR_cap hlog2

end InformationTheory.ChannelCoding.BEC
