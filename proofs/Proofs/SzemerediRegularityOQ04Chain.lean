/-
  Szemerédi Regularity Lemma — OQ-04: the recursive chain construction (S21).

  The outer AFKS loop (`exists_afksTwoLevel_of_dichotomy_both`, S19) consumes a
  *chain* `parts : ℕ → Finset (Finset V)` given in advance, and the single-step
  realization (`exists_witnessed_next_of_not_afksFineRegular`, S20) produces,
  from one non-fine-regular partition, one successor.  What was still missing is
  the recursion that turns the step into the chain — the `Classical.choose` +
  iteration glue S20's docstring names as the outstanding brick.  This file
  supplies that recursion, in a form that isolates the one hypothesis the
  recursion genuinely still lacks (re-equitization):

  * `exists_fine_of_potential_oracle` — the ABSTRACT chain construction: for any
    invariant `Inv`, target `Fine`, and `[0,1]`-bounded potential `f` on
    `Inv`-states, an oracle that carries every non-`Fine` `Inv`-state to an
    `Inv`-state with `f`-gain `≥ δ > 0` forces the existence of an `Inv`-state
    that IS `Fine`.  Proof: if not, `Subtype.val`-iterating the chosen successor
    map from any start state gives a sequence along which `f` climbs by `δ`
    every step, contradicting the `[0,1]`-potential termination engine
    (`no_infinite_energy_increments`).  No graph theory at all.

  * `partitionEnergy_gain_of_witnessed_both` — the per-step energy gain of the
    two-shape witnessed step, factored OUT of the S19 iteration count
    (`afks_sharp_energy_iteration_count_of_witness_both` inlined it): EITHER
    witness shape at step `n` raises `partitionEnergy` by the sharp uniform
    floor `eps⁴·m²/n²` (for `eps ≤ 1`).

  * `exists_energy_next_of_not_afksFineRegular` — S20's realization restated in
    ENERGY form: a non-fine-regular equitable partition with mass floor `m`
    admits a successor that covers, is pairwise disjoint, refines whatever the
    parent refines, and carries `partitionEnergy` gain `≥ E⁴·m²/n²`.  (The
    successor is the bare split, so equitability and the mass floor are NOT
    asserted for it — that is exactly the re-equitization gap.)

  * `exists_afksFineRegular_of_maintained_oracle` — the concrete chain: from a
    seed partition satisfying the loop invariant (covering, pairwise disjoint,
    refining `Vparts`, equitable, mass floor `m`) and a MAINTAINED step oracle —
    one that returns a successor satisfying the SAME invariant along with any
    positive energy gain `δ` — some partition satisfying the invariant is
    AFKS-fine-regular.

  * `exists_afksTwoLevel_of_maintained_oracle` — the capstone: with an
    `ε`-regular coarse partition `Vparts` and the maintained oracle at fine
    tolerance `E (Vparts.card)`, the full two-level AFKS conclusion
    `IsAFKSTwoLevel` holds for some fine partition.

  Comparing the oracle the capstone needs with what
  `exists_energy_next_of_not_afksFineRegular` already delivers, the WHOLE
  remaining gap of the OQ-04 program is now one analytic statement: re-equitize
  the bare split (restoring equitability and the mass floor, staying a
  refinement) while keeping a positive fraction of its energy gain — the
  classical AFKS re-equitization bookkeeping, nothing else.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04OuterBoth
import Proofs.SzemerediRegularityOQ04StepRealize

namespace Szemeredi.RegularityOQ04Chain

open Classical
open Szemeredi.Core Szemeredi.Regularity Szemeredi.EnergyIncrement
  Szemeredi.RegularityOQ04 Szemeredi.RegularityOQ04Energy
  Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04StepThree
  Szemeredi.RegularityOQ04DefectGain Szemeredi.RegularityOQ04Outer
  Szemeredi.RegularityOQ04TwoLevel Szemeredi.RegularityOQ04ToleranceBridge
  Szemeredi.RegularityOQ04OuterBoth Szemeredi.RegularityOQ04StepRealize

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE ABSTRACT CHAIN CONSTRUCTION
-- ═══════════════════════════════════════════════════════════════════

/-- **Abstract chain construction from an invariant-maintaining oracle.**  Let
    `Inv` be an invariant, `Fine` a target predicate, and `f` a potential that
    is `[0,1]`-bounded on `Inv`-states.  Suppose every `Inv`-state that is not
    `Fine` can be carried to another `Inv`-state with potential gain at least
    `δ > 0`.  Then from any starting `Inv`-state some `Inv`-state is `Fine`.

    This is the `Classical.choose` + iteration glue of the AFKS outer loop,
    stated with no graph theory at all: were no `Inv`-state `Fine`, the chosen
    successor map would iterate from the seed into an infinite chain along
    which `f` gains `δ` at every step — impossible for a `[0,1]`-valued
    potential (`no_infinite_energy_increments`). -/
theorem exists_fine_of_potential_oracle {α : Type*}
    (Inv Fine : α → Prop) (f : α → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (h0 : ∀ q, Inv q → 0 ≤ f q) (h1 : ∀ q, Inv q → f q ≤ 1)
    (q₀ : α) (hq₀ : Inv q₀)
    (horacle : ∀ q, Inv q → ¬ Fine q → ∃ q', Inv q' ∧ f q + δ ≤ f q') :
    ∃ q, Inv q ∧ Fine q := by
  by_contra hcon
  have hnf : ∀ q, Inv q → ¬ Fine q := fun q hq hf => hcon ⟨q, hq, hf⟩
  -- The chosen successor map on the subtype of invariant states.
  have hstep : ∀ q : {q : α // Inv q}, ∃ q' : {q : α // Inv q},
      f q.val + δ ≤ f q'.val := by
    rintro ⟨q, hq⟩
    obtain ⟨q', hq', hgain⟩ := horacle q hq (hnf q hq)
    exact ⟨⟨q', hq'⟩, hgain⟩
  choose next hnext using hstep
  -- Iterating from the seed gives an infinite `δ`-increment chain: impossible.
  exact no_infinite_energy_increments
    (fun n => f ((next^[n] (⟨q₀, hq₀⟩ : {q : α // Inv q})).val)) δ hδ
    (fun n => h0 _ (next^[n] ⟨q₀, hq₀⟩).prop)
    (fun n => h1 _ (next^[n] ⟨q₀, hq₀⟩).prop)
    (fun n => by rw [Function.iterate_succ_apply']; exact hnext _)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE PER-STEP ENERGY GAIN OF THE TWO-SHAPE WITNESSED STEP
-- ═══════════════════════════════════════════════════════════════════

/-- **Energy gain of a witnessed step, either shape.**  A step of a chain
    witnessed by the symmetric 4-piece shape (`IsWitnessedSharpStep`) or by
    the asymmetric 3-piece shape (`IsWitnessedSharpStep3`) raises
    `partitionEnergy` by at least the sharp uniform floor `eps⁴·m²/n²`
    (for `eps ≤ 1`, the 3-piece `eps³` gain dominates the common `eps⁴`
    budget).  This is the per-step content of
    `afks_sharp_energy_iteration_count_of_witness_both` (S19), factored out
    so a single step can feed the recursive chain construction. -/
theorem partitionEnergy_gain_of_witnessed_both
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (hε : 0 < eps) (hε1 : eps ≤ 1) (hm : 0 < m)
    (hwit : IsWitnessedSharpStep G parts n eps m ∨
      IsWitnessedSharpStep3 G parts n eps m) :
    partitionEnergy G (parts n) + eps ^ 4 * m ^ 2 / (Fintype.card V : ℚ) ^ 2 ≤
      partitionEnergy G (parts (n + 1)) := by
  rcases hwit with hstep | hstep
  · -- Symmetric 4-piece step: the sharp `eps⁴` product gain.
    obtain ⟨R, A, B, A₁, A₂, B₁, B₂, hpn, hpn1, hAu, hBu, hdA, hdB,
      hAins, hBR, hA1, hA2, hB1, hB2, hmA, hmB, hcA, hcB, hdev⟩ := hstep
    rw [hpn, hpn1]
    have hgain := partitionEnergy_prod_gain_eps4 G R A B A₁ A₂ B₁ B₂
      hAu hBu hdA hdB hAins hBR hA1 hA2 hB1 hB2 eps hε.le hcA hcB hdev
    have hmass : m ^ 2 ≤ (A.card : ℚ) * B.card := by
      nlinarith [hmA, hmB, hm.le]
    have hfloor : eps ^ 4 * m ^ 2 / (Fintype.card V : ℚ) ^ 2 ≤
        eps ^ 4 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 := by
      gcongr
    linarith [hgain, hfloor]
  · -- Asymmetric 3-piece step: the `eps³` defect gain dominates `eps⁴`.
    obtain ⟨R, A, B, B₁, B₂, hpn, hpn1, hBu, hdB, hAins, hBR, hAins',
      hB₁ins, hB₂R, hmA, hmB, hfl, hdev⟩ := hstep
    rw [hpn, hpn1]
    have hApos : 0 < (A.card : ℚ) := lt_of_lt_of_le hm hmA
    have hBpos : 0 < (B.card : ℚ) := lt_of_lt_of_le hm hmB
    have hgain := partitionEnergy_step3_refinement_gain G R A B B₁ B₂
      hBu hdB hAins hBR hAins' hB₁ins hB₂R eps hε hApos hBpos hfl hdev
    have hmass : m ^ 2 ≤ (A.card : ℚ) * B.card := by
      nlinarith [hmA, hmB, hm.le]
    have heps3 : (0 : ℚ) ≤ eps ^ 3 := by positivity
    have h43 : eps ^ 4 ≤ eps ^ 3 := by
      nlinarith [mul_nonneg heps3 (sub_nonneg.mpr hε1)]
    have hnum : eps ^ 4 * m ^ 2 ≤ eps ^ 3 * ((A.card : ℚ) * B.card) :=
      mul_le_mul h43 hmass (sq_nonneg m) heps3
    have hfloor : eps ^ 4 * m ^ 2 / (Fintype.card V : ℚ) ^ 2 ≤
        eps ^ 3 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hnum (by positivity)
    linarith [hgain, hfloor]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE SINGLE STEP IN ENERGY FORM
-- ═══════════════════════════════════════════════════════════════════

/-- **The single-step realization, in energy form.**  An equitable, pairwise
    disjoint, covering partition with per-part mass floor `m` that is not
    AFKS-fine-regular admits a successor partition that covers, is pairwise
    disjoint, refines every coarse partition the parent refines, and carries
    a `partitionEnergy` gain of at least the sharp uniform floor `E⁴·m²/n²`.

    The successor is the bare split of `exists_witnessed_next_of_not_afksFineRegular`
    (S20); its witnessed step is converted to the energy gain by
    `partitionEnergy_gain_of_witnessed_both` through the two-term chain
    `q, q', q', …`.  Equitability and the mass floor are NOT asserted for the
    successor — a bare split genuinely loses them; restoring them at a bounded
    energy cost is precisely the re-equitization gap this file isolates. -/
theorem exists_energy_next_of_not_afksFineRegular
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε E m : ℚ)
    (hε : 0 ≤ ε) (hE : 0 < E) (hE1 : E ≤ 1) (hm : 0 < m)
    (q : Finset (Finset V))
    (hcover : ∀ v : V, ∃ P ∈ q, v ∈ P)
    (hdisj : ∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q)
    (hequit : ∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1)
    (hmass : ∀ P ∈ q, m ≤ (P.card : ℚ))
    (hnot : ¬ IsAFKSFineRegular G ε E q) :
    ∃ q' : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
      (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
      (∀ Vparts : Finset (Finset V),
        IsRefinement q Vparts → IsRefinement q' Vparts) ∧
      partitionEnergy G q + E ^ 4 * m ^ 2 / (Fintype.card V : ℚ) ^ 2 ≤
        partitionEnergy G q' := by
  obtain ⟨q', hc, hd, hr, hwit⟩ :=
    exists_witnessed_next_of_not_afksFineRegular G ε E m hε hE hm q
      hcover hdisj hequit hmass hnot
  refine ⟨q', hc, hd, hr, ?_⟩
  -- Thread the witnessed step through the two-term chain `q, q', q', …`.
  have h := partitionEnergy_gain_of_witnessed_both G
    (fun i => if i = 0 then q else q') 0 E m hE hE1 hm
    (hwit (fun i => if i = 0 then q else q') 0 (by simp) (by simp))
  simpa using h

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THE CONCRETE CHAIN AND THE TWO-LEVEL CAPSTONE
-- ═══════════════════════════════════════════════════════════════════

/-- **AFKS fine-regularity from a maintained step oracle.**  Let `q₀` satisfy
    the loop invariant — covering, pairwise disjoint, refining the coarse
    partition `Vparts`, equitable, per-part mass floor `m` — and suppose the
    step oracle: every partition satisfying the invariant that is not
    AFKS-fine-regular at `(ε, Ek)` has a successor satisfying the SAME
    invariant with `partitionEnergy` gain at least `δ > 0`.  Then some
    partition satisfying the invariant is AFKS-fine-regular.

    This is the recursive chain construction of the AFKS outer loop.  The
    oracle differs from what `exists_energy_next_of_not_afksFineRegular`
    provides only in the equitability and mass-floor clauses of the successor:
    discharging that difference — re-equitizing the bare split at a bounded
    energy cost — is the single remaining analytic gap of the OQ-04 program. -/
theorem exists_afksFineRegular_of_maintained_oracle
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε Ek m δ : ℚ) (hδ : 0 < δ)
    (Vparts q₀ : Finset (Finset V))
    (hcover₀ : ∀ v : V, ∃ P ∈ q₀, v ∈ P)
    (hdisj₀ : ∀ P Q : Finset V, P ∈ q₀ → Q ∈ q₀ → P ≠ Q → Disjoint P Q)
    (href₀ : IsRefinement q₀ Vparts)
    (hequit₀ : ∀ P Q : Finset V, P ∈ q₀ → Q ∈ q₀ → (P.card : ℤ) - Q.card ≤ 1)
    (hmass₀ : ∀ P ∈ q₀, m ≤ (P.card : ℚ))
    (horacle : ∀ q : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q, v ∈ P) →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q) →
      IsRefinement q Vparts →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1) →
      (∀ P ∈ q, m ≤ (P.card : ℚ)) →
      ¬ IsAFKSFineRegular G ε Ek q →
      ∃ q' : Finset (Finset V),
        (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
        IsRefinement q' Vparts ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → (P.card : ℤ) - Q.card ≤ 1) ∧
        (∀ P ∈ q', m ≤ (P.card : ℚ)) ∧
        partitionEnergy G q + δ ≤ partitionEnergy G q') :
    ∃ q : Finset (Finset V),
      IsRefinement q Vparts ∧ IsAFKSFineRegular G ε Ek q := by
  -- Instantiate the abstract chain construction with the packaged invariant.
  obtain ⟨q, hq, hfine⟩ := exists_fine_of_potential_oracle
    (Inv := fun q : Finset (Finset V) =>
      (∀ v : V, ∃ P ∈ q, v ∈ P) ∧
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q) ∧
      IsRefinement q Vparts ∧
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1) ∧
      (∀ P ∈ q, m ≤ (P.card : ℚ)))
    (Fine := fun q => IsAFKSFineRegular G ε Ek q)
    (f := fun q => partitionEnergy G q) (δ := δ) hδ
    (fun q _ => partitionEnergy_nonneg G q)
    (fun q hq => partitionEnergy_le_one G q hq.1 hq.2.1)
    q₀ ⟨hcover₀, hdisj₀, href₀, hequit₀, hmass₀⟩
    (by
      rintro q ⟨hc, hd, hr, he, hmq⟩ hnot
      obtain ⟨q', hc', hd', hr', he', hm', hgain⟩ :=
        horacle q hc hd hr he hmq hnot
      exact ⟨q', ⟨hc', hd', hr', he', hm'⟩, hgain⟩)
  exact ⟨q, hq.2.2.1, hfine⟩

/-- **The two-level AFKS conclusion from a maintained step oracle.**  With an
    `ε`-regular coarse partition `Vparts`, a seed fine partition satisfying the
    loop invariant, and the maintained step oracle at the dependent fine
    tolerance `E (Vparts.card)` (any positive per-step energy gain `δ`), the
    full two-level conclusion holds: some fine partition refines `Vparts` and
    is AFKS-fine-regular — `IsAFKSTwoLevel G ε E Vparts`.

    Together with `exists_energy_next_of_not_afksFineRegular`, this reduces the
    entire remaining OQ-04 program to the re-equitization statement: convert
    the bare-split successor into an invariant-maintaining one while keeping a
    positive fraction `δ` of its `E⁴·m²/n²` energy gain. -/
theorem exists_afksTwoLevel_of_maintained_oracle
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (m δ : ℚ) (hδ : 0 < δ)
    (Vparts q₀ : Finset (Finset V))
    (hcoarse : IsRegularPartition G ε Vparts)
    (hcover₀ : ∀ v : V, ∃ P ∈ q₀, v ∈ P)
    (hdisj₀ : ∀ P Q : Finset V, P ∈ q₀ → Q ∈ q₀ → P ≠ Q → Disjoint P Q)
    (href₀ : IsRefinement q₀ Vparts)
    (hequit₀ : ∀ P Q : Finset V, P ∈ q₀ → Q ∈ q₀ → (P.card : ℤ) - Q.card ≤ 1)
    (hmass₀ : ∀ P ∈ q₀, m ≤ (P.card : ℚ))
    (horacle : ∀ q : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q, v ∈ P) →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q) →
      IsRefinement q Vparts →
      (∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1) →
      (∀ P ∈ q, m ≤ (P.card : ℚ)) →
      ¬ IsAFKSFineRegular G ε (E Vparts.card) q →
      ∃ q' : Finset (Finset V),
        (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
        IsRefinement q' Vparts ∧
        (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → (P.card : ℤ) - Q.card ≤ 1) ∧
        (∀ P ∈ q', m ≤ (P.card : ℚ)) ∧
        partitionEnergy G q + δ ≤ partitionEnergy G q') :
    ∃ Wparts : Finset (Finset V), IsAFKSTwoLevel G ε E Vparts Wparts := by
  obtain ⟨q, href, hfine⟩ := exists_afksFineRegular_of_maintained_oracle
    G ε (E Vparts.card) m δ hδ Vparts q₀
    hcover₀ hdisj₀ href₀ hequit₀ hmass₀ horacle
  exact ⟨q, { coarseRegular := hcoarse, refines := href, fineRegular := hfine }⟩

end Szemeredi.RegularityOQ04Chain
