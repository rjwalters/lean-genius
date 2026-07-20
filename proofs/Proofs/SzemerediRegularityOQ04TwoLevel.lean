/-
  Szemerédi Regularity Lemma — OQ-04: the packaged two-level AFKS conclusion.

  The Alon–Fischer–Krivelevich–Szegedy strong regularity lemma outputs a *two-level*
  partition:

    (i)   a fine partition `Wparts` that **refines** a coarse partition `Vparts`;
    (ii)  the coarse partition `Vparts` is `ε`-regular;
    (iii) `Wparts` is `E(k)`-regular on all but `ε·C(ℓ,2)` of its pairs, where the
          fine tolerance `E : ℕ → ℚ` is chosen *after* seeing the coarse size
          `k = |Vparts|` (dependent tolerance) and is stronger, `E(k) ≤ ε`.

  Every prior OQ-04 file supplied an *ingredient* of the proof — the energy-increment
  step (`SzemerediRegularityOQ04Assembly`, the sharp `2×2` gain `partitionEnergy_prod_gain_eps4`),
  the finiteness/termination engine (`SzemerediRegularityOQ04`,
  `partitionEnergy_no_infinite_increments`, `afks_regular_step_within_bound`), the tolerance
  monotonicity of regularity (`SzemerediRegularityOQ04Tolerance`), and the AFKS-specific
  mixed fine-regularity predicate with its bridges (`SzemerediRegularityOQ04ToleranceBridge`,
  `IsAFKSFineRegular`).  **None of them states the two-level conclusion itself as a single
  packaged proposition.**  The `state.md` "What remains open" item 2 — *"spell out the AFKS
  conclusion … in Lean, with the dependent tolerance `E : ℕ → (0,1]` threaded correctly"* —
  is exactly that packaging, and this file discharges it.

  Contents:

  * `IsRefinement Wparts Vparts` — the block-refinement relation: every fine block sits
    inside some coarse block.  With `isRefinement_refl`/`isRefinement_trans` it is a
    preorder on partitions (the (i) clause).
  * `IsAFKSTwoLevel G ε E Vparts Wparts` — the packaged two-level AFKS conclusion,
    combining (i)+(ii)+(iii) with the dependent tolerance `E (Vparts.card)`.
  * `isRegularPartition_coarse_of_afksTwoLevel` — the coarse level is `ε`-regular
    (projection of clause (ii)).
  * `isRegularPartition_fine_of_afksTwoLevel` — **both levels are `ε`-regular**: the fine
    level, built to the stronger dependent tolerance `E(k) ≤ ε`, automatically satisfies
    the coarse `ε`-regularity demand (via the `ToleranceBridge` bridge-up).  This is the
    defining feature of the strong lemma — a coarse regular partition *and* a refinement
    that is still regular, only much more finely.
  * `isAFKSTwoLevel_of_regular_refinement` — the **builder**: a coarse `ε`-regular partition
    together with any genuinely `E(k)`-regular refinement (`E(k) ≤ ε`) assembles into the
    two-level conclusion (this is what the outer AFKS loop produces at its regular step).
  * `isAFKSTwoLevel_mono_coarse` — the conclusion is monotone in the coarse tolerance `ε`.

  Everything is elementary order/set arithmetic over the `Szemeredi.Core` definitions and the
  already-verified `ToleranceBridge`/`Tolerance` monotonicity lemmas — no energy machinery.
  This is *statement-level* progress (item 2); the analytic energy-increment core (item 1) and
  the outer-loop assembly that actually *produces* such a partition for every graph (item 3)
  live in the sibling files and remain the substantive open crux.

  0 axioms, 0 sorries.
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularityOQ04Tolerance
import Proofs.SzemerediRegularityOQ04ToleranceBridge

namespace Szemeredi.RegularityOQ04TwoLevel

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Tolerance
  Szemeredi.RegularityOQ04ToleranceBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE BLOCK-REFINEMENT RELATION (clause (i))
-- ═══════════════════════════════════════════════════════════════════

/-- **Block refinement.**  `Wparts` refines `Vparts` when every fine block `W ∈ Wparts`
    is contained in some coarse block `Vp ∈ Vparts`.  This is the standard partition
    refinement order restricted to the block-containment witness the AFKS statement needs
    (clause (i): `W` refines `V`). -/
def IsRefinement (Wparts Vparts : Finset (Finset V)) : Prop :=
  ∀ W ∈ Wparts, ∃ Vp ∈ Vparts, W ⊆ Vp

/-- Refinement is reflexive: every partition refines itself (each block sits inside
    itself). -/
theorem isRefinement_refl (parts : Finset (Finset V)) : IsRefinement parts parts :=
  fun W hW => ⟨W, hW, subset_rfl⟩

/-- Refinement is transitive: a refinement of a refinement is a refinement.  If every
    `W`-block sits in a `U`-block and every `U`-block sits in a `V`-block, then every
    `W`-block sits in a `V`-block. -/
theorem isRefinement_trans {Wparts Uparts Vparts : Finset (Finset V)}
    (hWU : IsRefinement Wparts Uparts) (hUV : IsRefinement Uparts Vparts) :
    IsRefinement Wparts Vparts := by
  intro W hW
  obtain ⟨U, hU, hWU'⟩ := hWU W hW
  obtain ⟨Vp, hVp, hUV'⟩ := hUV U hU
  exact ⟨Vp, hVp, hWU'.trans hUV'⟩

/-- The empty fine partition trivially refines anything (vacuously). -/
theorem isRefinement_empty (Vparts : Finset (Finset V)) :
    IsRefinement (∅ : Finset (Finset V)) Vparts := by
  intro W hW
  simp at hW

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE PACKAGED TWO-LEVEL AFKS CONCLUSION (clauses (i)+(ii)+(iii))
-- ═══════════════════════════════════════════════════════════════════

/-- **The two-level AFKS conclusion, packaged.**  A coarse partition `Vparts` and a fine
    partition `Wparts` form an *AFKS two-level partition* at coarse tolerance `ε` with
    dependent fine tolerance `E : ℕ → ℚ` when:

    * `coarseRegular` — the coarse partition `Vparts` is `ε`-regular (clause (ii));
    * `refines` — `Wparts` refines `Vparts` (clause (i));
    * `fineRegular` — `Wparts` is AFKS-fine-regular at coarse budget `ε` and *fine*
      tolerance `E (Vparts.card)`: all but `ε·C(ℓ,2)` of its pairs are `E(k)`-regular,
      with `k = |Vparts|` the coarse size — the dependent tolerance chosen *after* seeing
      the coarse partition (clause (iii)).

    This is exactly the strong (AFKS) regularity lemma's output as a single proposition.
    The dependent tolerance is threaded by evaluating `E` at `Vparts.card`, so the fine
    level's guarantee genuinely depends on the coarse size. -/
structure IsAFKSTwoLevel (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℚ) (E : ℕ → ℚ) (Vparts Wparts : Finset (Finset V)) : Prop where
  /-- The coarse partition is `ε`-regular (clause (ii)). -/
  coarseRegular : IsRegularPartition G ε Vparts
  /-- The fine partition refines the coarse one (clause (i)). -/
  refines : IsRefinement Wparts Vparts
  /-- The fine partition is `E(k)`-regular on all but `ε·C(ℓ,2)` pairs (clause (iii)),
      with the dependent tolerance evaluated at the coarse size `k = |Vparts|`. -/
  fineRegular : IsAFKSFineRegular G ε (E Vparts.card) Wparts

/-- **Coarse projection.**  The coarse level of an AFKS two-level partition is `ε`-regular. -/
theorem isRegularPartition_coarse_of_afksTwoLevel (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℚ} {E : ℕ → ℚ} {Vparts Wparts : Finset (Finset V)}
    (h : IsAFKSTwoLevel G ε E Vparts Wparts) :
    IsRegularPartition G ε Vparts :=
  h.coarseRegular

/-- **Both levels are `ε`-regular.**  When the dependent fine tolerance is at least as
    strong as the coarse one (`E (Vparts.card) ≤ ε` — the AFKS requirement), the fine
    partition `Wparts`, built to the stronger tolerance, *automatically* satisfies the
    coarse `ε`-regularity demand.  Thus an AFKS two-level partition delivers a coarse
    `ε`-regular partition **and** an `ε`-regular refinement of it — the defining strength
    of the strong lemma over the classical one.  Proof: the fine clause (iii) is
    `IsAFKSFineRegular` at fine tolerance `E(k)`; bridge up (`ToleranceBridge`) turns that
    into `IsRegularPartition G ε Wparts` under `E(k) ≤ ε`. -/
theorem isRegularPartition_fine_of_afksTwoLevel (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℚ} {E : ℕ → ℚ} {Vparts Wparts : Finset (Finset V)}
    (h : IsAFKSTwoLevel G ε E Vparts Wparts)
    (hEε : E (Vparts.card) ≤ ε) :
    IsRegularPartition G ε Wparts :=
  isRegularPartition_of_afksFineRegular G h.fineRegular hEε

/-- **Builder.**  Assemble the two-level conclusion from its pieces: a coarse `ε`-regular
    partition `Vparts`, a refinement `Wparts` of it, and a genuine `E(k)`-regularity of
    `Wparts` at the stronger tolerance `E(k) ≤ ε`.  The `E(k)`-regular refinement is
    upgraded to the AFKS mixed predicate by bridge-down (`afksFineRegular_of_isRegularPartition`).
    This is the shape the outer AFKS loop produces at the regular step it terminates in. -/
theorem isAFKSTwoLevel_of_regular_refinement (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℚ} {E : ℕ → ℚ} {Vparts Wparts : Finset (Finset V)}
    (hcoarse : IsRegularPartition G ε Vparts)
    (href : IsRefinement Wparts Vparts)
    (hfine : IsRegularPartition G (E (Vparts.card)) Wparts)
    (hEε : E (Vparts.card) ≤ ε) :
    IsAFKSTwoLevel G ε E Vparts Wparts where
  coarseRegular := hcoarse
  refines := href
  fineRegular := afksFineRegular_of_isRegularPartition G hfine hEε

/-- **Monotone in the coarse tolerance.**  Enlarging the coarse tolerance `ε ≤ ε'`
    preserves the two-level conclusion (same partitions, same dependent tolerance `E`):
    the coarse regularity relaxes (`isRegularPartition_mono`), the refinement is unchanged,
    and the fine mixed predicate relaxes its budget (`afksFineRegular_mono_coarse`). -/
theorem isAFKSTwoLevel_mono_coarse (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' : ℚ} {E : ℕ → ℚ} {Vparts Wparts : Finset (Finset V)}
    (h : IsAFKSTwoLevel G ε E Vparts Wparts) (hεε' : ε ≤ ε') :
    IsAFKSTwoLevel G ε' E Vparts Wparts where
  coarseRegular := isRegularPartition_mono G h.coarseRegular hεε'
  refines := h.refines
  fineRegular := afksFineRegular_mono_coarse G h.fineRegular hεε'

end Szemeredi.RegularityOQ04TwoLevel
