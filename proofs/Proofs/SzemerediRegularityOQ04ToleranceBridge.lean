/-
  Szemerédi Regularity Lemma — OQ-04: the AFKS hybrid-regularity bridge.

  The Alon–Fischer–Krivelevich–Szegedy strong regularity lemma outputs a *two-level*
  partition whose fine level `W₁..W_ℓ` has a peculiar mixed guarantee: all but an
  `ε·C(ℓ,2)`-fraction of its pairs are regular *not* at the coarse tolerance `ε`, but
  at the much stronger, dependently-chosen fine tolerance `E = E(k) ≤ ε`.  The
  exceptional **budget** is measured at the coarse `ε`, while the **regularity** each
  good pair enjoys is measured at the fine `E`.  This asymmetric predicate — strong
  regularity, coarse budget — is the exact currency the strong-lemma conclusion (iii)
  produces and the property-testing corollaries consume.

  `SzemerediRegularityOQ04Tolerance` supplied the one-directional monotonicity facts:
  `ε`-regularity is monotone in `ε` (`isEpsilonRegular_mono`), the irregular-pair count
  is antitone in `ε` (`irregularPairs_card_antitone`), and the whole `IsRegularPartition`
  predicate is tolerance-monotone (`isRegularPartition_mono`).  This file packages the
  AFKS-specific mixed predicate and pins down exactly where it sits in the regularity
  hierarchy:

  * `IsAFKSFineRegular G ε E parts` — equitable, with at most `ε·k(k−1)` ordered pairs
    failing the *fine* tolerance `E` (the AFKS fine-level guarantee).
  * `isRegularPartition_of_afksFineRegular` — **the bridge up**: an AFKS-fine-regular
    partition with `E ≤ ε` is automatically a classical `ε`-regular partition.  This is
    why the strong lemma's fine partition satisfies the coarse regularity demand *for
    free*: fewer pairs fail the coarse test than fail the fine one.
  * `afksFineRegular_of_isRegularPartition` — **the bridge down**: a genuinely
    `E`-regular partition (`E ≤ ε`) is AFKS-fine-regular, since its `E`-budget
    `E·k(k−1)` is dominated by the coarse budget `ε·k(k−1)`.  Together with the bridge up
    this sandwiches the hybrid strictly between `E`-regular and `ε`-regular.
  * `afksFineRegular_mono_fine` — relaxing the fine tolerance `E ≤ E'` preserves the
    hybrid (the fine-irregular set only shrinks).
  * `afksFineRegular_mono_coarse` — enlarging the coarse tolerance `ε ≤ ε'` preserves
    the hybrid (the coarse budget only grows).
  * `isRegularPartition_of_isRegularPartition_fine` — the capstone `E`-regular ⟹
    `ε`-regular (`E ≤ ε`) **factored through the hybrid**, exhibiting AFKS-fine-regularity
    as the intermediate object of `isRegularPartition_mono`.

  Everything is elementary order arithmetic over the `Szemeredi.Core` definitions and the
  `SzemerediRegularityOQ04Tolerance` antitonicity lemma — no energy machinery.
-/
import Mathlib
import Proofs.SzemerediCore
import Proofs.SzemerediRegularityOQ04Tolerance

namespace Szemeredi.RegularityOQ04ToleranceBridge

open Classical Szemeredi.Core Szemeredi.RegularityOQ04Tolerance

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `k·(k − 1) ≥ 0` for a natural `k` cast into `ℚ`: the ordered-pair budget factor is
    nonnegative, so scaling it by a larger tolerance only enlarges the budget. -/
private theorem card_mul_pred_nonneg (parts : Finset (Finset V)) :
    (0 : ℚ) ≤ (parts.card : ℚ) * ((parts.card : ℚ) - 1) := by
  rcases Nat.eq_zero_or_pos parts.card with hk | hk
  · simp [hk]
  · have h1 : (1 : ℚ) ≤ (parts.card : ℚ) := by exact_mod_cast hk
    exact mul_nonneg (by positivity) (by linarith)

/-- **AFKS hybrid fine-regularity.**  A partition is *AFKS-fine-regular* at coarse
    tolerance `ε` and fine tolerance `E` if it is equitable and all but at most
    `ε·k(k−1)` of its ordered pairs are regular at the *fine* tolerance `E`.

    This mixes a strong regularity guarantee (`E`, typically `≪ ε`) with the coarse
    exceptional budget (`ε`).  It is precisely the AFKS strong-lemma conclusion (iii):
    the fine partition is `E(k)`-regular on all but `ε·C(ℓ,2)` (unordered) pairs. -/
def IsAFKSFineRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε E : ℚ) (parts : Finset (Finset V)) : Prop :=
  (∀ P Q : Finset V, P ∈ parts → Q ∈ parts → (P.card : ℤ) - Q.card ≤ 1) ∧
  ((parts.product parts).filter (fun pq =>
    pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G E pq.1 pq.2)).card ≤
    ε * ((parts.card : ℚ) * ((parts.card : ℚ) - 1))

/-- **Bridge up.**  An AFKS-fine-regular partition (fine tolerance `E ≤ ε`) is a
    classical `ε`-regular partition.  The exceptional pairs of the coarse `ε`-test are a
    subset of those of the fine `E`-test (`irregularPairs_card_antitone`), so the coarse
    exceptional count is even smaller than the fine one, which already fits the shared
    budget `ε·k(k−1)`.  Equitability is tolerance-free.

    This is the formal reason the strong lemma's fine partition meets the coarse
    regularity requirement automatically. -/
theorem isRegularPartition_of_afksFineRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E : ℚ} {parts : Finset (Finset V)}
    (hfine : IsAFKSFineRegular G ε E parts) (hEε : E ≤ ε) :
    IsRegularPartition G ε parts := by
  obtain ⟨hequit, hcount⟩ := hfine
  refine ⟨hequit, ?_⟩
  calc (((parts.product parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε pq.1 pq.2)).card : ℚ)
      ≤ (((parts.product parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G E pq.1 pq.2)).card : ℚ) := by
        exact_mod_cast irregularPairs_card_antitone G hEε parts
    _ ≤ ε * ((parts.card : ℚ) * ((parts.card : ℚ) - 1)) := hcount

/-- **Bridge down.**  A genuinely `E`-regular partition (`E ≤ ε`) is AFKS-fine-regular at
    coarse tolerance `ε`: its own `E`-budget `E·k(k−1)` is dominated by the coarse budget
    `ε·k(k−1)`.  Combined with `isRegularPartition_of_afksFineRegular`, this sandwiches the
    hybrid between `E`-regular and `ε`-regular. -/
theorem afksFineRegular_of_isRegularPartition (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E : ℚ} {parts : Finset (Finset V)}
    (hE : IsRegularPartition G E parts) (hEε : E ≤ ε) :
    IsAFKSFineRegular G ε E parts := by
  obtain ⟨hequit, hcount⟩ := hE
  refine ⟨hequit, ?_⟩
  refine le_trans hcount ?_
  exact mul_le_mul_of_nonneg_right hEε (card_mul_pred_nonneg parts)

/-- **Monotone in the fine tolerance.**  Relaxing the fine tolerance from `E` to `E' ≥ E`
    preserves AFKS-fine-regularity: the fine-irregular set only shrinks, so the count still
    fits the unchanged coarse budget. -/
theorem afksFineRegular_mono_fine (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E E' : ℚ} {parts : Finset (Finset V)}
    (hfine : IsAFKSFineRegular G ε E parts) (hEE' : E ≤ E') :
    IsAFKSFineRegular G ε E' parts := by
  obtain ⟨hequit, hcount⟩ := hfine
  refine ⟨hequit, ?_⟩
  calc (((parts.product parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G E' pq.1 pq.2)).card : ℚ)
      ≤ (((parts.product parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G E pq.1 pq.2)).card : ℚ) := by
        exact_mod_cast irregularPairs_card_antitone G hEE' parts
    _ ≤ ε * ((parts.card : ℚ) * ((parts.card : ℚ) - 1)) := hcount

/-- **Monotone in the coarse tolerance.**  Enlarging the coarse tolerance from `ε` to
    `ε' ≥ ε` preserves AFKS-fine-regularity: the fine-irregular count is unchanged (same
    `E`), while the budget `ε·k(k−1)` only grows. -/
theorem afksFineRegular_mono_coarse (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' E : ℚ} {parts : Finset (Finset V)}
    (hfine : IsAFKSFineRegular G ε E parts) (hεε' : ε ≤ ε') :
    IsAFKSFineRegular G ε' E parts := by
  obtain ⟨hequit, hcount⟩ := hfine
  refine ⟨hequit, le_trans hcount ?_⟩
  exact mul_le_mul_of_nonneg_right hεε' (card_mul_pred_nonneg parts)

/-- **Capstone (factored monotonicity).**  `E`-regular ⟹ `ε`-regular for `E ≤ ε`,
    routed through the AFKS hybrid: `IsRegularPartition G E → IsAFKSFineRegular G ε E →
    IsRegularPartition G ε`.  This re-proves `isRegularPartition_mono` while exhibiting the
    AFKS-fine-regular partition as the natural intermediate object of that monotonicity. -/
theorem isRegularPartition_of_isRegularPartition_fine (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε E : ℚ} {parts : Finset (Finset V)}
    (hE : IsRegularPartition G E parts) (hEε : E ≤ ε) :
    IsRegularPartition G ε parts :=
  isRegularPartition_of_afksFineRegular G
    (afksFineRegular_of_isRegularPartition G hE hEε) hEε

end Szemeredi.RegularityOQ04ToleranceBridge
