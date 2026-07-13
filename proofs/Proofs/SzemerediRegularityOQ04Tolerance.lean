/-
  Szemerédi Regularity Lemma — OQ-04: tolerance monotonicity of regularity.

  The strong (Alon–Fischer–Krivelevich–Szegedy) regularity lemma produces a
  *two-level* partition: a coarse `ε`-regular partition `V₁..V_k`, and a
  refinement `W₁..W_ℓ` all but `ε·C(ℓ,2)` of whose pairs are `E(k)`-regular,
  where the fine tolerance `E : ℕ → (0,1]` is chosen *after* seeing `k` and is
  taken *stronger* than the coarse tolerance, `E(k) ≤ ε`.  The reason this yields
  a genuinely stronger conclusion — and the reason the fine level automatically
  satisfies the coarse requirement — is the elementary but foundational fact that
  **`ε`-regularity is monotone in the tolerance `ε`**: a pair that is regular at a
  *strong* tolerance is regular at every *weaker* one.

  The whole OQ-04 tower so far discharges the *energy-increment* side (item 1 of
  the standing plan): the variance atom, the m×k product-refinement gains, the
  finiteness/termination engine.  None of it touches the *tolerance* dimension —
  yet the two-level AFKS conclusion statement (item 2) is stated entirely in terms
  of it.  This file supplies that missing dimension, at both the pair level and the
  whole-partition level, plus the exceptional-pair count-transfer that the AFKS
  conclusion consumes directly:

  * `isEpsilonRegular_mono` — pair regularity is monotone in the tolerance:
    `IsEpsilonRegular G ε A B → ε ≤ ε' → IsEpsilonRegular G ε' A B`.
  * `isEpsilonRegular_of_stronger_tolerance` — the AFKS-framed corollary: a pair
    regular at the fine tolerance `E(k) ≤ ε` is automatically `ε`-regular.
  * `irregularPairs_card_antitone` — the set of `ε`-irregular ordered pairs shrinks
    as `ε` grows, hence its cardinality is antitone in `ε`.
  * `afks_exceptional_count_transfer` — if all but `t` fine pairs are `E`-regular
    and `E ≤ ε`, then all but `t` fine pairs are `ε`-regular.
  * `isRegularPartition_mono` — the whole `IsRegularPartition` predicate is monotone
    in the tolerance: a partition regular at a strong tolerance is regular at every
    weaker one (equitability is tolerance-free; the exceptional count only shrinks
    and its budget `ε·k(k-1)` only grows).

  Everything is elementary order arithmetic over the `Szemeredi.Core` definitions —
  no energy machinery — hence cheap to machine-check in isolation.
-/
import Mathlib
import Proofs.SzemerediCore

namespace Szemeredi.RegularityOQ04Tolerance

open Classical Szemeredi.Core

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PAIR-LEVEL TOLERANCE MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- **`ε`-regularity is monotone in the tolerance.**  If `(A,B)` is regular at
    tolerance `ε` and `ε ≤ ε'`, then it is regular at the weaker tolerance `ε'`.

    The two obligations both relax in the right direction: the size floors
    `|A'| ≥ ε'|A|`, `|B'| ≥ ε'|B|` of the `ε'`-test are *harder* to meet than the
    `ε`-ones (`ε·|A| ≤ ε'·|A|`), so every `ε'`-admissible witness `(A',B')` is
    already `ε`-admissible; and the density deviation it must beat is *larger*
    (`ε ≤ ε'`), so the `ε`-bound `|d(A',B') − d(A,B)| ≤ ε` implies the `ε'`-bound. -/
theorem isEpsilonRegular_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' : ℚ} {A B : Finset V}
    (hreg : IsEpsilonRegular G ε A B) (hεε' : ε ≤ ε') :
    IsEpsilonRegular G ε' A B := by
  intro A' B' hA'sub hB'sub hA'card hB'card
  -- Every `ε'`-admissible witness is `ε`-admissible: `ε·|A| ≤ ε'·|A| ≤ |A'|`.
  have hA'card' : (A'.card : ℚ) ≥ ε * A.card :=
    le_trans (mul_le_mul_of_nonneg_right hεε' (by positivity)) hA'card
  have hB'card' : (B'.card : ℚ) ≥ ε * B.card :=
    le_trans (mul_le_mul_of_nonneg_right hεε' (by positivity)) hB'card
  -- The `ε`-deviation bound implies the (weaker) `ε'`-deviation bound.
  exact le_trans (hreg A' B' hA'sub hB'sub hA'card' hB'card') hεε'

/-- **AFKS bridge (pair level).**  A pair that is regular at the fine tolerance
    `E(k)`, chosen `≤ ε`, is automatically `ε`-regular.  This is exactly why the
    strong lemma's fine partition satisfies the coarse regularity requirement for
    free — the dependent tolerance is chosen *stronger*, so its guarantees dominate. -/
theorem isEpsilonRegular_of_stronger_tolerance (G : SimpleGraph V) [DecidableRel G.Adj]
    {Ek ε : ℚ} {A B : Finset V}
    (hreg : IsEpsilonRegular G Ek A B) (hle : Ek ≤ ε) :
    IsEpsilonRegular G ε A B :=
  isEpsilonRegular_mono G hreg hle

-- ═══════════════════════════════════════════════════════════════════
-- EXCEPTIONAL-PAIR COUNTING (the AFKS conclusion's currency)
-- ═══════════════════════════════════════════════════════════════════

/-- The set of `ε`-*irregular* ordered pairs of a partition is antitone in `ε`:
    if `ε ≤ ε'` then every `ε'`-irregular pair is already `ε`-irregular (a pair
    that fails at the *weaker* tolerance certainly fails at the stronger one), so
    the `ε'`-irregular set is contained in the `ε`-irregular set. -/
theorem irregularPairs_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' : ℚ} (hεε' : ε ≤ ε') (parts : Finset (Finset V)) :
    ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε' pq.1 pq.2)) ⊆
      ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε pq.1 pq.2)) := by
  intro pq hpq
  rw [Finset.mem_filter] at hpq ⊢
  refine ⟨hpq.1, hpq.2.1, ?_⟩
  -- `¬ε'-regular` gives `¬ε-regular`: if it *were* `ε`-regular, monotonicity would
  -- upgrade it to `ε'`-regular, contradicting `hpq`.
  exact fun hεreg => hpq.2.2 (isEpsilonRegular_mono G hεreg hεε')

/-- Cardinality form of `irregularPairs_subset`: the number of `ε`-irregular
    ordered pairs is antitone in `ε`. -/
theorem irregularPairs_card_antitone (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' : ℚ} (hεε' : ε ≤ ε') (parts : Finset (Finset V)) :
    ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε' pq.1 pq.2)).card ≤
      ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε pq.1 pq.2)).card :=
  Finset.card_le_card (irregularPairs_subset G hεε' parts)

/-- **AFKS exceptional-count transfer.**  If all but `t` ordered pairs of a
    partition are regular at the fine tolerance `E` (i.e. at most `t` are
    `E`-irregular), and `E ≤ ε`, then at most `t` pairs are `ε`-irregular.

    This is the mechanism by which the AFKS fine partition, built to be `E(k)`-regular
    on all-but-`ε·C(ℓ,2)` pairs, simultaneously meets the coarse `ε`-irregularity
    budget — the exceptional set only shrinks as the tolerance loosens. -/
theorem afks_exceptional_count_transfer (G : SimpleGraph V) [DecidableRel G.Adj]
    {E ε : ℚ} (hle : E ≤ ε) (parts : Finset (Finset V)) {t : ℚ}
    (hcount : ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G E pq.1 pq.2)).card ≤ t) :
    ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε pq.1 pq.2)).card ≤ t :=
  le_trans (by exact_mod_cast irregularPairs_card_antitone G hle parts) hcount

-- ═══════════════════════════════════════════════════════════════════
-- WHOLE-PARTITION TOLERANCE MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- `k·(k − 1) ≥ 0` for a natural `k` cast into `ℚ` — the pair-budget factor is
    nonnegative, so scaling it by a larger tolerance can only enlarge the budget. -/
private theorem card_mul_pred_nonneg (parts : Finset (Finset V)) :
    (0 : ℚ) ≤ (parts.card : ℚ) * ((parts.card : ℚ) - 1) := by
  rcases Nat.eq_zero_or_pos parts.card with hk | hk
  · simp [hk]
  · have h1 : (1 : ℚ) ≤ (parts.card : ℚ) := by exact_mod_cast hk
    exact mul_nonneg (by positivity) (by linarith)

/-- **`IsRegularPartition` is monotone in the tolerance.**  A partition that is
    `ε`-regular remains regular at every weaker tolerance `ε' ≥ ε`.

    Both clauses relax in the right direction: equitability
    (`|Pᵢ| − |Pⱼ| ≤ 1`) is tolerance-free, and the exceptional-pair count only
    *shrinks* while its budget `ε·k(k−1)` only *grows*:
    `#(ε'-irregular) ≤ #(ε-irregular) ≤ ε·k(k−1) ≤ ε'·k(k−1)`.

    Together with `isEpsilonRegular_of_stronger_tolerance` this is the exact sense
    in which the AFKS fine partition (regular at the *strong* dependent tolerance
    `E(k) ≤ ε`) automatically fulfils the coarse `ε`-regularity demand. -/
theorem isRegularPartition_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' : ℚ} {parts : Finset (Finset V)}
    (hreg : IsRegularPartition G ε parts) (hεε' : ε ≤ ε') :
    IsRegularPartition G ε' parts := by
  obtain ⟨hequit, hcount⟩ := hreg
  refine ⟨hequit, ?_⟩
  -- Chain: #irr(ε') ≤ #irr(ε) ≤ ε·k(k−1) ≤ ε'·k(k−1).
  have hcard : ((parts.product parts).filter (fun pq =>
      pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε' pq.1 pq.2)).card ≤
    ((parts.product parts).filter (fun pq =>
      pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε pq.1 pq.2)).card :=
    irregularPairs_card_antitone G hεε' parts
  have hbudget : ε * ((parts.card : ℚ) * ((parts.card : ℚ) - 1)) ≤
      ε' * ((parts.card : ℚ) * ((parts.card : ℚ) - 1)) :=
    mul_le_mul_of_nonneg_right hεε' (card_mul_pred_nonneg parts)
  calc (((parts.product parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε' pq.1 pq.2)).card : ℚ)
      ≤ (((parts.product parts).filter (fun pq =>
          pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G ε pq.1 pq.2)).card : ℚ) := by
        exact_mod_cast hcard
    _ ≤ ε * ((parts.card : ℚ) * ((parts.card : ℚ) - 1)) := hcount
    _ ≤ ε' * ((parts.card : ℚ) * ((parts.card : ℚ) - 1)) := hbudget

end Szemeredi.RegularityOQ04Tolerance
