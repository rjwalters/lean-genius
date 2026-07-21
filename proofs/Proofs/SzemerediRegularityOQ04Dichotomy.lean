/-
  Szemerédi Regularity Lemma — OQ-04: the *analytic realizability* half of the
  regular-or-refine dichotomy.

  `SzemerediRegularityOQ04Outer` (item 3, structural half) closes the outer AFKS
  loop *modulo* an explicit hypothesis — the **regular-or-refine dichotomy**:

      ¬ IsAFKSFineRegular G ε (E k) (parts n)  →  IsWitnessedSharpStep …

  i.e. "a fine partition that is not AFKS-fine-regular admits a witnessed sharp
  `2×2` gain-refinement step".  `state.md` (S10) records this as *the remaining
  crux*: "a fine partition failing the `E(k)`-regular budget contains an
  `E(k)`-irregular pair whose sharp `2×2` refinement realizes the no-loss energy
  gain … assembling them into the exact `IsWitnessedSharpStep`-shaped,
  whole-partition dichotomy (freshness + equipartition split realizability) is the
  substantive open piece."

  This file discharges the **analytic realizability core** of that crux — the part
  that is genuine mathematics rather than combinatorial bookkeeping:

  * `exists_irregular_pair_of_not_afksFineRegular` — from a partition that is
    equitable but **not** AFKS-fine-regular (`0 ≤ ε`), extract an actual
    `E`-irregular ordered pair `(A, B)` of parts.  The AFKS exceptional budget
    `ε·k(k−1)` is nonnegative, so failing `IsAFKSFineRegular` on an equitable
    partition forces the `E`-irregular set to be *nonempty*, not merely
    over-budget.  (This is the AFKS-budget analogue of the classical
    `exists_irregular_pair`, whose filter tolerance and budget tolerance must
    coincide; here they differ — filter at the fine `E`, budget at the coarse `ε`.)

  * `exists_sharp_split_of_not_afksFineRegular` — compose that with
    `exists_irregular_witness` to produce the **sharp `2×2` split data**: two
    distinct parts `A, B ∈ parts` and a split `A = A₁ ∪ A₂`, `B = B₁ ∪ B₂` (each a
    disjoint two-piece split) whose `A₁/B₁` corner keeps the `E`-mass floors
    `E·|A| ≤ |A₁|`, `E·|B| ≤ |B₁|` and whose corner density deviates from the
    parent density by `≥ E`:  `E ≤ |d(A₁,B₁) − d(A,B)|`.  These are exactly the
    quantitative clauses of `IsWitnessedSharpStep` (mass floors, split shape,
    `E`-gap) — everything except the chain-and-freshness packaging
    (`parts n = insert A (insert B R)`, `parts (n+1) = …`, the disjoint-fresh
    side-conditions), which constrains an *externally given* refinement chain and
    is combinatorial bookkeeping, not analysis.

  Honesty: this does **not** prove the full dichotomy hypothesis of
  `exists_afksTwoLevel_of_dichotomy`.  That hypothesis quantifies over a *given*
  refinement chain `parts : ℕ → …` and asserts the step `parts n → parts (n+1)`
  *is* the sharp split; realizing it requires either constructing the chain
  recursively or threading the freshness/cover side-conditions.  What is closed
  here is the mathematical content the hypothesis abstracts: the split with its
  mass floors and `E`-gap genuinely *exists* whenever fine-regularity fails.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularity
import Proofs.SzemerediRegularityOQ04ToleranceBridge

namespace Szemeredi.RegularityOQ04Dichotomy

open Classical Szemeredi.Core Szemeredi.RegularityOQ04ToleranceBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: EXTRACT AN E-IRREGULAR PAIR FROM A NON-AFKS-FINE-REGULAR PARTITION
-- ═══════════════════════════════════════════════════════════════════

/-- **Extract the irregular pair.**  If `parts` is equitable but **not**
    AFKS-fine-regular at coarse tolerance `ε ≥ 0` and fine tolerance `E`, then some
    ordered pair `(P, Q)` of distinct parts is `E`-irregular.

    The AFKS exceptional budget `ε·(k(k−1))` is nonnegative, so a partition whose
    `E`-irregular count *exceeds* it cannot have an empty `E`-irregular set: failing
    `IsAFKSFineRegular` while equitable means the fine-irregular filter is nonempty.
    Unlike the classical `exists_irregular_pair` (filter and budget share one
    tolerance), here the filter runs at the fine `E` and the budget at the coarse
    `ε` — this is the AFKS-hybrid version. -/
theorem exists_irregular_pair_of_not_afksFineRegular (G : SimpleGraph V)
    [DecidableRel G.Adj] (ε E : ℚ) (hε : 0 ≤ ε) (parts : Finset (Finset V))
    (hequit : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → (P.card : ℤ) - Q.card ≤ 1)
    (hnot : ¬ IsAFKSFineRegular G ε E parts) :
    ∃ P Q : Finset V, P ∈ parts ∧ Q ∈ parts ∧ P ≠ Q ∧
      ¬ IsEpsilonRegular G E P Q := by
  -- The ordered-pair budget factor `k(k−1)` is nonnegative.
  have hknn : (0 : ℚ) ≤ (parts.card : ℚ) * ((parts.card : ℚ) - 1) := by
    rcases Nat.eq_zero_or_pos parts.card with hk | hk
    · simp [hk]
    · have h1 : (1 : ℚ) ≤ (parts.card : ℚ) := by exact_mod_cast hk
      exact mul_nonneg (by positivity) (by linarith)
  -- Hence the exceptional set is nonempty: were it empty, equitability + the
  -- nonnegative budget would give `IsAFKSFineRegular`, contradicting `hnot`.
  have hcard_pos : 0 < ((parts.product parts).filter (fun pq =>
      pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G E pq.1 pq.2)).card := by
    by_contra hle
    push_neg at hle
    apply hnot
    unfold IsAFKSFineRegular
    refine ⟨hequit, ?_⟩
    have hz : ((parts.product parts).filter (fun pq =>
        pq.1 ≠ pq.2 ∧ ¬IsEpsilonRegular G E pq.1 pq.2)).card = 0 := Nat.le_zero.mp hle
    rw [hz]
    simpa using mul_nonneg hε hknn
  obtain ⟨⟨P, Q⟩, hmem⟩ := Finset.card_pos.mp hcard_pos
  have hf := Finset.mem_filter.mp hmem
  have hp := Finset.mem_product.mp hf.1
  exact ⟨P, Q, hp.1, hp.2, hf.2.1, hf.2.2⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART II: REALIZE THE SHARP 2×2 SPLIT
-- ═══════════════════════════════════════════════════════════════════

/-- **The sharp `2×2` split exists.**  From an equitable partition that is not
    AFKS-fine-regular (`0 ≤ ε`), there exist two distinct parts `A, B` and a
    disjoint two-piece split of each — `A = A₁ ∪ A₂`, `B = B₁ ∪ B₂` — whose
    `A₁/B₁` corner keeps the `E`-mass floors and realizes an `E`-density gap:

      `E·|A| ≤ |A₁|`,  `E·|B| ≤ |B₁|`,  `E ≤ |d(A₁,B₁) − d(A,B)|`.

    These are precisely the *quantitative* clauses of `IsWitnessedSharpStep`
    (`Outer.lean`): the split shape (`A₁ ∪ A₂ = A`, disjointness), the mass floors
    `eps·|A| ≤ |A₁|`, and the `eps`-gap `eps ≤ |d(A₁,B₁) − d(A,B)|`.  Only the
    chain-and-freshness packaging (`parts n = insert A (insert B R)`,
    `parts (n+1) = …`, the fresh-block side-conditions) is left — that constrains
    an externally supplied refinement chain and is combinatorial, not analytic.

    Construction: take an `E`-irregular pair `(A, B)`
    (`exists_irregular_pair_of_not_afksFineRegular`), pull the deviating subsets
    `A' ⊆ A`, `B' ⊆ B` out of it (`exists_irregular_witness`), and split
    `A₁ := A'`, `A₂ := A ∖ A'`, `B₁ := B'`, `B₂ := B ∖ B'`. -/
theorem exists_sharp_split_of_not_afksFineRegular (G : SimpleGraph V)
    [DecidableRel G.Adj] (ε E : ℚ) (hε : 0 ≤ ε) (parts : Finset (Finset V))
    (hequit : ∀ P Q : Finset V, P ∈ parts → Q ∈ parts → (P.card : ℤ) - Q.card ≤ 1)
    (hnot : ¬ IsAFKSFineRegular G ε E parts) :
    ∃ A B A₁ A₂ B₁ B₂ : Finset V,
      A ∈ parts ∧ B ∈ parts ∧ A ≠ B ∧
      A₁ ∪ A₂ = A ∧ B₁ ∪ B₂ = B ∧ Disjoint A₁ A₂ ∧ Disjoint B₁ B₂ ∧
      E * A.card ≤ (A₁.card : ℚ) ∧ E * B.card ≤ (B₁.card : ℚ) ∧
      E ≤ |edgeDensity G A₁ B₁ - edgeDensity G A B| := by
  obtain ⟨A, B, hA, hB, hAB, hirr⟩ :=
    exists_irregular_pair_of_not_afksFineRegular G ε E hε parts hequit hnot
  obtain ⟨A', B', hA'sub, hB'sub, hcA', hcB', hd⟩ :=
    Szemeredi.Regularity.exists_irregular_witness G E A B hirr
  refine ⟨A, B, A', A \ A', B', B \ B', hA, hB, hAB, ?_, ?_, ?_, ?_, hcA', hcB',
    le_of_lt hd⟩
  · -- A' ∪ (A ∖ A') = A
    rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hA'sub
  · -- B' ∪ (B ∖ B') = B
    rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hB'sub
  · -- Disjoint A' (A ∖ A')
    exact Finset.disjoint_left.mpr fun a ha ha' => (Finset.mem_sdiff.mp ha').2 ha
  · -- Disjoint B' (B ∖ B')
    exact Finset.disjoint_left.mpr fun b hb hb' => (Finset.mem_sdiff.mp hb').2 hb

end Szemeredi.RegularityOQ04Dichotomy
