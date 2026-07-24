/-
  Szemerédi Regularity OQ04 — S24: energy stability under merging (re-cut loss bound)

  The AFKS two-level pipeline is complete up to RE-EQUITIZATION (S12–S23).  S23
  (`SzemerediRegularityOQ04ChopRefine.lean`) supplied the *refinement* half: chop
  every part into size-`m` pieces, at most one deficient (`< m`) remainder per
  part, with FULL energy retention.  The remaining *merging* half must pool the
  ≤ `|P|` deficient remainders and re-cut their union into size-`m` chunks —
  which is NOT a refinement, so energy can drop.

  This file proves the analytic core of that step: **replacing a subfamily `D`
  of a pairwise-disjoint family `Q` (keeping everything outside `D`) loses at
  most `2·mass(D)/n` of partition energy**, where `mass(D) = Σ_{A∈D} |A|` and
  `n = |V|`.  The mechanism is elementary: every ordered pair of parts
  contributes at most its normalized weight `|A|·|B|/n²` (density ≤ 1), so the
  pairs touching `D` contribute at most `2·mass(D)·mass(Q)/n² ≤ 2·mass(D)/n`,
  and partition energy is monotone under family inclusion.

  Main results:
  * `pairEnergy_nonneg`, `pairEnergy_le_weight` — pointwise bounds `0 ≤ pe ≤ w`.
  * `sum_card_le_card_univ` — a pairwise-disjoint family occupies ≤ `|V|` vertices.
  * `partitionEnergy_subset_le` — energy is monotone under family inclusion.
  * `partitionEnergy_sdiff_ge` — removing `D` loses at most `2·mass(D)/n`.
  * `partitionEnergy_replace_ge` — capstone: any family retaining `Q \ D`
    (e.g. the re-cut) has energy ≥ `E(Q) − 2·mass(D)/n`.
  * `partitionEnergy_replace_ge_of_small` — consumer form for S23's output:
    ≤ `|D|` deficient pieces of size ≤ `m` cost at most `2·|D|·m/n`.

  With these, the outstanding merging obligation reduces to pure combinatorics
  (re-cut the pooled union into size-`m` chunks, S22's chopping engine) plus
  choosing parameters with `2·|P|·m/n` below the retained gain fraction.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Bridge

namespace Szemeredi.RegularityOQ04MergeLoss

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: POINTWISE PAIR-ENERGY BOUNDS
-- ═══════════════════════════════════════════════════════════════════

omit [DecidableEq V] in
/-- Pair energy is nonnegative. -/
theorem pairEnergy_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : 0 ≤ pairEnergy G A B := by
  unfold pairEnergy
  have hw : (0 : ℚ) ≤ (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 := by
    positivity
  exact mul_nonneg hw (sq_nonneg _)

/-- **Weight bound.**  Since edge density lies in `[0,1]`, one ordered pair
contributes at most its normalized weight: `pe(A,B) ≤ |A|·|B|/n²`. -/
theorem pairEnergy_le_weight (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    pairEnergy G A B ≤ (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 := by
  unfold pairEnergy
  have hw : (0 : ℚ) ≤ (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 := by
    positivity
  have hd : (edgeDensity G A B) ^ 2 ≤ 1 := by
    have h0 := edgeDensity_nonneg G A B
    have h1 := edgeDensity_le_one G A B
    nlinarith
  calc (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 * (edgeDensity G A B) ^ 2
      ≤ (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hd hw
    _ = (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 := mul_one _

-- ═══════════════════════════════════════════════════════════════════
-- PART II: MASS AND MONOTONICITY
-- ═══════════════════════════════════════════════════════════════════

/-- A pairwise-disjoint family of vertex sets occupies at most `|V|` vertices. -/
theorem sum_card_le_card_univ {Q : Finset (Finset V)}
    (hdisj : (↑Q : Set (Finset V)).PairwiseDisjoint id) :
    ∑ A ∈ Q, (A.card : ℚ) ≤ (Fintype.card V : ℚ) := by
  have hnat : ∑ A ∈ Q, A.card ≤ Fintype.card V := by
    have hbi : (Q.biUnion id).card = ∑ A ∈ Q, A.card :=
      Finset.card_biUnion fun x hx y hy hxy => hdisj hx hy hxy
    calc ∑ A ∈ Q, A.card = (Q.biUnion id).card := hbi.symm
      _ ≤ Fintype.card V := Finset.card_le_univ _
  exact_mod_cast hnat

/-- Partition energy is monotone under inclusion of families (all ordered-pair
contributions are nonnegative). -/
theorem partitionEnergy_subset_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q₁ Q₂ : Finset (Finset V)} (h : Q₁ ⊆ Q₂) :
    partitionEnergy G Q₁ ≤ partitionEnergy G Q₂ := by
  rw [partitionEnergy_eq_sum_pairEnergy, partitionEnergy_eq_sum_pairEnergy]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.product_subset_product h h) fun pq _ _ => ?_
  exact pairEnergy_nonneg G pq.1 pq.2

-- ═══════════════════════════════════════════════════════════════════
-- PART III: CROSS-BLOCK BOUND AND THE MERGING LOSS
-- ═══════════════════════════════════════════════════════════════════

/-- Division is monotone in the numerator for a nonnegative denominator
(valid at denominator `0`, where both sides vanish). -/
private theorem div_le_div_of_le {a b c : ℚ} (h : a ≤ b) (hc : 0 ≤ c) :
    a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc)

/-- **Cross-block bound.**  The ordered pairs running from a family `S` into a
family `D` contribute at most `mass(S)·mass(D)/n²`. -/
theorem cross_sum_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S D : Finset (Finset V)) :
    ∑ A ∈ S, ∑ B ∈ D, pairEnergy G A B ≤
      (∑ A ∈ S, (A.card : ℚ)) * (∑ B ∈ D, (B.card : ℚ)) /
        (Fintype.card V : ℚ) ^ 2 := by
  have h1 : ∑ A ∈ S, ∑ B ∈ D, pairEnergy G A B ≤
      ∑ A ∈ S, ∑ B ∈ D,
        (A.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 :=
    Finset.sum_le_sum fun A _ =>
      Finset.sum_le_sum fun B _ => pairEnergy_le_weight G A B
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun A _ => by rw [Finset.sum_div]

/-- Purely arithmetic collection step: `n·m/n² + m·n/n² = 2·m/n` in `ℚ`
(both sides vanish at `n = 0`, where division is junk-zero). -/
private theorem collect_halves (n m : ℚ) :
    n * m / n ^ 2 + m * n / n ^ 2 = 2 * m / n := by
  rcases eq_or_ne n 0 with rfl | h0
  · norm_num
  · field_simp
    ring

/-- Block decomposition of the double sum: separating a subfamily `D ⊆ Q`
splits the ordered-pair sum into the surviving block and two cross blocks. -/
private theorem energy_decomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q D : Finset (Finset V)} (hD : D ⊆ Q) :
    partitionEnergy G Q = partitionEnergy G (Q \ D) +
      (∑ A ∈ Q \ D, ∑ B ∈ D, pairEnergy G A B) +
      (∑ A ∈ D, ∑ B ∈ Q, pairEnergy G A B) := by
  have hdouble : ∀ parts : Finset (Finset V), partitionEnergy G parts =
      ∑ A ∈ parts, ∑ B ∈ parts, pairEnergy G A B := fun parts => by
    rw [partitionEnergy_eq_sum_pairEnergy,
      show parts.product parts = parts ×ˢ parts from rfl, Finset.sum_product]
  rw [hdouble Q, hdouble (Q \ D)]
  calc ∑ A ∈ Q, ∑ B ∈ Q, pairEnergy G A B
      = ∑ A ∈ Q \ D, ∑ B ∈ Q, pairEnergy G A B +
          ∑ A ∈ D, ∑ B ∈ Q, pairEnergy G A B := (Finset.sum_sdiff hD).symm
    _ = ∑ A ∈ Q \ D, (∑ B ∈ Q \ D, pairEnergy G A B +
          ∑ B ∈ D, pairEnergy G A B) +
          ∑ A ∈ D, ∑ B ∈ Q, pairEnergy G A B := by
        rw [Finset.sum_congr rfl fun A _ => (Finset.sum_sdiff hD).symm]
    _ = (∑ A ∈ Q \ D, ∑ B ∈ Q \ D, pairEnergy G A B) +
          (∑ A ∈ Q \ D, ∑ B ∈ D, pairEnergy G A B) +
          ∑ A ∈ D, ∑ B ∈ Q, pairEnergy G A B := by
        rw [Finset.sum_add_distrib]

/-- **Merging loss bound.**  Removing a subfamily `D ⊆ Q` from a
pairwise-disjoint family `Q` loses at most `2·mass(D)/n` of partition energy:
the removed ordered pairs all touch `D`, and each is dominated by its weight. -/
theorem partitionEnergy_sdiff_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q D : Finset (Finset V)} (hD : D ⊆ Q)
    (hdisj : (↑Q : Set (Finset V)).PairwiseDisjoint id) :
    partitionEnergy G Q ≤ partitionEnergy G (Q \ D) +
      2 * (∑ A ∈ D, (A.card : ℚ)) / (Fintype.card V : ℚ) := by
  have hmD0 : (0 : ℚ) ≤ ∑ A ∈ D, (A.card : ℚ) :=
    Finset.sum_nonneg fun A _ => by positivity
  have hmQ : ∑ A ∈ Q, (A.card : ℚ) ≤ (Fintype.card V : ℚ) :=
    sum_card_le_card_univ hdisj
  have hmS : ∑ A ∈ Q \ D, (A.card : ℚ) ≤ (Fintype.card V : ℚ) :=
    sum_card_le_card_univ (hdisj.subset
      (Finset.coe_subset.mpr fun x hx => (Finset.mem_sdiff.mp hx).1))
  have hT1 : ∑ A ∈ Q \ D, ∑ B ∈ D, pairEnergy G A B ≤
      (Fintype.card V : ℚ) * (∑ A ∈ D, (A.card : ℚ)) /
        (Fintype.card V : ℚ) ^ 2 :=
    (cross_sum_le G (Q \ D) D).trans
      (div_le_div_of_le (mul_le_mul_of_nonneg_right hmS hmD0) (by positivity))
  have hT2 : ∑ A ∈ D, ∑ B ∈ Q, pairEnergy G A B ≤
      (∑ A ∈ D, (A.card : ℚ)) * (Fintype.card V : ℚ) /
        (Fintype.card V : ℚ) ^ 2 :=
    (cross_sum_le G D Q).trans
      (div_le_div_of_le (mul_le_mul_of_nonneg_left hmQ hmD0) (by positivity))
  calc partitionEnergy G Q
      = partitionEnergy G (Q \ D) +
          (∑ A ∈ Q \ D, ∑ B ∈ D, pairEnergy G A B) +
          (∑ A ∈ D, ∑ B ∈ Q, pairEnergy G A B) := energy_decomposition G hD
    _ ≤ partitionEnergy G (Q \ D) +
          ((Fintype.card V : ℚ) * (∑ A ∈ D, (A.card : ℚ)) /
            (Fintype.card V : ℚ) ^ 2) +
          ((∑ A ∈ D, (A.card : ℚ)) * (Fintype.card V : ℚ) /
            (Fintype.card V : ℚ) ^ 2) :=
        add_le_add (add_le_add le_rfl hT1) hT2
    _ = partitionEnergy G (Q \ D) +
          2 * (∑ A ∈ D, (A.card : ℚ)) / (Fintype.card V : ℚ) := by
        rw [add_assoc, collect_halves]

/-- **Local re-partition stability (capstone).**  If a family `Q'` retains
every part of `Q` outside `D` — e.g. `Q'` re-cuts the pooled union of the
deficient remainders `D` into fresh chunks — its energy drops below `Q`'s by at
most `2·mass(D)/n`.  This is the analytic half of the re-equitization merging
step; the combinatorial half is the size-`m` re-cut itself. -/
theorem partitionEnergy_replace_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    {Q D Q' : Finset (Finset V)} (hD : D ⊆ Q)
    (hdisj : (↑Q : Set (Finset V)).PairwiseDisjoint id)
    (hkeep : Q \ D ⊆ Q') :
    partitionEnergy G Q - 2 * (∑ A ∈ D, (A.card : ℚ)) / (Fintype.card V : ℚ) ≤
      partitionEnergy G Q' := by
  have h1 := partitionEnergy_sdiff_ge G hD hdisj
  have h2 := partitionEnergy_subset_le G hkeep
  linarith

/-- **Consumer form for S23's output.**  When the replaced subfamily consists
of at most-size-`m` pieces (the deficient remainders of the chop refinement),
the loss is at most `2·|D|·m/n`.  Choosing `m` small against `n` makes the
loss negligible against the retained `eps⁴m²/n²`-scale energy gain. -/
theorem partitionEnergy_replace_ge_of_small (G : SimpleGraph V)
    [DecidableRel G.Adj] {Q D Q' : Finset (Finset V)} {m : ℕ} (hD : D ⊆ Q)
    (hdisj : (↑Q : Set (Finset V)).PairwiseDisjoint id)
    (hkeep : Q \ D ⊆ Q') (hsmall : ∀ A ∈ D, A.card ≤ m) :
    partitionEnergy G Q - 2 * (D.card * m : ℚ) / (Fintype.card V : ℚ) ≤
      partitionEnergy G Q' := by
  have hmass : ∑ A ∈ D, (A.card : ℚ) ≤ (D.card * m : ℚ) := by
    calc ∑ A ∈ D, (A.card : ℚ) ≤ ∑ _A ∈ D, (m : ℚ) :=
          Finset.sum_le_sum fun A hA => by exact_mod_cast hsmall A hA
      _ = (D.card * m : ℚ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h1 := partitionEnergy_replace_ge G hD hdisj hkeep
  have h2 : 2 * (∑ A ∈ D, (A.card : ℚ)) / (Fintype.card V : ℚ) ≤
      2 * (D.card * m : ℚ) / (Fintype.card V : ℚ) :=
    div_le_div_of_le (by linarith) (Nat.cast_nonneg _)
  linarith

end Szemeredi.RegularityOQ04MergeLoss
