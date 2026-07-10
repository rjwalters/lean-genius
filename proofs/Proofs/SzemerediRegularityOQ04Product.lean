/-
  Szemerédi Regularity Lemma — OQ-04: the m×k product-refinement energy increment.

  The companion file `SzemerediRegularityOQ04Energy` supplies the 2×2 simultaneous
  refinement increment (`pairEnergy_prod_refinement_gain`): refining a pair `(A, B)`
  into a disjoint `{A₁,A₂}×{B₁,B₂}` grid raises the normalized pair energy by at
  least `(|A₁||B₁|/n²)·d²` whenever the corner sub-cell deviates from `d(A,B)` by
  `≥ d`.  That result is the 2×2 instance of the abstract atom gain
  `weighted_second_moment_atom_gain`, which already handles an *arbitrary* finite
  index.  This file discharges the standing next step recorded in the problem's
  knowledge base: lift the 2×2 grid to a genuine **m×k product refinement** driven
  by two arbitrary disjoint families `{Aᵢ}_{i∈I}` and `{Bⱼ}_{j∈J}`.

  The crux is the **general law of total density**

    `|A||B|·d(A,B) = Σ_{i∈I} Σ_{j∈J} |Aᵢ||Bⱼ|·d(Aᵢ,Bⱼ)`,   `A = ⋃Aᵢ, B = ⋃Bⱼ`,

  which certifies that `d(A,B)` is the honest `|Aᵢ||Bⱼ|`-weighted centroid of the
  refined density distribution.  We obtain it by iterating the two one-sided 2-way
  laws (`edgeDensity_union_mul`, `edgeDensity_union_mul_right`) over each family via
  `Finset.induction`.  Feeding the mean identity plus the total-weight identity
  `Σ_{i,j} |Aᵢ||Bⱼ| = |A||B|` into `weighted_second_moment_atom_gain` over the
  product index `I ×ˢ J` yields, for any single deviating witness cell `(i₀,j₀)`,
  the energy jump

    `pairEnergy G A B + (|A_{i₀}||B_{j₀}|/n²)·d²
       ≤ Σ_{i∈I} Σ_{j∈J} pairEnergy G Aᵢ Bⱼ`.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Energy

namespace Szemeredi.RegularityOQ04Energy

open Szemeredi.Core Szemeredi.Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE GENERAL ONE-SIDED LAW OF TOTAL DENSITY (biUnion)
-- ═══════════════════════════════════════════════════════════════════

/-- **A-side general law of total density.**  For a disjoint family `{Aᵢ}_{i∈I}`
    and a fixed `B`, the edge-count-weighted density of the union splits as a sum
    over the family:
    `|⋃Aᵢ|·|B|·d(⋃Aᵢ,B) = Σ_{i∈I} |Aᵢ|·|B|·d(Aᵢ,B)`.
    Proved by `Finset.induction` on `I`, peeling one part off with the 2-way
    one-sided identity `edgeDensity_union_mul` at each step. -/
theorem edgeDensity_biUnion_mul (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (As : ι → Finset V) (B : Finset V)
    (hdisj : (↑I : Set ι).PairwiseDisjoint As) :
    (↑(I.biUnion As).card : ℚ) * ↑B.card * edgeDensity G (I.biUnion As) B =
      ∑ i ∈ I, (↑(As i).card : ℚ) * ↑B.card * edgeDensity G (As i) B := by
  revert hdisj
  induction I using Finset.induction with
  | empty => intro _; simp
  | @insert a s ha ih =>
    intro hdisj
    have hsub : (↑s : Set ι).PairwiseDisjoint As :=
      hdisj.subset (Finset.coe_subset.mpr (Finset.subset_insert a s))
    have hdisjBig : Disjoint (As a) (s.biUnion As) := by
      rw [Finset.disjoint_biUnion_right]
      intro i hi
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_insert_self a s))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hi)) (fun h => ha (h ▸ hi))
    rw [Finset.biUnion_insert,
        edgeDensity_union_mul G (As a) (s.biUnion As) B hdisjBig,
        Finset.sum_insert ha, ih hsub]

/-- **B-side general law of total density.**  Mirror of `edgeDensity_biUnion_mul`
    on the second coordinate: for a fixed `A` and a disjoint family `{Bⱼ}_{j∈J}`,
    `|A|·|⋃Bⱼ|·d(A,⋃Bⱼ) = Σ_{j∈J} |A|·|Bⱼ|·d(A,Bⱼ)`. -/
theorem edgeDensity_mul_biUnion (G : SimpleGraph V) [DecidableRel G.Adj]
    {κ : Type*} [DecidableEq κ] (A : Finset V) (J : Finset κ) (Bs : κ → Finset V)
    (hdisj : (↑J : Set κ).PairwiseDisjoint Bs) :
    (↑A.card : ℚ) * ↑(J.biUnion Bs).card * edgeDensity G A (J.biUnion Bs) =
      ∑ j ∈ J, (↑A.card : ℚ) * ↑(Bs j).card * edgeDensity G A (Bs j) := by
  revert hdisj
  induction J using Finset.induction with
  | empty => intro _; simp
  | @insert b t hb ih =>
    intro hdisj
    have hsub : (↑t : Set κ).PairwiseDisjoint Bs :=
      hdisj.subset (Finset.coe_subset.mpr (Finset.subset_insert b t))
    have hdisjBig : Disjoint (Bs b) (t.biUnion Bs) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj (Finset.mem_coe.mpr (Finset.mem_insert_self b t))
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hj)) (fun h => hb (h ▸ hj))
    rw [Finset.biUnion_insert,
        edgeDensity_union_mul_right G A (Bs b) (t.biUnion Bs) hdisjBig,
        Finset.sum_insert hb, ih hsub]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE PRODUCT LAW OF TOTAL DENSITY AND TOTAL WEIGHT
-- ═══════════════════════════════════════════════════════════════════

/-- **The general product law of total density.**  When a pair is refined
    simultaneously into two arbitrary disjoint families `{Aᵢ}_{i∈I}`, `{Bⱼ}_{j∈J}`,
    the whole edge-count-weighted density is the double sum of the sub-cell ones:

      `|⋃Aᵢ|·|⋃Bⱼ|·d(⋃Aᵢ,⋃Bⱼ) = Σ_{i∈I} Σ_{j∈J} |Aᵢ||Bⱼ|·d(Aᵢ,Bⱼ)`.

    Equivalently, `d(A,B)` is the `|Aᵢ||Bⱼ|`-weighted mean of the `m·k` sub-densities:
    the mean identity that `weighted_second_moment_atom_gain` consumes.  Proved by
    the A-side biUnion law followed by the B-side one inside each term. -/
theorem edgeDensity_prod_family_split (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs) :
    (↑(I.biUnion As).card : ℚ) * ↑(J.biUnion Bs).card *
        edgeDensity G (I.biUnion As) (J.biUnion Bs) =
      ∑ i ∈ I, ∑ j ∈ J,
        (↑(As i).card : ℚ) * ↑(Bs j).card * edgeDensity G (As i) (Bs j) := by
  rw [edgeDensity_biUnion_mul G I As (J.biUnion Bs) hA]
  exact Finset.sum_congr rfl (fun i _ => edgeDensity_mul_biUnion G (As i) J Bs hB)

/-- **Total refined weight.**  The `|Aᵢ||Bⱼ|` weights of an `m×k` product
    refinement sum to `|A||B|`, since the family cardinalities add over each
    disjoint union (`Finset.card_biUnion`) and the double sum factors as a product
    of the two marginal sums (`Finset.sum_mul_sum`). -/
theorem prod_family_total_weight
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs) :
    (∑ i ∈ I, ∑ j ∈ J, (↑(As i).card : ℚ) * ↑(Bs j).card) =
      (↑(I.biUnion As).card : ℚ) * ↑(J.biUnion Bs).card := by
  rw [Finset.card_biUnion
        (fun x hx y hy hxy => hA (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy),
      Finset.card_biUnion
        (fun x hx y hy hxy => hB (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr hy) hxy)]
  push_cast
  rw [Finset.sum_mul_sum]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE m×k PRODUCT-REFINEMENT ENERGY INCREMENT
-- ═══════════════════════════════════════════════════════════════════

/-- **The m×k product-refinement energy increment.**  Refining a pair `(A, B)`
    simultaneously into two arbitrary disjoint families `{Aᵢ}_{i∈I}`, `{Bⱼ}_{j∈J}`
    (with `A = ⋃Aᵢ`, `B = ⋃Bⱼ`) raises the normalized pair energy by at least
    `(|A_{i₀}||B_{j₀}|/n²)·d²` whenever a single witness sub-cell `(i₀,j₀)` has
    density deviating from the whole density `d(A,B)` by at least `d`:

      `pairEnergy G A B + (|A_{i₀}||B_{j₀}|/n²)·d²
         ≤ Σ_{i∈I} Σ_{j∈J} pairEnergy G Aᵢ Bⱼ`.

    This is the full-generality form of `pairEnergy_prod_refinement_gain` (the `2×2`
    case, `I = J = {·,·}`).  It is exactly `weighted_second_moment_atom_gain` over
    the product index `I ×ˢ J`, with weights `|Aᵢ||Bⱼ|`, values `d(Aᵢ,Bⱼ)`, mean
    `d(A,B)` (discharged by `edgeDensity_prod_family_split`), total weight `|A||B|`
    (`prod_family_total_weight`), and the witness cell as the deviating atom; the
    raw variance excess is scaled by `1/n²` and the `pairEnergy` terms read off.
    For an `ε`-irregular witness `|A_{i₀}| ≥ ε|A|`, `|B_{j₀}| ≥ ε|B|`,
    `|d(A_{i₀},B_{j₀}) − d(A,B)| > ε`, this gives an energy jump `≥ ε⁴·|A||B|/n²`. -/
theorem pairEnergy_prod_family_refinement_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs)
    (i₀ : ι) (j₀ : κ) (hi₀ : i₀ ∈ I) (hj₀ : j₀ ∈ J)
    (d : ℚ) (hd : 0 ≤ d)
    (hdev : d ≤ |edgeDensity G (As i₀) (Bs j₀) -
                  edgeDensity G (I.biUnion As) (J.biUnion Bs)|) :
    pairEnergy G (I.biUnion As) (J.biUnion Bs) +
        (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * d ^ 2 ≤
      ∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j) := by
  classical
  set w : ι × κ → ℚ := fun p => (↑(As p.1).card : ℚ) * ↑(Bs p.2).card with hwdef
  set x : ι × κ → ℚ := fun p => edgeDensity G (As p.1) (Bs p.2) with hxdef
  set μ : ℚ := edgeDensity G (I.biUnion As) (J.biUnion Bs) with hμdef
  have hmem : (i₀, j₀) ∈ I ×ˢ J := Finset.mem_product.mpr ⟨hi₀, hj₀⟩
  have hwnn : ∀ p ∈ I ×ˢ J, 0 ≤ w p := by
    intro p _; simp only [hwdef]; positivity
  -- Total weight `Σ w = |A||B|`.
  have hWtot : (∑ p ∈ I ×ˢ J, w p) =
      (↑(I.biUnion As).card : ℚ) * ↑(J.biUnion Bs).card := by
    rw [Finset.sum_product]
    simpa only [hwdef] using prod_family_total_weight I J As Bs hA hB
  -- Mean identity `Σ w·x = (Σ w)·d(A,B)` — the general law of total density.
  have hmean : (∑ p ∈ I ×ˢ J, w p * x p) = (∑ p ∈ I ×ˢ J, w p) * μ := by
    rw [hWtot, Finset.sum_product]
    simp only [hwdef, hxdef, hμdef]
    exact (edgeDensity_prod_family_split G I J As Bs hA hB).symm
  -- The witness cell is the deviating atom.
  have hdev' : d ≤ |x (i₀, j₀) - μ| := by
    show d ≤ |edgeDensity G (As i₀) (Bs j₀) - μ|
    exact hdev
  -- Apply the abstract atom gain over the product index.
  have hgain := weighted_second_moment_atom_gain (I ×ˢ J) w x hwnn μ hmean
    (i₀, j₀) hmem (w (i₀, j₀)) d (hwnn _ hmem) hd (le_refl _) hdev'
  -- Scale the raw excess by `1/n² ≥ 0` and identify the `pairEnergy` terms.
  have hn2 : (0 : ℚ) ≤ 1 / (Fintype.card V : ℚ) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hgain hn2
  have hL : pairEnergy G (I.biUnion As) (J.biUnion Bs) +
        (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * d ^ 2
      = 1 / (Fintype.card V : ℚ) ^ 2 *
          ((∑ p ∈ I ×ˢ J, w p) * μ ^ 2 + w (i₀, j₀) * d ^ 2) := by
    rw [hWtot, hμdef]
    simp only [hwdef]
    unfold pairEnergy
    ring
  have hR : (∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j))
      = 1 / (Fintype.card V : ℚ) ^ 2 * (∑ p ∈ I ×ˢ J, w p * x p ^ 2) := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hwdef, hxdef]
    unfold pairEnergy
    ring
  rw [hL, hR]
  exact hscaled

/-- **The ε-irregular product-refinement energy jump (`ε⁴` form).**  Specializing
    `pairEnergy_prod_family_refinement_gain` to a genuinely `ε`-irregular witness
    cell — one that is not too small in either coordinate (`|A_{i₀}| ≥ ε|A|`,
    `|B_{j₀}| ≥ ε|B|`) and whose density deviates by at least `ε`
    (`ε ≤ |d(A_{i₀},B_{j₀}) − d(A,B)|`) — yields the clean uniform energy jump

      `pairEnergy G A B + ε⁴·|A||B|/n² ≤ Σ_{i∈I} Σ_{j∈J} pairEnergy G Aᵢ Bⱼ`.

    This is the concrete `ε⁴` bound recorded (but not previously formalized) in the
    docstring of `pairEnergy_prod_family_refinement_gain`; it is the increment that
    drives the energy-increment argument in the Szemerédi regularity proof: each
    refinement of an irregular pair raises the total energy by a fixed `ε⁴`-sized
    amount, and since energy is bounded above the process must terminate.  The gain
    term now depends only on `ε` and the *original* cell sizes `|A|, |B|`, not on the
    witness sub-cell sizes: we replace `|A_{i₀}||B_{j₀}|·ε²` by the smaller
    `ε²|A||B|·ε² = ε⁴|A||B|` using the irregularity lower bounds. -/
theorem pairEnergy_prod_family_refinement_gain_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (I : Finset ι) (J : Finset κ) (As : ι → Finset V) (Bs : κ → Finset V)
    (hA : (↑I : Set ι).PairwiseDisjoint As) (hB : (↑J : Set κ).PairwiseDisjoint Bs)
    (i₀ : ι) (j₀ : κ) (hi₀ : i₀ ∈ I) (hj₀ : j₀ ∈ J)
    (ε : ℚ) (hε : 0 ≤ ε)
    (hAcard : ε * ↑(I.biUnion As).card ≤ (↑(As i₀).card : ℚ))
    (hBcard : ε * ↑(J.biUnion Bs).card ≤ (↑(Bs j₀).card : ℚ))
    (hdev : ε ≤ |edgeDensity G (As i₀) (Bs j₀) -
                  edgeDensity G (I.biUnion As) (J.biUnion Bs)|) :
    pairEnergy G (I.biUnion As) (J.biUnion Bs) +
        ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card / (Fintype.card V : ℚ) ^ 2 ≤
      ∑ i ∈ I, ∑ j ∈ J, pairEnergy G (As i) (Bs j) := by
  have hgain := pairEnergy_prod_family_refinement_gain G I J As Bs hA hB
    i₀ j₀ hi₀ hj₀ ε hε hdev
  -- Replace the witness-cell gain by the uniform `ε⁴|A||B|` lower bound.
  have hcore : ε * ↑(I.biUnion As).card * (ε * ↑(J.biUnion Bs).card)
      ≤ (↑(As i₀).card : ℚ) * ↑(Bs j₀).card :=
    mul_le_mul hAcard hBcard (mul_nonneg hε (by positivity)) (by positivity)
  have key : ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card
      ≤ (↑(As i₀).card : ℚ) * ↑(Bs j₀).card * ε ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hcore (sq_nonneg ε)]
  have hinv : (0 : ℚ) ≤ 1 / (Fintype.card V : ℚ) ^ 2 := by positivity
  have hstep : ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card / (Fintype.card V : ℚ) ^ 2
      ≤ (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * ε ^ 2 :=
    calc ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card / (Fintype.card V : ℚ) ^ 2
        = (ε ^ 4 * ↑(I.biUnion As).card * ↑(J.biUnion Bs).card)
            * (1 / (Fintype.card V : ℚ) ^ 2) := by ring
      _ ≤ ((↑(As i₀).card : ℚ) * ↑(Bs j₀).card * ε ^ 2)
            * (1 / (Fintype.card V : ℚ) ^ 2) := mul_le_mul_of_nonneg_right key hinv
      _ = (↑(As i₀).card : ℚ) * ↑(Bs j₀).card / (Fintype.card V : ℚ) ^ 2 * ε ^ 2 := by ring
  linarith [hgain, hstep]

end Szemeredi.RegularityOQ04Energy
