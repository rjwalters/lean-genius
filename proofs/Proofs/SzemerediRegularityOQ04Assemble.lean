/-
  Szemerédi Regularity OQ04 — S27b-ii: invariant restoration and the deficit form
  of the maintained step

  This file composes the whole S20–S27b-i pipeline into the two statements the
  Chain oracle (`exists_afksTwoLevel_of_maintained_oracle`) actually consumes:

  * `exists_invariant_restore` — the modular capstone.  ANY covering, pairwise
    disjoint family refining the coarse partition `Vparts` (blocks pairwise
    disjoint with per-block mass `m² ≤ |A|`) can be rebuilt into a family
    satisfying the FULL Chain loop invariant — covering, pairwise disjoint,
    refining `Vparts`, globally ±1-equitable, mass floor `m` — at explicit
    ambient energy cost `2·|q₁|·m/n + 2·|Vparts|·m²/n`.  Empty pieces are
    stripped for free (`partitionEnergy_filter_card_ne_zero`), the per-block
    ground floors come from `fiber_ground_eq_block`, and the rebuild is
    S27b-i's `exists_equitable_recut_blocks` over `T = Vparts`.

  * `exists_maintained_next_deficit` — the DEFICIT form of the maintained step:
    an invariant-satisfying partition that is not AFKS-fine-regular has a
    successor satisfying the full invariant whose energy exceeds the parent's
    by the bare-split gain `E⁴m²/n²` MINUS the restoration cost above.

  ## Honesty note — why this does NOT close the oracle (S28 blocker)

  The Chain oracle needs the deficit to be positive: restoration cost strictly
  below the retained gain.  It never is.  The gain `E⁴m²/n²` comes from ONE
  witnessed deviating pair (S18/S19: the sharp single-witness floor), while any
  re-equitization that moves even a single piece of mass `≈ m` costs on the
  order of `2m/n`, and `2m/n > E⁴m²/n²  ⟺  2n > E⁴m`, which holds for every
  admissible parameter choice (`E ≤ 1`, `m ≤ n`).  Even the single absorption
  term `2m²/n` alone exceeds the gain (`2m²/n > E⁴m²/n² ⟺ 2n > E⁴`).  So no
  parameter bookkeeping can close the maintained oracle from the single-witness
  step: the per-step gain must first be AMPLIFIED to a constant scale — the
  true AFKS mechanism, where ¬regularity yields a mass-weighted ε-fraction of
  irregular pairs and the summed energy increment is `≥ ε⁵`-scale, independent
  of `m/n`.  That amplification (a mass-weighted defect extraction from
  `¬ IsAFKSFineRegular`, S28) is a materially new mechanism, recorded as the
  blocked route's reopen criterion.  These two theorems are exactly the
  interface it will consume: an S28 gain `γ` feeds the same
  `exists_invariant_restore`, and the oracle closes when `γ` exceeds the cost.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000); Komlós–Simonovits (1996).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Iterate
import Proofs.SzemerediRegularityOQ04Chain

namespace Szemeredi.RegularityOQ04Assemble

open Szemeredi.Core Szemeredi.Regularity
open Szemeredi.RegularityOQ04Energy Szemeredi.RegularityOQ04Bridge
open Szemeredi.RegularityOQ04TwoLevel Szemeredi.RegularityOQ04ToleranceBridge
open Szemeredi.RegularityOQ04Iterate Szemeredi.RegularityOQ04Chain

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- **Fiber grounds are whole blocks.**  If `q` covers `V` and refines the
pairwise-disjoint block family `Vparts`, then the ground set of the fiber of a
block `A` (the pieces of `q` contained in `A`) is exactly `A`: containment one
way is by definition of the fiber, and a vertex `v ∈ A` lies in some piece `P`,
which sits inside some block `A'`; blocks are disjoint and `v ∈ A ∩ A'`, so
`A' = A` and `P` is in the fiber. -/
theorem fiber_ground_eq_block (Vparts q : Finset (Finset V)) {A : Finset V}
    (hA : A ∈ Vparts)
    (hVdisj : (↑Vparts : Set (Finset V)).PairwiseDisjoint id)
    (hcover : ∀ v : V, ∃ P ∈ q, v ∈ P)
    (href : IsRefinement q Vparts) :
    (q.filter (· ⊆ A)).biUnion id = A := by
  apply Finset.Subset.antisymm
  · exact Finset.biUnion_subset.mpr (fun c hc => (Finset.mem_filter.mp hc).2)
  · intro v hv
    obtain ⟨P, hP, hvP⟩ := hcover v
    obtain ⟨A', hA', hPA'⟩ := href P hP
    have hAA' : A = A' := by
      by_contra hne
      have hd := hVdisj (Finset.mem_coe.mpr hA) (Finset.mem_coe.mpr hA') hne
      have hd' : Disjoint A A' := by simpa [Function.onFun] using hd
      exact absurd (hPA' hvP) (Finset.disjoint_left.mp hd' hv)
    refine Finset.mem_biUnion.mpr ⟨P, Finset.mem_filter.mpr ⟨hP, ?_⟩, hvP⟩
    rw [hAA']
    exact hPA'

/-- **Invariant restoration (S27b-ii modular capstone).**  Any covering,
pairwise-disjoint family `q₁` refining the pairwise-disjoint coarse partition
`Vparts` (each block of ground mass at least `m²`) can be rebuilt into a family
satisfying the FULL Chain loop invariant — covering, pairwise disjoint,
refining `Vparts`, globally ±1-equitable (all sizes in `{m, m+1}`), mass floor
`m` — at ambient energy cost at most `2·|q₁|·m/n + 2·|Vparts|·m²/n`.

Pipeline: strip empty pieces (free, `partitionEnergy_filter_card_ne_zero`);
per-block ground floors from `fiber_ground_eq_block`; rebuild all blocks with
S27b-i's `exists_equitable_recut_blocks` (`T = Vparts`); global equitability
follows because every rebuilt piece sits inside a block (the locality clause)
and is therefore sized `{m, m+1}`.

This is the exact interface a future amplified-gain step (S28) composes with:
successor + restoration = maintained oracle, provided the gain beats the cost. -/
theorem exists_invariant_restore (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (Vparts q₁ : Finset (Finset V))
    (hVdisj : (↑Vparts : Set (Finset V)).PairwiseDisjoint id)
    (hVfloor : ∀ A ∈ Vparts, m * m ≤ A.card)
    (hcover : ∀ v : V, ∃ P ∈ q₁, v ∈ P)
    (hdisj : ∀ P Q : Finset V, P ∈ q₁ → Q ∈ q₁ → P ≠ Q → Disjoint P Q)
    (href : IsRefinement q₁ Vparts) :
    ∃ q' : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
      (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
      IsRefinement q' Vparts ∧
      (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → (P.card : ℤ) - Q.card ≤ 1) ∧
      (∀ P ∈ q', (m : ℚ) ≤ P.card) ∧
      partitionEnergy G q₁
          - (2 * ((q₁.card : ℚ) * (m : ℚ)) / (Fintype.card V : ℚ)
             + 2 * ((Vparts.card : ℚ) * ((m : ℚ) * (m : ℚ))) / (Fintype.card V : ℚ)) ≤
        partitionEnergy G q' := by
  classical
  set Q₀ : Finset (Finset V) := q₁.filter (fun P => P.card ≠ 0) with hQ₀def
  have hQ₀sub : Q₀ ⊆ q₁ := Finset.filter_subset _ _
  have hQ₀cover : ∀ v : V, ∃ P ∈ Q₀, v ∈ P := by
    intro v
    obtain ⟨P, hP, hvP⟩ := hcover v
    exact ⟨P, Finset.mem_filter.mpr ⟨hP, Finset.card_ne_zero_of_mem hvP⟩, hvP⟩
  have hQ₀ne : ∀ c ∈ Q₀, c.Nonempty := fun c hc =>
    Finset.card_pos.mp (Nat.pos_of_ne_zero (Finset.mem_filter.mp hc).2)
  have hQ₀disj : (↑Q₀ : Set (Finset V)).PairwiseDisjoint id := by
    intro a ha b hb hab
    simpa [Function.onFun] using
      hdisj a b (hQ₀sub (Finset.mem_coe.mp ha)) (hQ₀sub (Finset.mem_coe.mp hb)) hab
  have hQ₀ref : IsRefinement Q₀ Vparts := fun c hc => href c (hQ₀sub hc)
  have hfloor : ∀ A ∈ Vparts, m * m ≤ ((Q₀.filter (· ⊆ A)).biUnion id).card := by
    intro A hA
    rw [fiber_ground_eq_block Vparts Q₀ hA hVdisj hQ₀cover hQ₀ref]
    exact hVfloor A hA
  obtain ⟨Q₁, hground, hQ₁disj, hQ₁ne, hQ₁sized, _hfib, hpe, hloc⟩ :=
    exists_equitable_recut_blocks G m hm Vparts Q₀ hVdisj hQ₀disj hQ₀ne hfloor
  have hQ₁ref : IsRefinement Q₁ Vparts := by
    intro c hc
    rcases hloc c hc with h0 | h
    · exact hQ₀ref c h0
    · exact h
  have hsize : ∀ c ∈ Q₁, c.card = m ∨ c.card = m + 1 := by
    intro c hc
    obtain ⟨A, hA, hcA⟩ := hQ₁ref c hc
    exact hQ₁sized A hA c hc hcA
  refine ⟨Q₁, ?_, ?_, hQ₁ref, ?_, ?_, ?_⟩
  · -- covering: the ground set is preserved by the rebuild
    intro v
    obtain ⟨P, hP, hvP⟩ := hQ₀cover v
    have hv : v ∈ Q₁.biUnion id := by
      rw [hground]
      exact Finset.mem_biUnion.mpr ⟨P, hP, hvP⟩
    obtain ⟨P', hP', hvP'⟩ := Finset.mem_biUnion.mp hv
    exact ⟨P', hP', hvP'⟩
  · -- pairwise disjointness, pointwise form
    intro P Q hP hQ hne
    have := hQ₁disj (Finset.mem_coe.mpr hP) (Finset.mem_coe.mpr hQ) hne
    simpa [Function.onFun] using this
  · -- global ±1 equitability: all sizes lie in {m, m+1}
    intro P Q hP hQ
    rcases hsize P hP with h1 | h1 <;> rcases hsize Q hQ with h2 | h2 <;>
      rw [h1, h2] <;> omega
  · -- mass floor (the `card = m` branch auto-closes under `rw`)
    intro P hP
    rcases hsize P hP with h | h <;> rw [h]
    exact_mod_cast Nat.le_succ m
  · -- energy accounting
    have hpe0 : partitionEnergy G Q₀ = partitionEnergy G q₁ := by
      rw [hQ₀def]
      exact partitionEnergy_filter_card_ne_zero G q₁
    have hcost := recut_blocks_cost_le (V := V) m Vparts Q₀ hVdisj hQ₀ne
    have hb1 : 2 * ((Q₀.card : ℚ) * (m : ℚ)) / (Fintype.card V : ℚ)
        ≤ 2 * ((q₁.card : ℚ) * (m : ℚ)) / (Fintype.card V : ℚ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (by positivity))
      have h := Nat.mul_le_mul_right m (Finset.card_le_card hQ₀sub)
      have h' : ((Q₀.card * m : ℕ) : ℚ) ≤ ((q₁.card * m : ℕ) : ℚ) := by
        exact_mod_cast h
      push_cast at h'
      linarith
    linarith [hpe, hcost, hb1, hpe0]

/-- **The maintained step, deficit form (S27b-ii).**  An invariant-satisfying
partition `q` (covering, disjoint, refining `Vparts`, ±1-equitable, mass floor
`m`) that is not AFKS-fine-regular admits a successor satisfying the FULL
invariant whose energy exceeds `partitionEnergy G q` by the bare-split gain
`E⁴m²/n²` minus the restoration cost `2·|q₁|·m/n + 2·|Vparts|·m²/n` (with `q₁`
the intermediate bare-split successor, exposed by the existential).

This is everything the Chain oracle needs EXCEPT positivity of the deficit —
which fails for every admissible parameter choice (see the module docstring):
the single-witness gain is dominated by even one absorption's cost.  Closing
the oracle requires amplifying the gain to the summed mass-weighted defect of
all irregular pairs (`≥ ε⁵`-scale, the true AFKS mechanism) — the S28 target,
which composes with `exists_invariant_restore` verbatim. -/
theorem exists_maintained_next_deficit
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε E : ℚ) (m : ℕ)
    (hε : 0 ≤ ε) (hE : 0 < E) (hE1 : E ≤ 1) (hm : 1 ≤ m)
    (Vparts q : Finset (Finset V))
    (hVdisj : (↑Vparts : Set (Finset V)).PairwiseDisjoint id)
    (hVfloor : ∀ A ∈ Vparts, m * m ≤ A.card)
    (hcover : ∀ v : V, ∃ P ∈ q, v ∈ P)
    (hdisj : ∀ P Q : Finset V, P ∈ q → Q ∈ q → P ≠ Q → Disjoint P Q)
    (href : IsRefinement q Vparts)
    (hequit : ∀ P Q : Finset V, P ∈ q → Q ∈ q → (P.card : ℤ) - Q.card ≤ 1)
    (hmass : ∀ P ∈ q, (m : ℚ) ≤ P.card)
    (hnot : ¬ IsAFKSFineRegular G ε E q) :
    ∃ q' q₁ : Finset (Finset V),
      (∀ v : V, ∃ P ∈ q', v ∈ P) ∧
      (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → P ≠ Q → Disjoint P Q) ∧
      IsRefinement q' Vparts ∧
      (∀ P Q : Finset V, P ∈ q' → Q ∈ q' → (P.card : ℤ) - Q.card ≤ 1) ∧
      (∀ P ∈ q', (m : ℚ) ≤ P.card) ∧
      partitionEnergy G q + E ^ 4 * (m : ℚ) ^ 2 / (Fintype.card V : ℚ) ^ 2
          - (2 * ((q₁.card : ℚ) * (m : ℚ)) / (Fintype.card V : ℚ)
             + 2 * ((Vparts.card : ℚ) * ((m : ℚ) * (m : ℚ))) / (Fintype.card V : ℚ)) ≤
        partitionEnergy G q' := by
  obtain ⟨q₁, hc₁, hd₁, hr₁, hgain⟩ :=
    exists_energy_next_of_not_afksFineRegular G ε E (m : ℚ) hε hE hE1
      (by exact_mod_cast (by omega : 0 < m)) q hcover hdisj hequit hmass hnot
  obtain ⟨q', hc', hd', hr', he', hm', hrestore⟩ :=
    exists_invariant_restore G m hm Vparts q₁ hVdisj hVfloor hc₁ hd₁
      (hr₁ Vparts href)
  exact ⟨q', q₁, hc', hd', hr', he', hm', by linarith [hgain, hrestore]⟩

end Szemeredi.RegularityOQ04Assemble
