/-
  Szemerédi Regularity Lemma — OQ-04: discharging the *freshness* side-conditions
  of the sharp 2×2 product refinement gain from a concrete partition model.

  The whole-partition sharp-gain engine of the strong (AFKS) regularity lemma —
  `partitionEnergy_prod_refinement_gain` and its `ε⁴` floor
  `partitionEnergy_prod_gain_eps4` in `SzemerediRegularityOQ04Assembly` — needs, in
  addition to the density-deviation and size bounds, six *freshness* hypotheses:
  the coarse parts `A, B` and the four fine cells `A₁, A₂, B₁, B₂` obtained by
  splitting `A = A₁ ∪ A₂`, `B = B₁ ∪ B₂` must all be pairwise distinct as `Finset`s
  and none of them may already appear among the remaining parts `R`.  Those `∉`
  facts are what let `Finset.sum_insert` peel the six blocks off the double sum;
  they are threaded as raw hypotheses throughout the OQ-04 tower.

  Discharging them "from a nonempty-equipartition model" is recorded in the
  progress notes as *the standing open blocker*.  This file closes the
  set-theoretic half of that blocker: in any genuine partition — pairwise-disjoint
  nonempty blocks — two nonempty disjoint pieces of a block are automatically
  distinct from each other, from the pieces of a *different* block, and from every
  remaining block.  We package that as `freshness_of_partition`, whose conclusion
  is *exactly* the six-fold conjunction demanded by the gain theorems, so a caller
  holding an equipartition model can discharge all of them with a single
  `obtain`.

  Everything here is elementary `Finset` combinatorics over `Mathlib` alone (no
  dependence on the energy tower), hence cheap to machine-check in isolation.  The
  only piece the *analytic* half of the blocker still owes is the existence of such
  a split with the size floors `|A₁| ≥ ε|A|`, `|B₁| ≥ ε|B|` — the realizability of
  the witness, not its freshness.
-/
import Mathlib

namespace Szemeredi.RegularityOQ04Fresh

variable {V : Type*} [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- ELEMENTARY DISTINCTNESS FROM DISJOINTNESS
-- ═══════════════════════════════════════════════════════════════════

omit [DecidableEq V] in
/-- A nonempty finset is never disjoint from itself, hence a nonempty `s`
    disjoint from `t` cannot equal `t`. -/
theorem ne_of_disjoint_nonempty {s t : Finset V}
    (h : Disjoint s t) (hs : s.Nonempty) : s ≠ t := by
  rintro rfl
  obtain ⟨x, hx⟩ := hs
  exact Finset.disjoint_left.mp h hx hx

omit [DecidableEq V] in
/-- Two finsets that lie inside disjoint "hosts" are distinct as soon as the first
    is nonempty: if `s ⊆ u`, `t ⊆ v`, `Disjoint u v` and `s.Nonempty`, then
    `s ≠ t`.  (If `s = t` then a witness `x ∈ s` would live in both `u` and `v`.) -/
theorem ne_of_subset_disjoint {s t u v : Finset V}
    (hsu : s ⊆ u) (htv : t ⊆ v) (huv : Disjoint u v) (hs : s.Nonempty) : s ≠ t := by
  rintro rfl
  obtain ⟨x, hx⟩ := hs
  exact Finset.disjoint_left.mp huv (hsu hx) (htv hx)

omit [DecidableEq V] in
/-- A nonempty finset disjoint from every member of a family `R` is not itself a
    member of `R`.  (A member equal to `s` would be disjoint from `s`, impossible
    for nonempty `s`.) -/
theorem not_mem_of_forall_disjoint {R : Finset (Finset V)} {s : Finset V}
    (h : ∀ Q ∈ R, Disjoint Q s) (hs : s.Nonempty) : s ∉ R := by
  intro hmem
  obtain ⟨x, hx⟩ := hs
  exact Finset.disjoint_left.mp (h s hmem) hx hx

omit [DecidableEq V] in
/-- Membership variant of `ne_of_subset_disjoint`: a nonempty `s ⊆ u` is not a
    member of a family `R` all of whose blocks are disjoint from `u`. -/
theorem not_mem_of_subset_forall_disjoint {R : Finset (Finset V)} {s u : Finset V}
    (hsu : s ⊆ u) (h : ∀ Q ∈ R, Disjoint Q u) (hs : s.Nonempty) : s ∉ R := by
  refine not_mem_of_forall_disjoint (fun Q hQ => ?_) hs
  exact (h Q hQ).mono_right hsu

-- ═══════════════════════════════════════════════════════════════════
-- THE FRESHNESS DISCHARGE
-- ═══════════════════════════════════════════════════════════════════

/-- **Freshness of a 2×2 split inside a partition.**  Model the coarse pieces as
    two distinct blocks `A`, `B` of a partition — captured by `Disjoint A B` — and
    the split of each into two nonempty disjoint cells `A = A₁ ∪ A₂`,
    `B = B₁ ∪ B₂`.  Let `R` collect the remaining blocks, each disjoint from both
    `A` and `B`.  Then the six freshness side-conditions of
    `partitionEnergy_prod_refinement_gain` / `partitionEnergy_prod_gain_eps4` all
    hold simultaneously:

    * `A ∉ insert B R`  (coarse pieces distinct and unused),
    * `B ∉ R`,
    * `A₁ ∉ insert A₂ (insert B₁ (insert B₂ R))`,
    * `A₂ ∉ insert B₁ (insert B₂ R)`,
    * `B₁ ∉ insert B₂ R`,
    * `B₂ ∉ R`.

    This is the set-theoretic half of the "equipartition realizability" blocker:
    freshness is *free* in any genuine partition; only the size floors
    `|A₁| ≥ ε|A|` etc. must still be witnessed analytically. -/
theorem freshness_of_partition
    {A B A₁ A₂ B₁ B₂ : Finset V} {R : Finset (Finset V)}
    (hAunion : A₁ ∪ A₂ = A) (hBunion : B₁ ∪ B₂ = B)
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty)
    (hdisjA : Disjoint A₁ A₂) (hdisjB : Disjoint B₁ B₂)
    (hAB : Disjoint A B)
    (hRA : ∀ Q ∈ R, Disjoint Q A) (hRB : ∀ Q ∈ R, Disjoint Q B) :
    A ∉ insert B R ∧ B ∉ R ∧
      A₁ ∉ insert A₂ (insert B₁ (insert B₂ R)) ∧
      A₂ ∉ insert B₁ (insert B₂ R) ∧
      B₁ ∉ insert B₂ R ∧ B₂ ∉ R := by
  -- The four cells sit inside their coarse block.
  have hA₁A : A₁ ⊆ A := hAunion ▸ Finset.subset_union_left
  have hA₂A : A₂ ⊆ A := hAunion ▸ Finset.subset_union_right
  have hB₁B : B₁ ⊆ B := hBunion ▸ Finset.subset_union_left
  have hB₂B : B₂ ⊆ B := hBunion ▸ Finset.subset_union_right
  -- Each coarse block is nonempty (it contains a cell).
  have hAne : A.Nonempty := hA₁.mono hA₁A
  have hBne : B.Nonempty := hB₁.mono hB₁B
  -- Disjointness of the fine cells across the two coarse blocks.
  have hA₁B₁ : Disjoint A₁ B₁ := hAB.mono hA₁A hB₁B
  have hA₁B₂ : Disjoint A₁ B₂ := hAB.mono hA₁A hB₂B
  have hA₂B₁ : Disjoint A₂ B₁ := hAB.mono hA₂A hB₁B
  have hA₂B₂ : Disjoint A₂ B₂ := hAB.mono hA₂A hB₂B
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- A ∉ insert B R : A ≠ B and A ∉ R
    rw [Finset.mem_insert, not_or]
    refine ⟨ne_of_disjoint_nonempty hAB hAne, ?_⟩
    exact not_mem_of_forall_disjoint hRA hAne
  · -- B ∉ R
    exact not_mem_of_forall_disjoint hRB hBne
  · -- A₁ ∉ {A₂, B₁, B₂} ∪ R
    simp only [Finset.mem_insert, not_or]
    refine ⟨ne_of_disjoint_nonempty hdisjA hA₁,
      ne_of_disjoint_nonempty hA₁B₁ hA₁,
      ne_of_disjoint_nonempty hA₁B₂ hA₁, ?_⟩
    exact not_mem_of_subset_forall_disjoint hA₁A hRA hA₁
  · -- A₂ ∉ {B₁, B₂} ∪ R
    simp only [Finset.mem_insert, not_or]
    refine ⟨ne_of_disjoint_nonempty hA₂B₁ hA₂,
      ne_of_disjoint_nonempty hA₂B₂ hA₂, ?_⟩
    exact not_mem_of_subset_forall_disjoint hA₂A hRA hA₂
  · -- B₁ ∉ insert B₂ R
    rw [Finset.mem_insert, not_or]
    refine ⟨ne_of_disjoint_nonempty hdisjB hB₁, ?_⟩
    exact not_mem_of_subset_forall_disjoint hB₁B hRB hB₁
  · -- B₂ ∉ R
    exact not_mem_of_subset_forall_disjoint hB₂B hRB hB₂

end Szemeredi.RegularityOQ04Fresh
